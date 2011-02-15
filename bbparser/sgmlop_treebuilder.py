"""A simple SGML tree builder with namespaces support, based on Fredrik Lundh's
SgmlopXMLTreeBuilder and his sgmlop library.

This tree builder requires cElementTree and sgmlop.

This version copyright (c) 2007 by Ludovico Magnocavallo.  All rights reserved.

The original SgmlopXMLTreeBuilder can be found at http://effbot.org/downloads/
and is copyright (c) 1999-2004 by Fredrik Lundh.  All rights reserved.

"""

__copyright__ = "Copyright (c) 1999-2004 by Fredrik Lundh. Copyright (c) 2007 by Ludovico Magnocavallo"
__version__ = "$LastChangedRevision: 1302 $"[22:-2]
__date__ = "$LastChangedDate: 2007-02-18 13:24:10 +0100 (Sun, 18 Feb 2007) $"[18:-2]

import atexit
import htmlentitydefs

try:
    from xml.etree import cElementTree as et
except ImportError:
    from xml.etree import ElementTree as et
from xml.etree import ElementTree as et    

import sgmlop


DEBUG = False


def log(*args):
    if DEBUG:
        for a in args:
            print a,
        print


entitydefs = dict()
for k, v in htmlentitydefs.entitydefs.items():
    entitydefs[k] = v.decode('iso-8859-15')
entitydefs['apos'] = u"'"
entitydefs['nbsp'] = u' '

short_tags = "area base basefont br col frame hr img input isindex link meta param".split()

# shamelessly copied from libxml2's HTMLparser.c
html_startclose = dict(
    form=(
        'form', 'p', 'hr', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'dl', 'ul', 'ol',
        'menu', 'dir', 'address', 'pre', 'listing', 'xmp', 'head',
    ),
    head=('p',),
    title=('p',),
    body=('head', 'style', 'link', 'title', 'p',),
    frameset=('head', 'style', 'link', 'title', 'p',),
    li=(
        'p', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'dl', 'address', 'pre',
        'listing', 'xmp', 'head', 'li',
    ),
    hr=('p', 'head',),
    h1=('p', 'head',),
    h2=('p', 'head',),
    h3=('p', 'head',),
    h4=('p', 'head',),
    h5=('p', 'head',),
    h6=('p', 'head',),
    dir=('p', 'head',),
    address=('p', 'head', 'ul',),
    pre=('p', 'head', 'ul',),
    listing=('p', 'head',),
    xmp=('p', 'head',),
    blockquote=('p', 'head',),
    dl=('p', 'dt', 'menu', 'dir', 'address', 'pre', 'listing','xmp', 'head',),
    dt=('p', 'menu', 'dir', 'address', 'pre', 'listing', 'xmp','head', 'dd',),
    dd=('p', 'menu', 'dir', 'address', 'pre', 'listing', 'xmp','head', 'dt',),
    ul=('p', 'head', 'ol', 'menu', 'dir', 'address', 'pre','listing', 'xmp',),
    ol=('p', 'head', 'ul',),
    menu=('p', 'head', 'ul',),
    p=('p', 'head', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6',),
    div=('p', 'head',),
    noscript=('p', 'head',),
    center=('font', 'b', 'i', 'p', 'head',),
    a=('a',),
    caption=('p',),
    colgroup=('caption', 'colgroup', 'col', 'p',),
    col=('caption', 'col', 'p',),
    table=('p', 'head', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'pre','listing', 'xmp', 'a',),
    th=('th', 'td', 'p', 'span', 'font', 'a', 'b', 'i', 'u',),
    td=('th', 'td', 'p', 'span', 'font', 'a', 'b', 'i', 'u',),      
    tr=('th', 'td', 'tr', 'caption', 'col', 'colgroup', 'p',),
    thead=('caption', 'col', 'colgroup',),
    tfoot=('th', 'td', 'tr', 'caption', 'col', 'colgroup', 'thead','tbody', 'p',),
    tbody=(
        'th', 'td', 'tr', 'caption', 'col', 'colgroup', 'thead','tfoot',
        'tbody', 'p',
    ),
    optgroup=('option',),
    option=('option',),
    fieldset=(
        'legend', 'p', 'head', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'pre',
        'listing', 'xmp', 'a',
    ),
)

class SgmlopTreeBuilder(object):
    """ElementTree builder for SGML source data, based on the SGMLOP parser.
    
    You need a new builder for each new document you need to parse. This is to
    make SgmlopTreeBuilder behave like the standard ElementTree TreeBuilder.
    Modifying it so that it can be reused is trivial.
    
    
    >>> p = SgmlopTreeBuilder()
    >>> p.feed('<div>Torna anche quest&#39;anno l&#39;appuntamento con il Premio Via Po, riconoscimento letterario cittadino organizzato dall&#39;Associazione Culturale per Torino in collaborazione con l&rsquo;Associazione Amici dell&rsquo;Universit&agrave; degli Studi di Torino e il contributo di Regione Piemonte e Fondazione Ferrero. Il Premio,&nbsp;intitolato quest&#39;anno...</div>')
    >>> tree = p.close()
    >>>
    """
    
    entitydefs = entitydefs
    short_tags = dict(zip(short_tags, [None]*len(short_tags)))
    
    def __init__(
        self, check_prolog=True, handle_special=False, decode=True,
        builder_class=None, parser_class=None, skip_ns=tuple()):
        if check_prolog:
            self.handle_proc = self._handle_proc
            self._prolog_found = False
        if handle_special:
            self.handle_special = self._handle_special
        if not decode:
            self.handle_charref = self._handle_charref
            self.handle_entityref = self._handle_entityref
        self.check_prolog = check_prolog
        self.warnings = list()
        self._ns = list()
        self._protect_recursion = list()
        self._autoclosed = list()
        self._names = dict(xml='http://www.w3.org/XML/1998/namespace')
        self._builder_class = builder_class or et.TreeBuilder
        self._builder = self._builder_class()
        parser = parser_class or sgmlop.XMLParser
        self._skip_ns = skip_ns
        self._parser = parser()
        self._parser.register(self)
        self._registered = True
        self.closed = False
        atexit.register(self.unregister)
    
    def feed(self, data):
        """Feeds data to the parser."""
        if not self._registered:
            raise ValueError("This tree builder has already been used.")
        if isinstance(data, unicode):
            self._parser.feed(data.encode('utf-8'))
        else:
            self._parser.feed(data)
        
    def unregister(self):
        if self._registered:
            self._parser.register(None)
            self._registered = False
            self._parser = None
            self._builder = None
    
    def close(self):
        """Finishes feeding data to the parser."""
        self._parser.close()
        for tag, ns in reversed(self._ns):
            if ns:
                self._ns_close(ns)
            self._builder.end(tag)
        tree = self._builder.close()
        self.unregister()
        return tree
    
    def _handle_proc(self, target, content):
        if self._prolog_found:
            return
        if target == 'xml':
            self._prolog_found = True
            # discard everything up to this point
            self._ns = list()
            self._builder = self._builder_class()
            
    
    def _handle_special(self, content):
        # we feed the whole document in one go, so we should not receive chunks
        if content[:7] == 'DOCTYPE':
            return
        if content[:6] == 'ENTITY':
            return
        if content[:6] == 'ATTLIST':
            return
        self._builder.data("<!%s" % content)

    def resolve_entityref(self, ref):
        if self.closed:
            log("*** closed ***")
            return
        log("RESOLVE ENTITY", ref)
        e = self.entitydefs.get(ref, "&%s" % ref)
        log("RESOLVED ENTITY TO", e, "type", type(e))
        if isinstance(e, unicode):
            return e.encode('utf8')
        return e
        
    def handle_charref(self, ref):
        if self.closed:
            log("*** closed ***")
            return
        log("CHARREF", ref)
        if not ref:
            self._builder.data("&#")
            return
        if ref[0] == 'x':
            base = 16
            ref = "0%s" % ref
        else:
            base = 10
        try:
            ref = int(ref, base)
        #    if ref in (38, 60, 62):
        #        raise ValueError
        except (ValueError, OverflowError):
            self._builder.data("&#%s;" % ref if not isinstance(ref, str) else ref.decode('utf-8', 'ignore'))
        else:
            try:
                self._builder.data(unichr(ref))
            except ValueError:
                self._builder.data("&#%s;" % ref)
            
    def handle_entityref(self, ref):
        #if ref in ('amp', 'gt','lt'):
        #   self._builder.data('&%s;' % ref)
        #   return
        if self.closed:
            log("*** closed ***")
            return
        log("REF", ref)
        entity = self.entitydefs.get(ref, "&%s;" % ref)
        if entity[:2] == '&#':
            entity = self.handle_charref(entity[2:-1])
        else:
            if isinstance(entity, str):
                entity = entity.decode('utf-8', 'ignore')
            self._builder.data(entity)
    
    def _handle_charref(self, ref):
        if self.closed:
            log("*** closed ***")
            return
        log("_CHARREF", ref)
        self._builder.data("&#%s;" % ref)
        
    def _handle_entityref(self, ref):
        log("_REF", ref)
        self._builder.data("&%s;" % ref)
        
    def handle_comment(self, text):
        return
        self._builder.data("<!--%s-->" % text)
        
    def finish_starttag(self, tag, attrib):
        if self.closed:
            log("*** closed ***")
            return
        log("-- open", tag, attrib)
        # look for namespaces in attributes
        ns = list()
        ns_attrib = []
        skip_ns = self._skip_ns
        # lowercase tags and attrs like the original feedparser
        tag = tag.lower()
        attrib = dict(attrib)
        for _k, v in attrib.items():
            k = _k.lower()
            if k != _k:
                del(attrib[_k])
                attrib[k] = v
            if k.startswith('xmlns:'):
                prefix = k[6:]
                ns.append((prefix, v, self._names.get(prefix)))
                del(attrib[k])
            elif k == 'xmlns':
                prefix = None
                ns.append((prefix, v, self._names.get(prefix)))
                del(attrib[k])
            elif k.find(':') > 1:
                ns_attrib.append(k)
            elif v:
                try:
                    attrib[k] = v.decode('utf-8', 'ignore')
                except UnicodeEncodeError:
                    continue
            else:
                attrib[k] = ''
        for prefix, name, oldvalue in ns:
            self._names[prefix] = name
        for k in ns_attrib:
            prefix, name = k.split(':', 1)
            attr_ns = self._names.get(prefix)
            if attr_ns:
                if attr_ns in skip_ns:
                    attrib[name] = attrib[k]
                else:
                    attrib["{%s}%s" % (attr_ns, name)] = attrib[k]
                del(attrib[k])
        # now check the tag namespace
        pos = tag.find(':')
        if pos > 0:
            prefix = tag[:pos]
            tag = tag[pos+1:]
        else:
            prefix = None
        tag_ns = self._names.get(prefix)
        if tag_ns:
            if tag_ns in skip_ns:
                tag = tag
            else:
                tag = "{%s}%s" % (tag_ns, tag)
        # check to see if this tag autocloses previous tags
        autoclose = html_startclose.get(tag)
        if autoclose and self._ns:
            _tag, _ns = self._ns[-1]
            if _tag in autoclose:
                log("--- got", tag, "autoclosing ", _tag)
                self._autoclosed.append(_tag)
                if _ns:
                    self._ns_close(_ns)
                self._builder.end(_tag)
                self._ns = self._ns[:-1]
            #_i = None
            #for i, t in enumerate(self._ns):
            #    _tag, _ns = t
            #    if _tag in autoclose:
            #        _i = i
            #        break
            #if _i is not None:
            #    log("--- got", tag, "autoclosing ", _tag)
            #    log("--- [self._ns]", self._ns)
            #    for _tag, _ns in reversed(self._ns[_i:]):
            #        log("---- autoclosing", _tag, _ns)
            #        self._autoclosed.append(_tag)
            #        if _ns:
            #            self._ns_close(_ns)
            #        self._builder.end(_tag)
            #    self._ns = self._ns[:_i]
            #    log("--- [self._ns]", self._ns)
        if tag not in ('br', 'hr', 'img'):
            if len(self._ns) > 300:
                self._protect_recursion.append((tag, ns))
                return
            else:
                self._ns.append((tag, ns))
        log("--- [self._ns]", self._ns)
        # now build the element
        #log('<--- open', tag, len(self._ns), self._ns)
        try:
            self._builder.start(tag, attrib)
        except SyntaxError, e:
            self.warnings.append("SgmlopTreeBuilder error on tag '%s': %s" % (tag, e))
        except UnicodeDecodeError, e:
            print tag, attrib, e
            raise
        if tag in ('br', 'hr', 'img'):
            # shortcircuit
            self._builder.end(tag)

    def finish_endtag(self, tag):
        """
        >>> doc = "<root><a><b><c>umph</a></c></root><other></other>"
        >>> t = SgmlopTreeBuilder()
        >>> t.feed(doc)
        >>> tree = t.close()
        >>> et.tostring(tree)
        '<root><a><b><c>umph</c></b></a></root>'
        >>> 
        """
        if self._protect_recursion:
            self._protect_recursion.pop()
            return
        if self.closed:
            log("*** closed ***")
            return
        log("-- close", tag)
        # check the tag namespace
        tag = tag.lower()
        pos = tag.find(':')
        if pos > 0:
            prefix = tag[:pos]
            tag = tag[pos+1:]
        else:
            prefix = None
        tag_ns = self._names.get(prefix)
        if tag_ns:
            if tag_ns in self._skip_ns:
                tag = tag
            else:
                tag = "{%s}%s" % (tag_ns, tag)
        #elif prefix:
        #    log("----> name not found!!!!!", prefix, self._names)
        log("---> closing", tag, len(self._ns), self._ns)
        # decrease namespace counters, if any
        ns = None
        try:
            open_tag, ns = self._ns.pop()
        except IndexError:
            #log("ouch", tag)
            pass
        else:
            if open_tag != tag:
                if tag in ('br', 'hr', 'img'):
                    log("--- short tag", tag)
                    self._ns.append((open_tag, ns))
                    return
                log('--- stray close', tag, 'expected', open_tag)
                log("---- autoclosed list", self._autoclosed)
                # stray tag close
                if tag in self._autoclosed:
                    log("--- found in autoclosed")
                    i = max(i for i, t in enumerate(self._autoclosed) if t == tag)
                    del(self._autoclosed[i])
                    self._ns.append((open_tag, ns))
                    log("---", self._ns)
                    return
                #if open_tag in self.short_tags:
                #    log("---- short tag", open_tag )
                #    try:
                #        self._builder.end(open_tag)
                #        open_tag, ns = self._ns.pop()
                #    except IndexError:
                #        return
                #    else:
                #        if ns:
                #            self._ns_close(ns)
                else:
                    # backtrack through the ns list to check if this is a stray tag open or close
                    bg_levels = 3
                    bg_start = 0 if len(self._ns) <= bg_levels else len(self._ns) - bg_levels
                    log("--- backtracking through", bg_levels, "levels starting from", bg_start)
                    tag = tag.lower()
                    try:
                        i = max(i for i, t in enumerate(self._ns[bg_start:]) if t[0] == tag)
                    except ValueError:
                        log("--- no backtracking possible, appending", open_tag, ns)
                        self._ns.append((open_tag, ns))
                        #if len(self._ns) == 1:
                        return
                    else:
                        log("---- closing expected open tag", open_tag)
                        if ns:
                            self._ns_close(ns)
                        self._autoclosed.append(open_tag)
                        self._builder.end(open_tag)
                        log("---- all elements", self._ns)
                        log("---- backtracked elements from", i + bg_start, self._ns[-(i+bg_start+1):])
                        for open_tag, ns in reversed(self._ns[i+bg_start+1:]):
                            log("---- closing backtracked tag", open_tag)
                            if ns:
                                self._ns_close(ns)
                            try:
                                self._builder.end(open_tag)
                            except IndexError:
                                pass
                        self._ns = self._ns[:i+bg_start]
        #if not self.strict:
        #    # check that the top-level element has been closed
        #    if not self._ns:
        #        self._parser.register(None)
        if ns:
            log("closing", ns)
            self._ns_close(ns)
        try:
            log("---> builder closing", tag)
            self._builder.end(tag)
            if len(self._ns) == 0:
                log("***** no more elements after", tag, "*****")
        except IndexError:
            pass
        
        # let's see if it makes a difference
        if not self._ns:
            self.closed = True

    def _ns_close(self, ns):
        for prefix, name, oldvalue in ns:
            if oldvalue is None and prefix in self._names:
                del(self._names[prefix])
            else:
                self._names[prefix] = oldvalue
        
    def handle_data(self, data):
        #log("data:", data)
        self._builder.data(data.decode('utf-8'))

        
def _test():
    import doctest
    doctest.testmod()

if __name__ == "__main__":
    _test()
