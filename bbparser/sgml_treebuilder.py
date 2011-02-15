"""A simple SGML tree builder with namespaces support, based on Fredrik Lundh's
SgmlopXMLTreeBuilder and his sgmlop library.

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

from sgmllib import SGMLParser

entitydefs = dict()
for k, v in htmlentitydefs.entitydefs.items():
    entitydefs[k] = v.decode('iso-8859-15')
entitydefs['apos'] = u"'"

short_tags = "area base basefont br col frame hr img input isindex link meta param".split()


class SGMLTreeBuilder(SGMLParser):
    """ElementTree builder for SGML source data, based on the SGMLOP parser.
    
    You need a new builder for each new document you need to parse. This is to
    make SgmlopTreeBuilder behave like the standard ElementTree TreeBuilder.
    Modifying it so that it can be reused is trivial.
    """
    
    entitydefs = entitydefs
    short_tags = dict(zip(short_tags, [None]*len(short_tags)))
    
    def __init__(self, decode=True, builder_class=None):
        SGMLParser.__init__(self)
        if not decode:
            self.unknown_charref = self._unknown_charref
            self.unknown_entityref = self._unknown_entityref
        self.warnings = list()
        self._ns = list()
        self._names = dict(xml='http://www.w3.org/XML/1998/namespace')
        builder = builder_class or et.TreeBuilder
        self._builder = builder()
    
    def feed(self, data):
        """Feeds data to the parser."""
        if isinstance(data, unicode):
            SGMLTreeBuilder.feed(self, data.encode('utf-8'))
        else:
            SGMLParser.feed(self, data)
        
    def close(self):
        """Finishes feeding data to the parser."""
        SGMLParser.close(self)
        SGMLParser.reset(self)
        tree = self._builder.close()
        return tree
    
    def unknown_charref(self, ref):
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
            self._builder.data("&#%s;" % ref)
        else:
            self._builder.data(unichr(ref))
            
    def unknown_entityref(self, ref):
        #if ref in ('amp', 'gt','lt'):
        #   self._builder.data('&%s;' % ref)
        #   return
        entity = self.entitydefs.get(ref, "&%s;" % ref)
        if entity[:2] == '&#':
            entity = self.handle_charref(entity[2:])
        self._builder.data(entity)
    
    def _unknown_charref(self, ref):
        self._builder.data("&#%s;" % ref)
        
    def _unknown_entityref(self, ref):
        self._builder.data("&%s;" % ref)
        
    def handle_comment(self, text):
        self._builder.data("<!--%s-->" % text)
        
    def unknown_starttag(self, tag, attrib):
        # look for namespaces in attributes
        ns = list()
        ns_attrib = []
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
                attrib[k] = v.decode('utf-8', 'replace')
            else:
                attrib[k] = ''
        for prefix, name, oldvalue in ns:
            self._names[prefix] = name
        for k in ns_attrib:
            prefix, name = k.split(':', 1)
            if prefix in self._names:
                attrib["{%s}%s" % (self._names[prefix], name)] = attrib[k]
                del(attrib[k])
        # now check the tag namespace
        pos = tag.find(':')
        if pos > 0:
            prefix = tag[:pos]
            tag = tag[pos+1:]
        else:
            prefix = None
        name = self._names.get(prefix)
        if name:
            tag = "{%s}%s" % (name, tag)
        self._ns.append((tag, ns))
        # now build the element
        #print '<--- open', tag, len(self._ns), self._ns
        try:
            self._builder.start(tag, attrib)
        except SyntaxError, e:
            self.warnings.append("SgmlopTreeBuilder error on tag '%s': %s" % (tag, e))

    def unknown_endtag(self, tag):
        """
        >>> doc = "<root><a><b><c>umph</a></c></root><other></other>"
        >>> t = SgmlopTreeBuilder()
        >>> t.feed(doc)
        >>> tree = t.close()
        >>> et.tostring(tree)
        '<root><a><b><c>umph</c></b></a></root>'
        >>> t.warnings
        ["SgmlopTreeBuilder error on tag 'other': multiple elements on top level"]
        >>> 
        """
        # check the tag namespace
        tag = tag.lower()
        pos = tag.find(':')
        if pos > 0:
            prefix = tag[:pos]
            tag = tag[pos+1:]
        else:
            prefix = None
        name = self._names.get(prefix)
        if name:
            tag = "{%s}%s" % (name, tag)
        #elif prefix:
        #    print "----> name not found!!!!!", prefix, self._names
        #print "---> closing", tag, len(self._ns), self._ns
        # decrease namespace counters, if any
        try:
            open_tag, ns = self._ns.pop()
        except IndexError:
            #print "ouch", tag
            pass
        else:
            if open_tag != tag:
                #print '--- stray close', tag, 'expected', open_tag
                # stray tag close, restore the ns list
                if open_tag in self.short_tags:
                    open_tag, ns = self._ns.pop()
                else:
                    # backtrack through the ns list to check if this is a stray tag open or close
                    found_at = None
                    for i, t in enumerate(reversed(self._ns)):
                        #print "checking", i, t
                        open_tag, ns = t
                        if open_tag.lower() == tag.lower():
                            #print "found", tag, "at", i
                            found_at = i + 1
                            break
                    if found_at is not None:
                        #print "slicing", self._ns, found_at
                        ns_slice = self._ns[-found_at:]
                        ns_slice.reverse()
                        #print "closing open tags", ns_slice
                        for open_tag, ns in ns_slice:
                            #print open_tag
                            if ns:
                                #print "closing", ns
                                self._ns_close(ns)
                            #print "end", open_tag
                            self._builder.end(open_tag)
                        self._ns = self._ns[:-found_at]
                    else:
                        self._ns.append((open_tag, ns))
                        if len(self._ns) == 1:
                            return
        #if not self.strict:
        #    # check that the top-level element has been closed
        #    if not self._ns:
        #        self._parser.register(None)
        if ns:
            #print "closing", ns
            self._ns_close(ns)
        try:
            self._builder.end(tag)
        except IndexError:
            pass

    def _ns_close(self, ns):
        for prefix, name, oldvalue in ns:
            if oldvalue is None and prefix in self._names:
                del(self._names[prefix])
            else:
                self._names[prefix] = oldvalue
        
    def handle_data(self, data):
        #print "data:", data
        self._builder.data(data.decode('utf-8'))

        
def _test():
    import doctest
    doctest.testmod()

if __name__ == "__main__":
    _test()
