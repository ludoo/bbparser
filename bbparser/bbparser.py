#! /usr/bin/python2.5

import re
import codecs
import datetime
import copy
import sgmlop
import iso8601
try:
    from xml.etree import cElementTree as et
except ImportError:
    from xml.etree import ElementTree as et
from xml.sax.saxutils import escape, unescape
from cgi import parse_header
from base64 import b64decode
from urlparse import urljoin
from email.utils import parsedate_tz

from sgmlop_treebuilder import SgmlopTreeBuilder

DECL_RE = re.compile(r"\<\?\s*xml\s+version=[\"|']1.0[\"|'](?:\s+encoding=[\"|'](.+?)[\"|'])?", re.I | re.S | re.M)

XML_BASE = '{http://www.w3.org/XML/1998/namespace}base'
XML_LANG = '{http://www.w3.org/XML/1998/namespace}lang'

SANE_TAGS = """\
a i em b strong p h1 h2 h3 h4 h5 ul ol dl li dt dd pre code q cite blockquote
abbr s u img style table theader tbody tr th td div span hr br sup sub center
caption col colgroup thead tfoot legend map area""".split()
SANE_ATTRS = ('title', 'style', 'align', 'border',) # TODO: remove align and border when tests pass
SANE_TAG_ATTRS = dict(a=('href', 'rel'), map=('name',), area=('coords', 'shape', 'href'), img=('src', 'alt', 'width', 'height', 'usemap'))
STRIP_TAGS_RE = re.compile(r'<[^>]+>', re.M|re.S|re.U)

UTC = iso8601.Utc()

# straight from feedparser
CP1252 = {
    unichr(128): unichr(8364), # euro sign
    unichr(130): unichr(8218), # single low-9 quotation mark
    unichr(131): unichr( 402), # latin small letter f with hook
    unichr(132): unichr(8222), # double low-9 quotation mark
    unichr(133): unichr(8230), # horizontal ellipsis
    unichr(134): unichr(8224), # dagger
    unichr(135): unichr(8225), # double dagger
    unichr(136): unichr( 710), # modifier letter circumflex accent
    unichr(137): unichr(8240), # per mille sign
    unichr(138): unichr( 352), # latin capital letter s with caron
    unichr(139): unichr(8249), # single left-pointing angle quotation mark
    unichr(140): unichr( 338), # latin capital ligature oe
    unichr(142): unichr( 381), # latin capital letter z with caron
    unichr(145): unichr(8216), # left single quotation mark
    unichr(146): unichr(8217), # right single quotation mark
    unichr(147): unichr(8220), # left double quotation mark
    unichr(148): unichr(8221), # right double quotation mark
    unichr(149): unichr(8226), # bullet
    unichr(150): unichr(8211), # en dash
    unichr(151): unichr(8212), # em dash
    unichr(152): unichr( 732), # small tilde
    unichr(153): unichr(8482), # trade mark sign
    unichr(154): unichr( 353), # latin small letter s with caron
    unichr(155): unichr(8250), # single right-pointing angle quotation mark
    unichr(156): unichr( 339), # latin small ligature oe
    unichr(158): unichr( 382), # latin small letter z with caron
    unichr(159): unichr( 376), # latin capital letter y with diaeresis
}

# TODO: sanitize element attributes where we use them like we do for tags
# TODO: apply xml:base only if we don't have a netloc
# TODO: check id/link attributes


class ParserError(Exception):
    pass

class NoData(ParserError):
    pass

class UnknownRoot(ParserError):
    pass

class DummyFile(list):
    write = list.append

def _urljoin(root, rel):
    if not root:
        return rel
    if not rel:
        return root
    if root[-1] != '/':
        root = "%s/" % root
    if rel[0] == '/':
        rel = rel[1:]
    return urljoin(root, rel)
    
def tostring(element):
    f = DummyFile()
    t = et.ElementTree(element)
    t._write(f, t._root, 'utf8', {})
    return ''.join(f)

def cleanup(elem, ns='{http://www.w3.org/1999/xhtml}', xml_base=None):
    """http://effbot.org/zone/element-bits-and-pieces.htm"""
    out = []
    l = len(ns)
    if elem.tag[:l] == ns:
        elem.tag = elem.tag[l:]
    attrib = dict()
    xml_base = elem.attrib.get(XML_BASE, xml_base)
    safe_attrib = SANE_ATTRS + SANE_TAG_ATTRS.get(elem.tag, tuple())
    for k, v in elem.attrib.items():
        if k[:l] == ns:
            k = k[l:]
        if not k in safe_attrib:
            continue
        if k in ('href', 'src') and xml_base:
            # check with urlsplit that it's a relative URL
            v = _urljoin(xml_base, v)
        attrib[k] = v
    elem.attrib = attrib
    for e in elem:
        cleanup(e, ns, xml_base=xml_base)
        if not e.tag in SANE_TAGS:
            if e.text:
                if out:
                    out[-1].tail = u"%s%s" % (out[-1].tail or '', e.text)
                else:
                    if elem.text is None: # is this really necessary?
                        elem.text = ''
                    elem.text += e.text
            out.extend(e)
            if e.tail:
                if out:
                    out[-1].tail = out[-1].tail or ''
                    out[-1].tail += e.tail
                else:
                    elem.text = "%s%s" % (elem.text or '', e.tail)
        else:
            out.append(e)
    elem[:] = out

class FeedBase(type):
    """Metaclass for feed types."""
    
    def __new__(cls, name, bases, attrs):
        register = None
        try:
            if not [b for b in bases if issubclass(b, Feed)]:
                register = False
        except (NameError, TypeError):
            register = False
        new_class = super(FeedBase, cls).__new__(cls, name, bases, attrs)
        if register is None and '_root_element' in attrs:
            root_element = attrs['_root_element']
            for namespace in attrs.get('_namespaces', tuple()):
                if namespace:
                    namespace = "{%s}" % namespace
                else:
                    namespace = ''
                Feed._feed_map["%s%s" % (namespace, root_element)] = new_class
        return new_class
        

class Feed(object):
    
    _feed_map = dict()
    __metaclass__ = FeedBase

    def __init__(self, tree, ns, warnings=list(), xml_base='', feedparser_compat=True):
        self.tree = tree
        self.warnings = warnings
        self.ns = ns
        self.xml_base = tree.attrib.get(XML_BASE, '') or xml_base
        self.xml_lang = tree.attrib.get(XML_LANG, '')
        self.feedparser_compat = feedparser_compat
    
    @classmethod
    def factory(cls, tree, warnings, feedparser_compat=True):
        ns = None
        tag = tree.tag
        if tag[0] == '{':
            ns, sep, tag = tag[1:].rpartition('}')
        if not tree.tag in cls._feed_map:
            raise UnknownRoot("Cannot parse feed with root '%s'." % tag)
        return cls._feed_map[tree.tag](tree, ns, warnings, feedparser_compat=feedparser_compat)
    
    def _ns_join(self, tag, ns=None):
        ns = ns or self.ns
        if ns is None:
            return tag
        return "{%s}%s" % (ns, tag)
    
    def _cp1252(self, s):
        if not s:
            return s
        # straight from feedparser
        # address common error where people take data that is already
        # utf-8, presume that it is iso-8859-1, and re-encode it.
        try:
            s = s.encode('iso-8859-1').decode('utf-8')
        except (UnicodeEncodeError, UnicodeDecodeError):
            pass
        s = s.replace('\r\n', '\n')
        return u''.join(CP1252.get(c, c) for c in s)
    
    def _element_to_string(self, el):
        """
        >>> f = Feed(et.XML('<doc />'), list(), None, None)
        >>> f._element_to_string(f.tree)
        u''
        >>> tree = et.XML('<doc>&amp;a</doc>')
        >>> f._element_to_string(tree)
        '&amp;a'
        >>> tree = et.XML('<doc>&amp;0<a>a</a>1<b>b<c>c</c></b>2</doc>')
        >>> f._element_to_string(tree)
        u'&amp;0<a>a</a>1<b>b<c>c</c></b>2'
        >>> 
        """
        if el.text is None:
            text = u''
        else:
            text = escape(el.text)
        if len(el) == 0:
            return text
        buffer = [text]
        for e in el.getchildren():
            buffer.append(tostring(e).decode('utf8'))
        return u''.join(buffer)
    
    def _sanitize_text(self, text, rss_text=False):
        """
        >>> f = Feed(et.XML('<doc />'), list(), None, None)
        >>> f._sanitize_text('<p><br /></p>')
        u'<p><br /></p>'
        >>> f._sanitize_text('<p><br /><dummy /></p>')
        u'<p><br /></p>'
        >>> f._sanitize_text('<p><br /><dummy><em>valid inside dummy</em></dummy></p>')
        u'<p><br /><em>valid inside dummy</em></p>'
        >>> f._sanitize_text('<p><br /><dummy><em title="valid attr" onclick="invalid attr">valid &amp; <a href="">inside</a> dummy</em></dummy></p>')
        u'<p><br /><em title="valid attr">valid &amp; <a href="">inside</a> dummy</em></p>'
        >>> 
        """
        # TODO: use a custom parser so that we do not have to build a tree then
        # loop on each of its elements
        tb = SgmlopTreeBuilder(skip_ns=('http://www.w3.org/1999/xhtml',))
        tb.feed(u'<div>%s</div>' % text)
        tree = tb.close()
        if not self.feedparser_compat or not rss_text:
            cleanup(tree, xml_base=self.xml_base)
            return tostring(tree).decode('utf8')[5:-6].strip()
        # use the following instead of the two preceding lines to leave
        # simple text unescaped
        if len(tree) > 0:
            cleanup(tree, xml_base=self.xml_base)
            return tostring(tree).decode('utf8')[5:-6].strip()
        else:
            return '' if tree.text is None else tree.text.strip()
    
    @property
    def fb_origlink(self):
        # should be moved to entry classes and renamed, but I don't care...
        if not hasattr(self, '_fb_origlink'):
            el = self.tree.find('{http://rssnamespace.org/feedburner/ext/1.0}origlink')
            self._fb_origlink = None
            if el is not None and isinstance(el.text, basestring):
                self._fb_origlink = el.text.strip()
        return self._fb_origlink

    @property
    def tags(self):
        if not hasattr(self, '_tags'):
            _tags = list()
            for el in self.tree.findall(self._ns_join('category')):
                tag = dict(term=None, scheme=None, label=None)
                if isinstance(el.text, basestring):
                    tag['term'] = el.text.strip()
                tag['scheme'] = el.attrib.get('domain')
                for a in ('term', 'scheme', 'label'):
                    value = el.attrib.get(a, None)
                    if isinstance(value, basestring):
                        tag[a] = STRIP_TAGS_RE.sub('', value)
                if tag['term'] and tag not in _tags:
                    _tags.append(tag)
            # check dc:subject too
            for el in  self.tree.findall(self._ns_join('subject', 'http://purl.org/dc/elements/1.1/')):
                if len(el) > 0:
                    # should not happen
                    text = self._element_to_string(el)
                else:
                    text = el.text
                if isinstance(text, basestring):
                    text = STRIP_TAGS_RE.sub('', text)
                tag = dict(term=text, scheme=None, label=None)
                if tag['term'] and tag not in _tags:
                    _tags.append(tag)
            self._tags = _tags
        return self._tags
    

class Atom(Feed):
    
    def __init__(self, tree, ns, warnings, xml_base='', feedparser_compat=True):
        super(Atom, self).__init__(tree, ns, warnings, xml_base, feedparser_compat=True)
        if self.ns == 'http://www.w3.org/2005/Atom':
            self.atom_version = '1.0'
        else:
            self.atom_version = '0.3'
            # use a conditional inside the method or we get pickling errors
            # self._element_text = self._element_text_03
    
    @property
    def links(self):
        if not hasattr(self, '_links'):
            links = list()
            for el in self.tree.findall(self._ns_join('link')):
                link = dict(href='', type='', rel='alternate', title='')
                link.update(el.attrib)
                if link['href']:
                    link['href'] = _urljoin(el.attrib.get(XML_BASE, self.xml_base), link['href'])
                links.append(link)
            self._links = links
        return self._links
    
    @property
    def link(self):
        if not hasattr(self, '_link'):
            self._link = None
            if len(self.links) == 1:
                self._link = self.links[0]['href']
            else:
                links = list()
                for link in self.links:
                    if link['rel'] == 'alternate': # and link['type'] == 'application/xhtml+xml':
                        links.append((0, link['href']))
                    elif not link['rel']:
                        links.append((1, link['href']))
                if links:
                    links.sort()
                    self._link = links[0][1]
        return self._link
    
    @property
    def title(self):
        if not hasattr(self, '_title'):
            el = self.tree.find(self._ns_join('title'))
            self._title = self._element_text(el) if el is not None else None
        return self._title
    
    @property
    def id(self):
        # TODO: relative URLs
        if not hasattr(self, '_id'):
            el = self.tree.find(self._ns_join('id'))
            if el and el.text is not None:
                self._id = STRIP_TAGS_RE.sub('', el.text)
            else:
                self._id = None
        return self._id
    
    def _element_text_html(self, el, is_text=False):
        if len(el) > 0:
            # we have child elements, it's an error (cf. RFC4287 3.1.1.2)
            if not is_text:
                self.warnings.append("Element '%s' of type 'html' has child elements." % el.tag)
            # regenerate it as string, but clean up namespaces etc. first
            cleanup(el, "{%s}" % self.ns, xml_base=self.xml_base)
            text = self._element_to_string(el)
            if is_text:
                text = escape(text)
            return text
        else:
            text = el.text
        if text is None:
            return
        if not text.strip():
            # skip the sanitization process
            return u''
        if is_text:
            text = escape(text)
        return self._sanitize_text(text)
    
    def _element_text_xhtml(self, el, xml_base=None):
        cleanup(el, xml_base=xml_base)
        return self._element_to_string(el)
        
    def _element_text(self, el):
        if self.atom_version ==  '0.3':
            text_type = el.attrib.get('type', 'text')
            text_mode = el.attrib.get('mode', 'xml')
            
            if text_mode == 'base64':
                if not el.text:
                    return
                el = copy.deepcopy(el)
                el.text = b64decode(el.text)
    
            if text_type in ('xhtml', 'application/xhtml+xml'):
                if len(el) != 1:
                    # the first and only element should be a div
                    self.warnings.append("Element '%s' of type 'xhtml' has more than one child." % el.tag)
                    return self._element_text_html(el)
                child = el.getchildren()[0]
                if child.tag != '{http://www.w3.org/1999/xhtml}div':
                    self.warnings.append("Element '%s' of type 'xhtml' has a child of '%s' instead of '{http://www.w3.org/1999/xhtml}div'." % (el.tag, child.tag))
                return self._cp1252(self._element_text_xhtml(child, el.attrib.get(XML_BASE, self.xml_base)))
            else:
                # treat as html anyway so that we can parse and sanitize it
                # text should not be escaped and sanitized as it's just text,
                # but for my needs text will be used in the same way as html/xhtml,
                # and so needs to be escaped
                return self._cp1252(self._element_text_html(el, is_text=(text_type in ('text', 'text/plain'))))
        else:
            text_type = el.attrib.get('type', 'text')
            if text_type == 'xhtml':
                if len(el) != 1:
                    # the first and only element should be a div
                    self.warnings.append("Element '%s' of type 'xhtml' has more than one child." % el.tag)
                    return self._element_text_html(el)
                child = el.getchildren()[0]
                if child.tag != '{http://www.w3.org/1999/xhtml}div': #self._ns_join(child, self.ns):
                    self.warnings.append("Element '%s' of type 'xhtml' has a child of '%s' instead of '{http://www.w3.org/1999/xhtml}div'." % (el.tag, child.tag))
                return self._cp1252(self._element_text_xhtml(child, el.attrib.get(XML_BASE, self.xml_base)))
            else:
                # treat as html anyway so that we can parse and sanitize it
                # text should not be escaped and sanitized as it's just text,
                # but for my needs text will be used in the same way as html/xhtml,
                # e.g. rendered unescaped on a page, and so needs to be escaped
                return self._cp1252(self._element_text_html(el, is_text=(text_type=='text')))
        
    
class AtomEntry(Atom):
    
    def __init__(self, *args, **kw):
        super(AtomEntry, self).__init__(*args, **kw)
    
    @property
    def summary(self):
        if not hasattr(self, '_summary'):
            el = self.tree.find(self._ns_join('summary'))
            self._summary = self._element_text(el) if el is not None else None
        return self._summary
        
    ### TODO ###
    #   the atom:entry contains content that is encoded in Base64;
    #   i.e., the "type" attribute of atom:content is a MIME media type
    #   [MIMEREG], but is not an XML media type [RFC3023], does not
    #   begin with "text/", and does not end with "/xml" or "+xml".
    #   http://www.ietf.org/rfc/rfc4287.txt
    #   http://www.xml.com/lpt/a/1633
    
    @property
    def content(self):
        # TODO: check older versions of atom against the rfc
        # "atom:entry elements MUST NOT contain more than one atom:content element"
        if not hasattr(self, '_content'):
            _content = list()
            for el in self.tree.findall(self._ns_join('content')):
                content = {'type':'text', 'language':'', 'value':''}
                content.update(el.attrib)
                content['value'] = self._element_text(el) if el is not None else None
                if content['type'] == 'text':
                    content['type'] = 'text/plain'
                _content.append(content)
            if not _content and self.summary:
                _content.append({'type':'text/html', 'language':'', 'value':self.summary})
            self._content = _content
        return self._content
    
    @property
    def updated(self):
        return self._get_date_element('updated')
    
    @property
    def published(self):
        return self._get_date_element('published')
    
    @property
    def modified(self):
        return self._get_date_element('modified')
    
    @property
    def issued(self):
        return self._get_date_element('issued')
    
    @property
    def created(self):
        return self._get_date_element('created')
    
    @property
    def date_published(self):
        return self.published or self.issued or self.updated

    def _get_date_element(self, name):
        _name = '_%s' % name
        if not hasattr(self, _name):
            el = self.tree.find(self._ns_join(name))
            value = None
            if el is not None and el.text is not None:
                try:
                    value = iso8601.parse_date(el.text)
                except (ValueError, iso8601.ParseError):
                    self.warnings.append("Incorrect '%s' format '%s'" % (name, el.text))
                else:
                    value = value.astimezone(UTC)
            setattr(self, _name, value)
            return value
        return getattr(self, _name)

    
class AtomFeed(Atom):
    
    _root_element = 'feed'
    _namespaces = (
        'http://www.w3.org/2005/Atom', 'http://purl.org/atom/ns#',
        'http://example.com/newformat#', 'http://example.com/necho',
        'http://purl.org/echo/', 'http://purl.org/pie/',
    )
    
    def __init__(self, *args, **kw):
        super(AtomFeed, self).__init__(*args, **kw)
        if not self.xml_base and self.link:
            self.xml_base = self.link
        
    @property
    def entries(self):
        if not hasattr(self, '_entries'):
            _entries = list()
            for el in self.tree.findall(self._ns_join('entry')):
                _entries.append(AtomEntry(el, self.ns, self.warnings, xml_base=self.xml_base))
            self._entries = _entries
        return self._entries
        

class Rss(Feed):

    _two_digit_year_re = re.compile(r'\s\d{2}\s\d{2}:\d{2}:\d{2}\s')
    _stupid_date_re = (
        re.compile(r'(?P<day>[0-9]{2})\.(?P<month>[0-9]{2})\.(?P<year>[0-9]{4})\s\-\s(?P<hour>[0-9]{2}):(?P<minute>[0-9]{2})', re.M|re.S),
        re.compile(r'\s*(?P<month>[0-9]{2})\s+(?P<day>[0-9]{2})\s+(?P<year>[0-9]{4})\s+(?P<hour>[0-9]{2}):(?P<minute>[0-9]{2}):(?P<second>[0-9]{2})(?:\s+[A-Za-z0-9+.-]+)?\s*', re.M|re.S),
    )
    
    def _element_text(self, el):
        if len(el) > 0:
            # we have child elements, let's clean them up
            cleanup(el, "{%s}" % self.ns, xml_base=self.xml_base)
            text = self._element_to_string(el)
            return text
        else:
            text = el.text
        if text is None:
            return
        if not text.strip():
            # skip the sanitization process
            return u''
        return self._sanitize_text(self._cp1252(text), True)
    
    def _stupid_date_fix(self, d):
        t = datetime.date.today()
        defaults = dict(year=t.year, month=t.month, day=t.day, hour=0, minute=0, second=0)
        for k, v in defaults.items():
            if not k in d:
                d[k] = v
        for k, v in d.items():
            if v and isinstance(v, basestring):
                # check if we have a leading zero
                if v[0] == '0':
                    v = v[1:]
                try:
                    d[k] = int(v)
                except (TypeError, ValueError):
                    d[k] = defaults.get(k)
            else:
                d[k] = defaults.get(k)
        d['tzinfo'] = iso8601.UTC
        try:
            return datetime.datetime(**d)
        except (TypeError, ValueError):
            return None
        
    def _get_date_element(self, name):
        _name = '_%s' % name
        if not hasattr(self, _name):
            el = self.tree.find(self._ns_join(name))
            value = None
            if el is not None and el.text is not None:
                d = parsedate_tz(el.text)
                if isinstance(d, tuple):
                    if self._two_digit_year_re.search(el.text):
                        d = ((d[0] + 2000),) + d[1:]
                    try:
                        value = datetime.datetime(*(d[:-3] + (iso8601.UTC,))) - datetime.timedelta(seconds=d[-1])
                    except TypeError, e:
                        value = datetime.datetime(*(d[:-3] + (iso8601.UTC,)))
                        self.warnings.append("Incorrect '%s' format '%s' timetuple '%s', error %s" % (name, el.text, d, e))
                    except ValueError:
                        pass
                if value is None:
                    # try with iso8601
                    try:
                        value = iso8601.parse_date(el.text)
                    except (ValueError, iso8601.ParseError):
                        pass
                    else:
                        value = value.astimezone(UTC)
                if value is None:
                    # try with the stupid formats seen in the wild
                    for r in self._stupid_date_re:
                        m = r.match(el.text)
                        if m:
                            value = self._stupid_date_fix(m.groupdict())
                            if value:
                                break
            else:
                # look for dc:date
                el = self.tree.find(self._ns_join('date', 'http://purl.org/dc/elements/1.1/'))
                if el is not None and el.text is not None:
                    try:
                        value = iso8601.parse_date(el.text)
                    except (ValueError, iso8601.ParseError):
                        self.warnings.append("Incorrect '%s' format '%s'" % (name, el.text))
                    else:
                        value = value.astimezone(UTC)
            if el is not None and value is None:
                self.warnings.append("Incorrect '%s' format '%s'" % (name, el.text if el is not None else ''))
            setattr(self, _name, value)
            return value
        return getattr(self, _name)

    @property
    def title(self):
        if not hasattr(self, '_title'):
            el = self.tree.find(self._ns_join('title'))
            if el is None:
                el = self.tree.find(self._ns_join('title', 'http://purl.org/dc/elements/1.1/'))
            self._title = self._element_text(el) if el is not None else None
        return self._title
        
    @property
    def link(self):
        if not hasattr(self, '_link'):
            el = self.tree.find(self._ns_join('link'))
            if el is not None:
                self._link = el.text if len(el) == 0 else None
            else:
                self._link = None
        return self._link
    
    @property
    def links(self):
        return list()

    @property
    def pubdate(self):
        return self._get_date_element('pubdate')
    
    @property
    def date_published(self):
        return self.pubdate
    
    
class RssFeed(Rss):
    
    _root_element = 'rss'
    _namespaces = (
        None, 'http://backend.userland.com/rss',
        'http://backend.userland.com/rss2',
        'http://backend.userland.com/rss2.1',
        'http://blogs.law.harvard.edu/tech/rss',
    )
    
    def __init__(self, *args, **kw):
        super(RssFeed, self).__init__(*args, **kw)
        self.version = self.tree.attrib.get('version')
        channel = self.tree.find(self._ns_join('channel'))
        if channel is None:
            raise ValueError("RSS feed has no channel element")
        self._tree = self.tree
        self.tree = channel

    @property
    def title(self):
        title = super(RssFeed, self).title
        if title:
            return title
        return self.description
        
    @property
    def description(self):
        if not hasattr(self, '_description'):
            el = self.tree.find(self._ns_join('description'))
            self._description = self._element_text(el) if el is not None else None
        return self._description
    
    @property
    def entries(self):
        if not hasattr(self, '_entries'):
            _entries = list()
            for el in self.tree.findall(self._ns_join('item')):
                _entries.append(RssEntry(el, self.ns, self.warnings))
            self._entries = _entries
        return self._entries


class RssEntry(Rss):
    
    def __init__(self, *args, **kw):
        super(RssEntry, self).__init__(*args, **kw)
        self._guid_is_link = True
    
    @property
    def link(self):
        link = super(RssEntry, self).link
        if link:
            return link.strip()
        if self.guid and self._guid_is_link:
            return self.guid
    
    @property
    def guid(self):
        # TODO: relative URL
        if not hasattr(self, '_guid'):
            el = self.tree.find(self._ns_join('guid'))
            if el is not None:
                self._guid = el.text if len(el) == 0 else None
                if el.attrib.get('ispermalink') == 'false':
                    self._guid_is_link = False
            else:
                self._guid = None
        return self._guid
    
    id = guid
    
    @property
    def description(self):
        if not hasattr(self, '_description'):
            el = self.tree.find(self._ns_join('description'))
            if el is None:
                el = self.tree.find(self._ns_join('description', 'http://purl.org/dc/elements/1.1/'))
            if el is None:
                el = self.tree.find(self._ns_join('summary', 'http://www.w3.org/2005/Atom'))
            if el is not None:
                cleanup(el, xml_base=self.xml_base)
                self._description = self._element_text(el)
            else:
                self._description = None
        return self._description
    
    summary = description
    
    @property
    def content(self):
        if not hasattr(self, '_content'):
            _content = list()
            tags = (
                ('body', None, 'text/html'),
                ('fullitem', None, 'text/html'),
                ('body', 'http://www.w3.org/1999/xhtml', 'application/xhtml+xml'),
                ('encoded', 'http://purl.org/rss/1.0/modules/content/', 'text/html'),
            )
            for tag, ns, content_type in tags:
                el = self.tree.find(self._ns_join(tag, ns))
                if el is None:
                    continue
                content = {'type':content_type, 'language':'', 'value':''}
                content.update(el.attrib)
                cleanup(el, xml_base=self.xml_base)
                content['value'] = self._element_text(el)
                _content.append(content)
            if not _content and self.summary:
                _content.append({'type':'text/html', 'language':'', 'value':self.summary})
            self._content = _content
        return self._content

    
class RdfFeed(RssFeed):
    
    _root_element = 'rdf'
    _namespaces = (None, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#',)

    def __init__(self, *args, **kw):
        super(RssFeed, self).__init__(*args, **kw)
        self._ns = self.ns
        ns = 'http://purl.org/rss/1.0/'
        channel = None
        for el in self.tree.getchildren():
            if el.tag.endswith('channel'):
                # grab the namespace
                if el.tag[0] == '{':
                    ns = el.tag[1:el.tag.find('}')]
                    channel = el
                    break
        if channel is None:
            raise ValueError("RSS feed with ns %s has no channel element %s" % (self.ns, self.tree.getchildren()))
        self.ns = ns
        self._tree = self.tree
        self.tree = channel
        if self.ns == 'http://my.netscape.com/rdf/simple/0.9/':
            self.version = '0.90'
        else:
            self.version = '1.0'

    @property
    def entries(self):
        if not hasattr(self, '_entries'):
            _entries = list()
            for el in self._tree.findall(self._ns_join('item')):
                _entries.append(RdfEntry(el, self.ns, self.warnings, rdf_ns=self._ns))
            self._entries = _entries
        return self._entries


class RdfEntry(RssEntry):
    
    def __init__(self, *args, **kw):
        self._ns = kw['rdf_ns']
        del(kw['rdf_ns'])
        super(RdfEntry, self).__init__(*args, **kw)
    
    @property
    def id(self):
        if not hasattr(self, '_id'):
            self._id = self.tree.attrib.get(self._ns_join('about', self._ns))
        return self._id


# TODO: move the following to be Feed class methods?

def decode(source, headers):
    warnings = list()
    content_type = headers.get('content-type', '')
    http_charset = None
    if content_type:
        content_type, params = parse_header(content_type)
        http_charset = params.get('charset', '').replace("'", '').strip()
    if http_charset:
        try:
            http_charset = codecs.lookup(http_charset).name
        except LookupError:
            warnings.append("unknown HTTP encoding %s" % http_charset)
            http_charset = None
    xml_charset = None
    m = DECL_RE.search(source)
    if m and m.group(1):
        try:
            xml_charset = codecs.lookup(m.group(1)).name
        except LookupError:
            warnings.append("unknown XML encoding %s" % m.group(1))
    if content_type in ('application/xml', 'application/xml-dtd', 'application/xml-external-parsed-entity'):
        charsets = [http_charset, xml_charset, 'utf-8']
    elif content_type.startswith('application/') and content_type.endswith('+xml'):
        charsets = [http_charset, xml_charset, 'utf-8']
    elif content_type in ('text/xml', 'text/xml-external-parsed-entity'):
        charsets = [http_charset, 'ascii', xml_charset]
    elif content_type.startswith('text/') and content_type.endswith('+xml'):
        charsets = [http_charset, 'ascii', xml_charset]
    elif content_type.startswith('text/'):
        charsets = [http_charset, 'ascii', xml_charset]
    elif headers and not content_type:
        charsets = [xml_charset, 'iso-8859-15']
    else:
        charsets = [xml_charset, 'utf-8']
    charsets = set(charsets)
    for c in charsets:
        if not c:
            continue
        try:
            source = source.decode(c)
        except UnicodeDecodeError:
            continue
        except LookupError, e:
            warnings.append("Error decoding feed: %s" % e)
            continue
        else:
            encoding = c
            break
    if not isinstance(source, unicode):
        warnings.append(
            "no valid charset in %s with http_charset %s and xml charset %s" % (
                charsets, http_charset, xml_charset)
        )
        for c in set(['iso-8859-15', 'utf-8']).difference(charsets):
            try:
                source = source.decode(c, 'replace')
            except UnicodeDecodeError:
                continue
            else:
                encoding = c
                break
    if not isinstance(source, unicode):
        raise UnicodeDecodeError, "cannot decode data, tried %s" % charsets
    return source, warnings

def parse(source, headers=None, try_strict=False, feedparser_compat=True):
    headers = headers or dict()
    if not isinstance(source, unicode):
        # convert to unicode
        source, warnings = decode(source, headers)
    else:
        warnings = list()
    source = source.encode('utf8')
    tree = None
    if try_strict:
        parsers = ((et.XMLTreeBuilder, dict()), (SgmlopTreeBuilder, dict(parser_class=sgmlop.XMLParser)))
    else:
        parsers = ((SgmlopTreeBuilder, dict(parser_class=sgmlop.XMLParser)),)
    for parser, kw in parsers:
        p = parser(**kw)
        try:
            p.feed(source)
            tree = p.close()
        except SyntaxError, e:
            warnings.append("Error parsing using %s: %s" % (parser, e))
            continue
        except AssertionError, e:
            warnings.append("Error parsing feed: %s" % e)
            continue
        else:
            if hasattr(parser, 'warnings'):
                warnings += parser.warnings
            break
    if not tree:
        raise NoData("No valid feed found, warnings: %s" % "\n".join(warnings))
    p = None
    return Feed.factory(tree, warnings, feedparser_compat)


def _test():
    import doctest
    doctest.testmod()


if __name__ == "__main__":
    _test()
