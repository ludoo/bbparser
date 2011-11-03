========
BBParser
========

BBParser is a fast, easy to modify feed parser library for Python.

It was written as a replacement for Mark Pilgrim's ubiquitous feedparser library,
which I used for a large feed aggregator and which had several problems dealing
with malformed utf8 feeds. Writing a feed parser from scratch was easier than
fixing feedparser, which is a very useful but convoluted piece of code.

BBParser makes heavy use of Fredrik Lundh's sgmlop library, which is blazing fast
and can parse even the most horribly malformed feeds.

Usage notes and examples soon.

