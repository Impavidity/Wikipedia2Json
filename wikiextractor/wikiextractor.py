#!/usr/bin/python
# -*- coding: utf-8 -*-

# The following code is based on the github project
#   https://github.com/jodaiber/Annotated-WikiExtractor
# which is, in turn, based on the wikiextractor by Medialab
#   http://medialab.di.unipi.it/wiki/Wikipedia_Extractor


# =============================================================================
#  Based on:
#
#  Version: 0.1 (Jan 26, 2010)
#  Author: Joachim Daiber (jo.daiber@fu-berlin.de)
#  https://github.com/jodaiber/Annotated-WikiExtractor
#
#  and
#
#  Version: 1.5 (Oct 17, 2009)
#  Author: Antonio Fuschetto (fuschett@di.unipi.it), University of Pisa
#  http://medialab.di.unipi.it/wiki/Wikipedia_Extractor
#
#  Modified by:
#  Soufian Jebbara, Semantic Computing Group, Bielefeld University, Germany
#
#  Modified by:
#  Sebastian Walter -> ported sourcecode to work with python 3.4 and higher
#
# =============================================================================

# =============================================================================
#  This project is a free software; you can redistribute it and/or modify it
#  under the terms of the GNU General Public License, version 3,
#  as published by the Free Software Foundation.
#
#  This project is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program.  If not, see <http://www.gnu.org/licenses/>.
# =============================================================================

import io
import sys
import getopt
import urllib
import re
import bz2
import os.path
import ujson
import urllib.parse
from multiprocessing import Pool

"""Wikipedia Extractor:
Extracts and cleans text from Wikipedia database dump and stores output in a
number of files of similar size in a given directory. In each line of these files,
a wikipedia page is stored in JSON format.

Usage:
  python wikiextractor.py [options] < your_wikipedia_dump.xml

Options:
  -c, --compress        : compress output files using bzip2 algorithm
  -b ..., --bytes=...   : put specified bytes per output file (500K by default)
  -o ..., --output=...  : place output files in specified directory (current
                          directory by default)
  --help                : display this help and exit
  --usage               : display script usage
  -w ..., --workers=... : use specified number of workers
  -p ..., --prefix=...  : use specified url prefix (default is 'http://en.wikipedia.org/wiki/')
"""


### SUPPORT CLASSES ###########################################################

class AnnotatedWikiDocument(dict):
    __slots__ = ['default', 'id', 'url', "title", 'text', 'annotations']

    def __init__(self, default=None, **kwargs):
        super(AnnotatedWikiDocument, self).__init__(**kwargs)
        self.default = default
        self.id = None
        self.url = None
        self.title = None
        self.text = None
        self.annotations = None

    def __str__(self):
        self["id"] = self.id
        self["url"] = self.url
        self["title"] = self.title
        self["text"] = self.text
        self["annotations"] = self.annotations
        return ujson.dumps(self) + "\n"


def get_wiki_document_url(wiki_document_title, prefix, quote=False):
    if quote:
        title = urllib.parse.quote(wiki_document_title.replace(' ', '_').encode('utf-8'))
        title = title.replace('%28', '(')
        title = title.replace('%29', ')')
        title = title.replace('%3A', ':')
        title = title.replace('%22', '"')
        title = title.replace('%27', "'")
    else:
        title = wiki_document_title.replace(' ', '_')

    return prefix + title[0].upper() + title[1:]


class AnnotatedWikiExtractor(object):
    __garbage_tags = (
        'ref', 'gallery', 'timeline', 'noinclude', 'pre', 'table', 'tr', 'td', 'ul', 'li', 'ol', 'dl', 'dt', 'dd',
        'menu', 'dir')
    __wrapper_tags = (
        'nowiki', 'cite', 'source', 'hiero', 'div', 'font', 'span', 'strong', 'strike', 'blockquote', 'tt', 'var',
        'sup', 'sub', 'big', 'small', 'center', 'h1', 'h2', 'h3', 'em', 'b', 'i', 'u', 'a', 's', 'p')
    __single_tags = ('references', 'ref', 'img', 'br', 'hr', 'li', 'dt', 'dd')
    __placeholder_tags = {'math': 'formula', 'code': 'codice'}

    __project_namespaces = (
        'wikipedia', 'mediawiki', 'wikiquote', 'wikibooks', 'wikisource', 'wiktionary', 'wikispecies', 'wikinews',
        'wikiversity', 'commons', 'wikicities', 'wikispot')

    __garbage_link_prefixes = (
        'image', 'category', 'file', 'http', 'https', 'simple', 'meta', 'wikipedia', "media", 'template', 'portal',
        'user', 'wikt', 'wikihow', "help", "user talk", "special", "s", "b", "v", "q", "?")

    __allowed_prefixes = ('w:', "en:")

    __garbage_page_prefixes = (
        'Image:', 'Category:', 'File:', 'Wikipedia:', 'Template:', 'Portal:', 'User:', "Help:", "Book:", "Draft:",
        "Module:", "TimedText:", "MediaWiki:")

    __char_entities = {'&nbsp;': u'\u00A0', '&iexcl;': u'\u00A1', '&cent;': u'\u00A2', '&pound;': u'\u00A3',
                       '&curren;': u'\u00A4', '&yen;': u'\u00A5', '&brvbar;': u'\u00A6', '&sect;': u'\u00A7',
                       '&uml;': u'\u00A8', '&copy;': u'\u00A9', '&ordf;': u'\u00AA', '&laquo;': u'\u00AB',
                       '&not;': u'\u00AC', '&shy;': u'\u00AD', '&reg;': u'\u00AE', '&macr;': u'\u00AF',
                       '&deg;': u'\u00B0', '&plusmn;': u'\u00B1', '&sup2;': u'\u00B2', '&sup3;': u'\u00B3',
                       '&acute;': u'\u00B4', '&micro;': u'\u00B5', '&para;': u'\u00B6', '&middot;': u'\u00B7',
                       '&cedil;': u'\u00B8', '&sup1;': u'\u00B9', '&ordm;': u'\u00BA', '&raquo;': u'\u00BB',
                       '&frac14;': u'\u00BC', '&frac12;': u'\u00BD', '&frac34;': u'\u00BE', '&iquest;': u'\u00BF',
                       '&Agrave;': u'\u00C0', '&Aacute;': u'\u00C1', '&Acirc;': u'\u00C2', '&Atilde;': u'\u00C3',
                       '&Auml;': u'\u00C4', '&Aring;': u'\u00C5', '&AElig;': u'\u00C6', '&Ccedil;': u'\u00C7',
                       '&Egrave;': u'\u00C8', '&Eacute;': u'\u00C9', '&Ecirc;': u'\u00CA', '&Euml;': u'\u00CB',
                       '&Igrave;': u'\u00CC', '&Iacute;': u'\u00CD', '&Icirc;': u'\u00CE', '&Iuml;': u'\u00CF',
                       '&ETH;': u'\u00D0', '&Ntilde;': u'\u00D1', '&Ograve;': u'\u00D2', '&Oacute;': u'\u00D3',
                       '&Ocirc;': u'\u00D4', '&Otilde;': u'\u00D5', '&Ouml;': u'\u00D6', '&times;': u'\u00D7',
                       '&Oslash;': u'\u00D8', '&Ugrave;': u'\u00D9', '&Uacute;': u'\u00DA', '&Ucirc;': u'\u00DB',
                       '&Uuml;': u'\u00DC', '&Yacute;': u'\u00DD', '&THORN;': u'\u00DE', '&szlig;': u'\u00DF',
                       '&agrave;': u'\u00E0', '&aacute;': u'\u00E1', '&acirc;': u'\u00E2', '&atilde;': u'\u00E3',
                       '&auml;': u'\u00E4', '&aring;': u'\u00E5', '&aelig;': u'\u00E6', '&ccedil;': u'\u00E7',
                       '&egrave;': u'\u00E8', '&eacute;': u'\u00E9', '&ecirc;': u'\u00EA', '&euml;': u'\u00EB',
                       '&igrave;': u'\u00EC', '&iacute;': u'\u00ED', '&icirc;': u'\u00EE', '&iuml;': u'\u00EF',
                       '&eth;': u'\u00F0', '&ntilde;': u'\u00F1', '&ograve;': u'\u00F2', '&oacute;': u'\u00F3',
                       '&ocirc;': u'\u00F4', '&otilde;': u'\u00F5', '&ouml;': u'\u00F6', '&divide;': u'\u00F7',
                       '&oslash;': u'\u00F8', '&ugrave;': u'\u00F9', '&uacute;': u'\u00FA', '&ucirc;': u'\u00FB',
                       '&uuml;': u'\u00FC', '&yacute;': u'\u00FD', '&thorn;': u'\u00FE', '&yuml;': u'\u00FF',
                       '&fnof;': u'\u0192', '&Alpha;': u'\u0391', '&Beta;': u'\u0392', '&Gamma;': u'\u0393',
                       '&Delta;': u'\u0394', '&Epsilon;': u'\u0395', '&Zeta;': u'\u0396', '&Eta;': u'\u0397',
                       '&Theta;': u'\u0398', '&Iota;': u'\u0399', '&Kappa;': u'\u039A', '&Lambda;': u'\u039B',
                       '&Mu;': u'\u039C', '&Nu;': u'\u039D', '&Xi;': u'\u039E', '&Omicron;': u'\u039F',
                       '&Pi;': u'\u03A0', '&Rho;': u'\u03A1', '&Sigma;': u'\u03A3', '&Tau;': u'\u03A4',
                       '&Upsilon;': u'\u03A5', '&Phi;': u'\u03A6', '&Chi;': u'\u03A7', '&Psi;': u'\u03A8',
                       '&Omega;': u'\u03A9', '&alpha;': u'\u03B1', '&beta;': u'\u03B2', '&gamma;': u'\u03B3',
                       '&delta;': u'\u03B4', '&epsilon;': u'\u03B5', '&zeta;': u'\u03B6', '&eta;': u'\u03B7',
                       '&theta;': u'\u03B8', '&iota;': u'\u03B9', '&kappa;': u'\u03BA', '&lambda;': u'\u03BB',
                       '&mu;': u'\u03BC', '&nu;': u'\u03BD', '&xi;': u'\u03BE', '&omicron;': u'\u03BF',
                       '&pi;': u'\u03C0', '&rho;': u'\u03C1', '&sigmaf;': u'\u03C2', '&sigma;': u'\u03C3',
                       '&tau;': u'\u03C4', '&upsilon;': u'\u03C5', '&phi;': u'\u03C6', '&chi;': u'\u03C7',
                       '&psi;': u'\u03C8', '&omega;': u'\u03C9', '&thetasym;': u'\u03D1', '&upsih;': u'\u03D2',
                       '&piv;': u'\u03D6', '&bull;': u'\u2022', '&hellip;': u'\u2026', '&prime;': u'\u2032',
                       '&Prime;': u'\u2033', '&oline;': u'\u203E', '&frasl;': u'\u2044', '&weierp;': u'\u2118',
                       '&image;': u'\u2111', '&real;': u'\u211C', '&trade;': u'\u2122', '&alefsym;': u'\u2135',
                       '&larr;': u'\u2190', '&uarr;': u'\u2191', '&rarr;': u'\u2192', '&darr;': u'\u2193',
                       '&harr;': u'\u2194', '&crarr;': u'\u21B5', '&lArr;': u'\u21D0', '&uArr;': u'\u21D1',
                       '&rArr;': u'\u21D2', '&dArr;': u'\u21D3', '&hArr;': u'\u21D4', '&forall;': u'\u2200',
                       '&part;': u'\u2202', '&exist;': u'\u2203', '&empty;': u'\u2205', '&nabla;': u'\u2207',
                       '&isin;': u'\u2208', '&notin;': u'\u2209', '&ni;': u'\u220B', '&prod;': u'\u220F',
                       '&sum;': u'\u2211', '&minus;': u'\u2212', '&lowast;': u'\u2217', '&radic;': u'\u221A',
                       '&prop;': u'\u221D', '&infin;': u'\u221E', '&ang;': u'\u2220', '&and;': u'\u2227',
                       '&or;': u'\u2228', '&cap;': u'\u2229', '&cup;': u'\u222A', '&int;': u'\u222B',
                       '&there4;': u'\u2234', '&sim;': u'\u223C', '&cong;': u'\u2245', '&asymp;': u'\u2248',
                       '&ne;': u'\u2260', '&equiv;': u'\u2261', '&le;': u'\u2264', '&ge;': u'\u2265',
                       '&sub;': u'\u2282', '&sup;': u'\u2283', '&nsub;': u'\u2284', '&sube;': u'\u2286',
                       '&supe;': u'\u2287', '&oplus;': u'\u2295', '&otimes;': u'\u2297', '&perp;': u'\u22A5',
                       '&sdot;': u'\u22C5', '&lceil;': u'\u2308', '&rceil;': u'\u2309', '&lfloor;': u'\u230A',
                       '&rfloor;': u'\u230B', '&lang;': u'\u2329', '&rang;': u'\u232A', '&loz;': u'\u25CA',
                       '&spades;': u'\u2660', '&clubs;': u'\u2663', '&hearts;': u'\u2665', '&diams;': u'\u2666',
                       '&quot;': u'\u0022', '&lt;': u'\u003C', '&gt;': u'\u003E', '&OElig;': u'\u0152',
                       '&oelig;': u'\u0153', '&Scaron;': u'\u0160', '&scaron;': u'\u0161', '&Yuml;': u'\u0178',
                       '&circ;': u'\u02C6', '&tilde;': u'\u02DC', '&ensp;': u'\u2002', '&emsp;': u'\u2003',
                       '&thinsp;': u'\u2009', '&zwnj;': u'\u200C', '&zwj;': u'\u200D', '&lrm;': u'\u200E',
                       '&rlm;': u'\u200F', '&ndash;': u'\u2013', '&mdash;': u'\u2014', '&lsquo;': u'\u2018',
                       '&rsquo;': u'\u2019', '&sbquo;': u'\u201A', '&ldquo;': u'\u201C', '&rdquo;': u'\u201D',
                       '&bdquo;': u'\u201E', '&dagger;': u'\u2020', '&Dagger;': u'\u2021', '&permil;': u'\u2030',
                       '&lsaquo;': u'\u2039', '&rsaquo;': u'\u203A', '&euro;': u'\u20AC'}

    def __init__(self, prefix='http://en.wikipedia.org/wiki/', drop_lists=False, drop_enumerations=False,
                 drop_tables=False, drop_indents=False, keep_anchors=False):
        self.prefix = prefix
        self.drop_lists = drop_lists
        self.drop_enumerations = drop_enumerations
        self.drop_tables = drop_tables
        self.drop_indents = drop_indents
        self.keep_anchors = keep_anchors

        # Riconosce i commenti HTML
        self.__comment_pattern = re.compile(r'<!--.*?-->', re.DOTALL)

        # Riconosce i tag HTML spazzatura
        self.__garbage_tag_patterns = list()
        for tag in self.__class__.__garbage_tags:
            pattern = re.compile(r'<\s*%s(\s*| [^/]+?)>.*?<\s*/\s*%s\s*>' % (tag, tag), re.DOTALL | re.IGNORECASE)
            self.__garbage_tag_patterns.append(pattern)

        # Riconosce i tag HTML contenitori
        self.__wrapper_tag_patterns = list()
        for tag in self.__class__.__wrapper_tags:
            left_pattern = re.compile(r'<\s*%s(\s*| [^/]+?)>' % tag, re.DOTALL | re.IGNORECASE)
            right_pattern = re.compile(r'<\s*/\s*%s\s*>' % tag, re.DOTALL | re.IGNORECASE)
            self.__wrapper_tag_patterns.append((left_pattern, right_pattern))

        # Riconosce i tag HTML singoli
        self.__single_tag_patterns = list()
        for tag in self.__class__.__single_tags:
            good_pattern = re.compile(r'<\s*%s(\s*| .+?)/\s*>' % tag, re.DOTALL | re.IGNORECASE)
            bad_pattern = re.compile(r'<\s*(/|\\)?\s*%s(\s*| [^/]+?)\\?\s*>' % tag, re.DOTALL | re.IGNORECASE)
            self.__single_tag_patterns.append((good_pattern, bad_pattern))

        # Riconosce i tag HTML segnaposto
        self.__placeholder_tag_patterns = list()
        for tag in self.__class__.__placeholder_tags:
            pattern = re.compile(r'<\s*%s(\s*| [^/]+?)>.*?<\s*/\s*%s\s*>' % (tag, tag), re.DOTALL | re.IGNORECASE)
            self.__placeholder_tag_patterns.append((pattern, self.__class__.__placeholder_tags[tag]))

        # Riconosce le tabelle e i template
        self.__table_pattern = re.compile(r'\{[^{]*?\}', re.DOTALL)

        # Riconosce i wikilink
        good_wikilink_pattern = re.compile(r'\[\[[^[]*?\]\]', re.DOTALL)
        bad_left_wikilink_pattern = re.compile(r'\[[^[]*?\]\]', re.DOTALL)
        bad_right_wikilink_pattern = re.compile(r'\[\[[^[]*?\]', re.DOTALL)
        self.__wikilink_pattern = (good_wikilink_pattern, bad_left_wikilink_pattern, bad_right_wikilink_pattern)

        # Riconosce i link HTTP
        self.__http_link_pattern = re.compile(r'\[http.*?\]', re.DOTALL | re.IGNORECASE)

        # Riconosce gli apostrofi che precedono grassetto e corsivo
        apostrophe_bold_pattern = re.compile(r"\w'('''[^\s'][^']*?[^\s']''')[^']", re.DOTALL)
        apostrophe_italic_pattern = re.compile(r"\w'(''[^\s'][^']*?[^\s']'')[^']", re.DOTALL)
        self.__apostrophe_pattern = (apostrophe_bold_pattern, apostrophe_italic_pattern)

        # Riconosce le entita' numeriche
        self.__numeric_entity_pattern = re.compile(r'&#\d+?;')

        # Riconosce gli spazi multipli
        self.__multi_space_pattern = re.compile(r' {2,}')

        # Riconosce i punti multipli
        self.__multi_dot_pattern = re.compile(r'\.{4,}')

    # ------------------------------------------------------------------------------


    def process_page(self, page):
        wiki_document = self.extract_raw_document(page, quote=False)
        if wiki_document is None:
            return

        wiki_document = self.process_document(wiki_document)
        if wiki_document is None:
            return

        return (wiki_document.url, wiki_document.__str__().encode('utf-8'))

    def extract_raw_document(self, page, quote=False):
        wiki_document = AnnotatedWikiDocument()
        for line in page:
            if not line:
                continue
            # Identificatore della pagina (nodo XML)
            if not wiki_document.id and line.startswith('<id>') and line.endswith('</id>'):
                wiki_document.id = int(line[4:-5])
                continue
            # Titolo della pagina (nodo XML)
            elif not wiki_document.url and line.startswith('<title>') and line.endswith('</title>'):
                title = line[7:-8].replace('&amp;', '&')
                if self.reject_page(title):
                    # print "REJECT", title
                    return None
                wiki_document.title = title
                wiki_document.url = get_wiki_document_url(title, self.prefix, quote=quote)

                wiki_document.text = '++%s++' % title

                continue
            # Inizio del testo della pagina (nodo XML)
            elif line.startswith('<text'):
                if line.endswith('</text>'):
                    # Redirect page
                    return None
                line = line[27:]
                if not line:
                    continue
            # Fine del testo della pagina (nodo XML)
            elif line.endswith('</text>'):
                line = line[:-7]
                if not line:
                    continue
            # Informazione superflua (nodo XML)
            elif line[0] == '<':
                continue
            # Titolo di paragafo (testo della pagina)
            elif line[0] == '=':
                line = '==%s==' % line.strip('= ')

            wiki_document.text += '\n%s' % line

        return wiki_document

    def reject_page(self, title):
        for reject_prefix in self.__garbage_page_prefixes:
            if title.startswith(reject_prefix):
                return True
        return False

    def process_document(self, wiki_document):
        wiki_document = self.__clean(wiki_document)
        wiki_document = self.__compact(wiki_document)

        if wiki_document is None:
            return None

        # This int is used to keep track of the difference between the original article with <a href="..">
        # links and the new article that only contains the label of the link.
        deltaStringLength = 0

        # As a first step, find all links in the article, save their positions into the annotations object
        ms = re.finditer('<a href="([^"]+)">([^>]+)</a>', wiki_document.text)

        annotations = []
        for m in ms:
            if urllib.parse.quote("#") not in m.group(1) or self.keep_anchors:
                annotations.append(
                    {"uri": m.group(1), "surface_form": m.group(2), "offset": m.start() - deltaStringLength})

            deltaStringLength += len(m.group(0)) - len(m.group(2))

        # As a second step, replace all links in the article by their label
        wiki_document.text = re.sub('<a href="([^"]+)">([^>]+)</a>', lambda m: m.group(2), wiki_document.text)

        # Create a new AnnotatedWikiDocument
        wiki_document.annotations = annotations

        return wiki_document

    def __clean(self, wiki_document):
        # Rende maggiormente riconoscibili i tag
        wiki_document.text = wiki_document.text.replace('&lt;', '<').replace('&gt;', '>')
        wiki_document.text = wiki_document.text.replace('<<', u'��').replace('>>', u'��')

        # Elimina i commenti HTML
        wiki_document.text = self.__comment_pattern.sub('', wiki_document.text)

        # Elimina i tag HTML spazzatura
        for pattern in self.__garbage_tag_patterns:
            wiki_document.text = pattern.sub('', wiki_document.text)

        # Elimina i tag HTML contenitori
        for left_pattern, right_pattern in self.__wrapper_tag_patterns:
            wiki_document.text = left_pattern.sub('', wiki_document.text)
            wiki_document.text = right_pattern.sub('', wiki_document.text)

        # Elimina i tag HTML singoli
        for good_pattern, bad_pattern in self.__single_tag_patterns:
            wiki_document.text = good_pattern.sub('', wiki_document.text)
            wiki_document.text = bad_pattern.sub('', wiki_document.text)

        # Elimina i tag HTML segnaposto
        for pattern, placeholder in self.__placeholder_tag_patterns:
            index = 1
            for match in pattern.finditer(wiki_document.text):
                wiki_document.text = wiki_document.text.replace(match.group(), '%s_%d' % (placeholder, index))
                index += 1

        # Elimina le tabelle e i template
        wiki_document.text = wiki_document.text.replace('{{end box}}', '}')
        wiki_document.text = wiki_document.text.replace('{{', '{').replace('}}', '}')
        wiki_document.text = wiki_document.text.replace('{|', '{').replace('|}', '}')
        wiki_document.text = self.__table_pattern.sub('', wiki_document.text)
        wiki_document.text = self.__table_pattern.sub('', wiki_document.text)
        wiki_document.text = self.__table_pattern.sub('', wiki_document.text)

        # Gestisce i wikilink (ben formattati; due livelli di annidamento)
        good_wikilink_pattern = self.__wikilink_pattern[0]
        for match in good_wikilink_pattern.finditer(wiki_document.text):
            wikilink = match.group()
            document_title, link_text = self.__handle_wikilink(wikilink[2:-2])
            wiki_document.text = wiki_document.text.replace(wikilink, self.__get_anchor_tag(document_title, link_text))
        for match in good_wikilink_pattern.finditer(wiki_document.text):
            wikilink = match.group()
            wiki_document.text = wiki_document.text.replace(wikilink, self.__handle_wikilink(wikilink[2:-2])[1])

        # Gestisce i wikilink (mal formattati)
        bad_left_wikilink_pattern = self.__wikilink_pattern[1]
        for match in bad_left_wikilink_pattern.finditer(wiki_document.text):
            wikilink = match.group()
            document_title, link_text = self.__handle_wikilink(wikilink[1:-2])
            wiki_document.text = wiki_document.text.replace(wikilink, self.__get_anchor_tag(document_title, link_text))

        bad_right_wikilink_pattern = self.__wikilink_pattern[2]
        for match in bad_right_wikilink_pattern.finditer(wiki_document.text):
            wikilink = match.group()
            document_title, link_text = self.__handle_wikilink(wikilink[2:-1])
            wiki_document.text = wiki_document.text.replace(wikilink, self.__get_anchor_tag(document_title, link_text))
        wiki_document.text = wiki_document.text.replace('[[', '').replace(']]', '')

        # Elimina i link HTTP
        wiki_document.text = self.__http_link_pattern.sub('', wiki_document.text).replace('[]', '')

        # Gestisce i grassetti e i corsivi
        apostrophe_bold_pattern = self.__apostrophe_pattern[0]
        for match in apostrophe_bold_pattern.finditer(wiki_document.text):
            bold_text = match.group(1)
            wiki_document.text = wiki_document.text.replace(bold_text, bold_text[3:-3])
        apostrophe_italic_pattern = self.__apostrophe_pattern[1]
        for match in apostrophe_italic_pattern.finditer(wiki_document.text):
            italic_text = match.group(1)
            wiki_document.text = wiki_document.text.replace(italic_text, '&quot;%s&quot;' % italic_text[2:-2])
        wiki_document.text = wiki_document.text.replace("'''", '').replace("''", '&quot;')

        # Gestisce i caratteri speciali
        wiki_document.text = wiki_document.text.replace('&amp;', '&').replace('&quot;&quot;', '&quot;')
        for entity in self.__class__.__char_entities:
            wiki_document.text = wiki_document.text.replace(entity, self.__class__.__char_entities[entity])

        # Gestisce i caratteri speciali
        for match in self.__numeric_entity_pattern.finditer(wiki_document.text):
            entity = match.group()
            wiki_document.text = wiki_document.text.replace(entity, self.__handle_unicode(entity))

        # Gestisce alcune imperfezioni del testo
        wiki_document.text = wiki_document.text.replace('\t', ' ')
        wiki_document.text = self.__multi_space_pattern.sub(' ', wiki_document.text)
        wiki_document.text = self.__multi_dot_pattern.sub('...', wiki_document.text)
        wiki_document.text = wiki_document.text.replace(' ,', ',').replace(' .', '.')
        wiki_document.text = wiki_document.text.replace(' :', ':').replace(' ;', ';')
        wiki_document.text = wiki_document.text.replace(',,', ',').replace(',.', '.')
        wiki_document.text = wiki_document.text.replace('( ', '(').replace(' )', ')')
        wiki_document.text = wiki_document.text.replace('[ ', '[').replace(' ]', ']')
        wiki_document.text = wiki_document.text.replace(u'�� ', u'��').replace(u' ��', u'��')

        return wiki_document

    def __compact(self, wiki_document):
        page = list()
        paragraph = list()

        for line in wiki_document.text.split('\n'):
            line = line.strip()
            if not line:
                continue

            # Gestisce il titolo della pagina
            if line.startswith('++'):
                title = line[2:-2]
                if title and title[-1] not in '!?':
                    title = '%s.' % title
                page = [title]
            # Gestisce i titoli dei paragrafi
            elif line.startswith('=='):
                if len(paragraph) > 1:
                    page.extend(paragraph)
                title = line[2:-2]
                if title and title[-1] not in '!?':
                    title = '%s.' % title
                paragraph = [title]

            elif line[:9].lower() == "#redirect":
                return None
            # The following misses a lot; exclude:

            # Elimina gli elenchi puntati e numerati
            # elif line[-1] == ':' or line[0] in '*#:;':
            #     continue
            elif line[0] == '*':
                if self.drop_lists:
                    continue
                else:
                    line = line.strip("* ")
            elif line[0] == '#':
                if self.drop_enumerations:
                    continue
                else:
                    line = line.strip("# ")
            elif line[0] == ':':
                if self.drop_indents:
                    continue
                else:
                    line = line.strip(": ")
            elif line[0] == ";":
                line = line.strip("; ")

            # Elimina i resti delle tabelle
            elif line[0] in '{|':
                if self.drop_tables:
                    continue
                else:
                    line = line.strip("{| ")

            # elif line[0] in '{|' or line[-1] in '}':
            #     continue

            # Elimina le righe non significative
            elif line.strip('.- ') == '':
                continue

            # elif (line[0] == '(' and line[-1] == ')'):
            #     continue

            # Elimina le righe con un basso numero di token
            elif not '_' in line and len(line.split()) < 6:
                continue
            # Gestisce il testo della pagina
            elif len(paragraph) == 0:
                page.append(line)
            # Gestisce il testo dei paragrafi
            else:
                paragraph.append(line)

        if len(paragraph) > 1:
            page.extend(paragraph)
        elif len(page) == 1:
            return None

        wiki_document.text = '\n'.join(page)
        return wiki_document

    def __handle_wikilink(self, wikilink):
        if wikilink.startswith(":"):
            # remove redundant preceding ":"
            wikilink = wikilink[1:]

        # allow some prefixes
        for p in self.__allowed_prefixes:
            if wikilink.strip().lower().startswith(p):
                wikilink = wikilink[len(p):]
                break

        # filter files, categories, etc, ...
        for p in self.__garbage_link_prefixes + self.__project_namespaces:
            wclean = wikilink.strip().lower()
            if wclean.startswith(p + ":"):
                # ignore all garbage links
                # ignore all "unknown"/non-english versions of garbage links by generic "wiki" prefix
                return "", ""

        # only consider article title, not link text, when checking for cross language links
        parts = wikilink.split("|")
        tokens = parts[0].split(":")
        if len(tokens) > 1 and len(tokens[0]) <= 3 and tokens[0].islower() and tokens[0].isalpha():
            # heuristic to ignore all cross language links
            return "", ""

        # split into  article title and link text
        parts = wikilink.split("|")

        # tokens = parts[0].split(":")
        # if len(tokens) > 1:
        # 	print wikilink

        if len(parts) == 1:
            article_title = parts[0]
            link_text = parts[0]
        elif len(parts) == 2:
            article_title, link_text = parts
        else:
            # print "ERROR: ", "  ".join(parts), "\t\t", wikilink
            article_title = ""
            link_text = ""
        return article_title, link_text

    def __get_anchor_tag(self, document_title, link_text):
        if not link_text:
            return ''
        if not document_title:
            return link_text
        return u'<a href="%s">%s</a>' % (get_wiki_document_url(document_title, '', quote=False), link_text)

    def __handle_unicode(self, entity):
        numeric_code = int(entity[2:-1])
        if numeric_code >= 0x10000: return ''
        return chr(numeric_code)


# ------------------------------------------------------------------------------


class OutputSplitter:
    def __init__(self, compress, max_file_size, path_name):
        self.__dir_index = 0
        self.__file_index = -1
        self.__cur_file_size = 0
        self.__line_number = 0
        self.__compress = compress
        self.__max_file_size = max_file_size
        self.__path_name = path_name
        self.__out_file, self.__current_filepath = self.__open_next_file()
        self.__index_file = io.open(os.path.join(path_name, "index.tsv"), "w", encoding="utf-8")

    #def write(self, (url, text)):
    def write(self, x):
        url = x[0]
        text =x[1]
        # print("write:", url)
        # print("write:", text)
        text_len = len(text)
        if self.__cur_file_size + text_len / 2 > self.__max_file_size:
            self.__close_cur_file()
            self.__out_file, self.__current_filepath = self.__open_next_file()
            self.__line_number = 0
            self.__cur_file_size = 0
        self.__out_file.write(text)
        self.__cur_file_size += text_len
        self.__add_to_index(url)
        self.__line_number += 1

    def close(self):
        self.__close_cur_file()
        self.__index_file.close()

    def __open_next_file(self):
        self.__file_index += 1
        if self.__file_index == 100:
            self.__dir_index += 1
            self.__file_index = 0
        dir_name = self.__get_dir_name()
        if not os.path.isdir(dir_name):
            os.makedirs(dir_name)
            print("Open next dir: {}".format(dir_name))

        filepath = os.path.join(dir_name, self.__get_file_name())
        if self.__compress:
            filepath = filepath + '.bz2'
            return bz2.BZ2File(filepath, 'w'), filepath
        else:
            return open(filepath, 'w'), filepath

    def __close_cur_file(self):
        self.__out_file.close()

    def __get_dir_name(self):
        char1 = self.__dir_index % 26
        char2 = self.__dir_index // 26 % 26
        return os.path.join(self.__path_name, '%c%c' % (ord('A') + char2, ord('A') + char1))

    def __get_file_name(self):
        return 'wiki%02d' % self.__file_index

    def __add_to_index(self, url):
        rel_filepath = os.path.relpath(self.__current_filepath, self.__path_name)
        self.__index_file.write(url + u"\t" + rel_filepath + u"\t" + str(self.__line_number) + u"\n")


### USER INTERFACE ############################################################

def show_help():
    print() >> sys.stdout, __doc__,


def show_usage(output_file, script_name):
    print(output_file, 'Usage: python %s [options] < your_wikipedia_dump.xml' % script_name)


def show_suggestion(output_file, script_name):
    print(output_file, 'Try \'%s --help\' for more information.' % script_name)


def show_size_error(script_name, file_size):
    print(sys.stderr, '%s: %s: Insufficient or invalid number of bytes' % (script_name, file_size))


def show_file_error(script_name, file_name):
    print(sys.stderr, '%s: %s: No such file or directory' % (script_name, file_name))


def process_file(input_file, output_splitter, number_of_workers):
    print("Start processing file ...")
    # Set up pool of worker processes
    pool = Pool(processes=number_of_workers)

    pages = []
    page = []
    page_counter = 0
    for line in input_file:
        line = line.strip()
        if line == '<page>':
            page = []
        elif line == '</page>':
            pages.append(page)
            page_counter += 1

            if len(pages) % 10000 == 0:
                print("Process page ", page_counter)

            if len(pages) >= 10000:
                for x in pool.map(process_page, pages):
                    if x is not None:
                        output_splitter.write(x)
                pages = []
        else:
            page.append(line)

    if len(pages) > 0:
        for x in pool.map(process_page, pages):
            if x is not None:
                output_splitter.write(x)


def process_page(page):
    return wiki_extractor.process_page(page)


def main():
    script_name = os.path.basename(sys.argv[0])

    try:
        long_opts = ['help', 'usage', 'compress', 'bytes=', 'output=', 'keep-anchors', "workers=", "prefix="]
        opts, args = getopt.gnu_getopt(sys.argv[1:], 'kcb:o:w:p:', long_opts)
    except getopt.GetoptError:
        show_usage(sys.stderr, script_name)
        show_suggestion(sys.stderr, script_name)
        sys.exit(1)

    compress = False
    file_size = 500 * 1024
    output_dir = '.'
    number_of_workers = 4
    keep_anchors = False
    prefix = default_prefix

    for opt, arg in opts:
        if opt == '--help':
            show_help()
            sys.exit()
        elif opt == '--usage':
            show_usage(sys.stdout, script_name)
            sys.exit()
        elif opt in ('-k', '--keep-anchors'):
            keep_anchors = True
        elif opt in ('-c', '--compress'):
            compress = True
        elif opt in ('-b', '--bytes'):
            try:
                if arg[-1] in 'kK':
                    file_size = int(arg[:-1]) * 1024
                elif arg[-1] in 'mM':
                    file_size = int(arg[:-1]) * 1024 * 1024
                else:
                    file_size = int(arg)
                if file_size < 200 * 1024: raise ValueError()
            except ValueError:
                show_size_error(script_name, arg)
                sys.exit(2)
        elif opt in ('-o', '--output'):
            if os.path.isdir(arg):
                output_dir = arg
            else:
                show_file_error(script_name, arg)
                sys.exit(3)
        elif opt in ("-w", "--workers"):
            number_of_workers = int(arg)
        elif opt in ("-p", "--prefix"):
            prefix = arg
            if prefix[-1] != "/":
                print("Prefix '{}' does not end on '/'".format(prefix))
                sys.exit(1)

    if len(args) > 0:
        show_usage(sys.stderr, script_name)
        show_suggestion(sys.stderr, script_name)
        sys.exit(4)

    output_splitter = OutputSplitter(compress, file_size, output_dir)
    wiki_extractor.keep_anchors = keep_anchors
    wiki_extractor.prefix = prefix
    process_file(sys.stdin, output_splitter, number_of_workers)

    output_splitter.close()


if __name__ == '__main__':
    # prefix = 'http://{}.wikipedia.org/wiki/'
    default_prefix = "http://en.wikipedia.org/wiki/"

    wiki_extractor = AnnotatedWikiExtractor(prefix=default_prefix, drop_lists=False, drop_enumerations=False,
                                            drop_tables=False, drop_indents=False, keep_anchors=False)
    main()
