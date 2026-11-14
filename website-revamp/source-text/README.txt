CREMONA WEBSITE: PLAIN-TEXT SNAPSHOT

What this is
  The deployed Cremona Pages site stripped to plain text for a revamp.
  HTML tags, scripts, buttons, and navigation chrome are removed.
  Headings, paragraphs, lists, tables, links, and code blocks remain.

Live site
  https://kenneth-cho-infosec.github.io/Cremona/

Files
  index.txt        home page
  docs.txt         language documentation
  examples.txt     runnable examples
  all-pages.txt    the three pages in one file
  style-css.txt    the deployed stylesheet, unchanged
  site-outline.txt page and heading inventory, source hashes, nav
  _extract_pages.py  regenerates these files from downloaded HTML

Provenance
  Fetched 2026-10-20. The live files are byte-identical to the
  site/ directory on the website branch at commit e040a3a.

Refresh
  mkdir -p /tmp/cremona-pages && cd /tmp/cremona-pages
  curl -fsSLO https://kenneth-cho-infosec.github.io/Cremona/index.html
  curl -fsSLO https://kenneth-cho-infosec.github.io/Cremona/docs.html
  curl -fsSLO https://kenneth-cho-infosec.github.io/Cremona/examples.html
  curl -fsSLO https://kenneth-cho-infosec.github.io/Cremona/style.css
  python3 /path/to/source-text/_extract_pages.py . /path/to/source-text
