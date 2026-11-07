#!/usr/bin/env node
// Extract the global CHARS sequence from paper.pdf, EXACTLY as the browser UI
// builds it (ui/app.js buildTextLayer): walk every page's text items in reading
// order, append item.str, and append '\n' after any item with hasEOL. Box pieces
// in tree.json are [start,end) offsets into this string.
//
// The PDF is the source of truth; chars.txt is a regenerable cache for headless
// tools (inspect.js) so they don't need pdf.js. Rerun when paper.pdf changes:
//   node tools/extract_chars.js
const pdfjs = require('pdfjs-dist/build/pdf.js');
const fs = require('fs');
const path = require('path');

const ROOT = path.resolve(__dirname, '..');
const PDF = path.join(ROOT, 'paper.pdf');
const OUT = path.join(ROOT, 'chars.txt');

(async () => {
  const data = new Uint8Array(fs.readFileSync(PDF));
  const pdf = await pdfjs.getDocument({ data, useSystemFonts: true }).promise;
  let CHARS = '';
  for (let p = 1; p <= pdf.numPages; p++) {
    const page = await pdf.getPage(p);
    const tc = await page.getTextContent();
    for (const item of tc.items) {
      if (!item.str) continue;
      CHARS += item.str;
      if (item.hasEOL) CHARS += '\n';
    }
  }
  fs.writeFileSync(OUT, CHARS);
  console.log(`wrote ${OUT} (${CHARS.length} chars)`);
})().catch((e) => { console.error(e); process.exit(1); });
