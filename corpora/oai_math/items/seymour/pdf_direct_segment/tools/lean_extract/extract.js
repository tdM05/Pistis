#!/usr/bin/env node
// lean_extract — get the ELABORATED Expr of a Lean declaration as JSON.
//
// The Seymour .lean files live inside a real Lean project (lakefile + built
// Mathlib) at .../Pistis/corpora/oai_math. We can't `import` the OAI modules by
// name (they aren't built to oleans in the search path), so instead we elaborate
// a COPY of the source file by path with a small Expr→JSON metaprogram appended
// (probe.lean.tmpl). The elaborated kernel Expr has all notation unfolded and all
// implicit args explicit — the canonical normal form the FOL aligner consumes.
//
//   node tools/lean_extract/extract.js <declName> [srcFile]
//
// Defaults target SupportedOn in MaxSupportKernel.lean. Prints the JSON tree to
// stdout (also usable as a module: require(...).extract({decl, srcFile})).
import { readFileSync, writeFileSync, mkdtempSync, unlinkSync, rmSync, statSync, mkdirSync } from 'fs';
import { execFileSync } from 'child_process';
import { fileURLToPath } from 'url';
import { tmpdir } from 'os';
import path from 'path';

const here = path.dirname(fileURLToPath(import.meta.url));
// project root = .../Pistis/corpora/oai_math (has the lakefile + .lake/mathlib)
const SEG_DIR = path.resolve(here, '..', '..');                 // pdf_direct_segment/
// pdf_direct_segment → seymour → items → oai_math (the Lean project root)
const LEAN_PROJECT = path.resolve(SEG_DIR, '..', '..', '..');
const PROBE_TMPL = path.join(here, 'probe.lean.tmpl');
const ELAN_BIN = '/u/taddmao/.elan/bin';

// default decl + source file for this item
const DEFAULT_DECL = 'OAI.SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel.SupportedOn';
const DEFAULT_SRC = 'items/seymour/pdf_direct_segment/lean/MaxSupportKernel.lean';

// cache dir: extracted trees keyed by decl, invalidated when the source file's
// mtime changes (so edits to the .lean re-extract, but repeat calls are instant).
const CACHE_DIR = path.join(SEG_DIR, '.lean_cache');

export function extract({ decl = DEFAULT_DECL, srcFile = DEFAULT_SRC, timeoutMs = 300000, noCache = false } = {}) {
  const absSrc = path.isAbsolute(srcFile) ? srcFile : path.join(LEAN_PROJECT, srcFile);
  const cacheKey = decl.replace(/[^\w.]/g, '_') + '.json';
  const cacheFile = path.join(CACHE_DIR, cacheKey);
  let srcMtime = 0; try { srcMtime = statSync(absSrc).mtimeMs; } catch (_) {}
  if (!noCache) {
    try { const c = JSON.parse(readFileSync(cacheFile, 'utf8'));
      if (c.srcMtime === srcMtime && c.decl === decl) return c.tree; } catch (_) {}
  }
  const tmpl = readFileSync(PROBE_TMPL, 'utf8').replaceAll('__DECL__', decl);
  // the probe must elaborate in the SAME module context as the source (so the
  // decl is in the environment), so we append it to a copy of the source and
  // place that copy INSIDE the project tree (so `lake env lean` uses the project).
  const dir = mkdtempSync(path.join(tmpdir(), 'leanx-'));
  const probeFile = path.join(LEAN_PROJECT, `__leanx_${process.pid}.lean`);
  try {
    const src = readFileSync(absSrc, 'utf8');
    writeFileSync(probeFile, src + '\n' + tmpl, 'utf8');
    const out = execFileSync('lake', ['env', 'lean', probeFile], {
      cwd: LEAN_PROJECT,
      env: { ...process.env, PATH: ELAN_BIN + ':' + process.env.PATH },
      encoding: 'utf8', timeout: timeoutMs, maxBuffer: 64 * 1024 * 1024,
    });
    const line = out.split('\n').find((l) => l.startsWith('__EXTRACT__'));
    if (!line) {
      const err = out.split('\n').find((l) => l.includes('__EXTRACT_ERR__'));
      throw new Error(err || 'no __EXTRACT__ line in lean output:\n' + out.slice(0, 2000));
    }
    const tree = JSON.parse(line.slice('__EXTRACT__'.length));
    try { mkdirSync(CACHE_DIR, { recursive: true }); writeFileSync(cacheFile, JSON.stringify({ decl, srcMtime, tree })); } catch (_) {}
    return tree;
  } finally {
    try { unlinkSync(probeFile); } catch (_) {}
    try { rmSync(dir, { recursive: true, force: true }); } catch (_) {}
  }
}

// CLI
if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const decl = process.argv[2] || DEFAULT_DECL;
  const srcFile = process.argv[3] || DEFAULT_SRC;
  try {
    const tree = extract({ decl, srcFile });
    console.log(JSON.stringify(tree, null, 2));
  } catch (e) {
    console.error('extract failed:', e.message);
    process.exit(1);
  }
}
