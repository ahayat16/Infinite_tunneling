#!/usr/bin/env node
import { readFile, readdir, mkdir, writeFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { build } from 'vite';
import react from '@vitejs/plugin-react';
import tailwindcss from '@tailwindcss/postcss';

const site = fileURLToPath(new URL('..', import.meta.url));
const output = path.join(site, 'outputs/share');
await mkdir(output, { recursive: true });
execFileSync('python3', ['scripts/generate_data.py'], { cwd: site, stdio: 'inherit' });

const result = await build({
  configFile: false,
  root: site,
  publicDir: false,
  resolve: { alias: { '@': site } },
  plugins: [react()],
  css: { postcss: { plugins: [tailwindcss()] } },
  build: {
    write: false,
    minify: true,
    cssMinify: true,
    lib: { entry: path.join(site, 'scripts/offline-entry.tsx'), name: 'InfiniteZero', formats: ['iife'] },
  },
  define: { 'process.env.NODE_ENV': JSON.stringify('production') },
});
const outputs = (Array.isArray(result) ? result : [result]).flatMap((item) => item.output);
const javascript = outputs.filter((item) => item.type === 'chunk');
const styles = outputs.filter((item) => item.type === 'asset' && item.fileName.endsWith('.css'));
if (javascript.length !== 1 || styles.length !== 1) throw Error('Expected one script and one stylesheet.');
const css = String(styles[0].source);
if (/url\((?!["']?data:)/.test(css)) throw Error('The offline stylesheet has an external asset.');

async function walk(dir) {
  const entries = await readdir(dir, { withFileTypes: true });
  return (await Promise.all(entries.map((entry) => entry.isDirectory()
    ? walk(path.join(dir, entry.name)) : [path.join(dir, entry.name)]))).flat();
}

const publicDir = path.join(site, 'public');
const files = {};
for (const folder of ['data', 'sources', 'notes']) {
  for (const file of (await walk(path.join(publicDir, folder))).sort()) {
    const key = path.relative(publicDir, file).split(path.sep).join('/');
    files[key] = {
      text: await readFile(file, 'utf8'),
      type: file.endsWith('.json') ? 'application/json' : 'text/plain;charset=utf-8',
    };
  }
}
const json = JSON.stringify(files).replaceAll('<', '\\u003c');
const script = javascript[0].code.replace(/<\/script/gi, '<\\/script');
const html = `<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Infinite Zero — Manuscript &amp; Lean</title>
<style>${css}</style></head><body>
<div id="root"></div><noscript>Enable JavaScript to read the formalization and explore its dependencies.</noscript>
<script type="application/json" id="offline-files">${json}</script>
<script>${script}</script></body></html>
`;
await writeFile(path.join(output, 'infinite-zero.html'), html);

// Package the standalone file and the existing static export separately.
execFileSync('python3', ['-c', `
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
site = Path(${JSON.stringify(site)})
out = site / 'outputs/share'
with ZipFile(out / 'infinite-zero-offline.zip', 'w', ZIP_DEFLATED) as z:
    z.write(out / 'infinite-zero.html', 'infinite-zero.html')
    z.writestr('README.txt', 'Infinite Zero — Manuscript and Lean\\n\\nOpen infinite-zero.html in a browser. The reader, sources and dependency graph work offline. Links to external references require an internet connection.\\n')
index = site / 'dist/client/index.html'
if not index.is_file():
    raise SystemExit('Run npm run build before exporting the static-site archive.')
with ZipFile(out / 'infinite-zero-site.zip', 'w', ZIP_DEFLATED) as z:
    for p in sorted((site / 'dist/client').rglob('*')):
        if p.is_file():
            z.write(p, 'infinite-zero-site/' + p.relative_to(site / 'dist/client').as_posix())
    z.writestr('README.txt', 'Infinite Zero — Static website\\n\\nPublish the contents of infinite-zero-site/ to a static web host.\\nTo preview locally: python3 -m http.server 4173 --directory infinite-zero-site\\nThen open http://localhost:4173.\\n')
`], { stdio: 'inherit' });
console.log(`Sharing exports written to ${output}`);
