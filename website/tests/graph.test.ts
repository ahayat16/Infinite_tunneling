import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import {
  admissionAncestors,
  graphSlice,
  graphDot,
  resolveName,
} from '../lib/model.ts';
import type { Declaration } from '../lib/model.ts';

const data: Declaration[] = JSON.parse(
  readFileSync(new URL('../public/data/index.json', import.meta.url), 'utf8'),
);
const rows = new Map(data.map((row) => [row.name, row]));
const admitted = data
  .filter((row) => row.status === 'admitted')
  .map((row) => row.name);
const ancestors = admissionAncestors(data, admitted);

await test('the main theorem has exactly the three classical admissions in its ancestry', () => {
  assert.deepEqual(
    new Set(ancestors.get('InfiniteZero.thm_main')),
    new Set(admitted),
  );
  assert.equal(admitted.length, 3);
});

await test('every graph arrow is a real dependency and endpoints remain visible', () => {
  const graph = graphSlice(
    rows,
    'InfiniteZero.thm_main',
    6,
    false,
    ancestors,
    45,
  );
  const visible = new Set(graph.nodes.map((n) => n.name));
  assert.equal(graph.nodes.length, 45);
  assert.ok(graph.total > 45);
  for (const [a, b] of graph.edges) {
    assert.ok(rows.get(a)!.dependencies.includes(b));
    assert.ok(visible.has(a) && visible.has(b));
  }
  assert.ok(
    graph.nodes.every((n) => Number.isFinite(n.x) && n.x >= 0 && n.y >= 0),
  );
});

await test('admission filter keeps exactly paths that can reach a registered admission', () => {
  const graph = graphSlice(rows, 'InfiniteZero.thm_main', 10, true, ancestors);
  assert.ok(graph.nodes.length > 4);
  assert.ok(graph.nodes.every((n) => ancestors.has(n.name)));
  for (const name of admitted)
    assert.ok(graph.nodes.some((n) => n.name === name));
});

await test('cycles terminate and missing roots produce an empty graph', () => {
  const loop = new Map([
    [
      'a',
      {
        name: 'a',
        kind: 'def',
        file: 'x',
        line: 1,
        status: 'proved',
        dependencies: ['b'],
      },
    ],
    [
      'b',
      {
        name: 'b',
        kind: 'def',
        file: 'x',
        line: 2,
        status: 'proved',
        dependencies: ['a'],
      },
    ],
  ]);
  assert.equal(graphSlice(loop, 'a', 10, false, new Map()).nodes.length, 2);
  assert.equal(
    graphSlice(loop, 'missing', 3, false, new Map()).nodes.length,
    0,
  );
});

await test('structure fields link to the owning declaration and DOT preserves direction', () => {
  assert.equal(
    resolveName('InfiniteZero.MainConclusion.spectral_zeros', rows),
    'InfiniteZero.MainConclusion',
  );
  const graph = graphSlice(rows, 'InfiniteZero.thm_main', 1, false, ancestors);
  const dot = graphDot(graph.nodes, graph.edges);
  assert.ok(
    dot.includes(
      '"InfiniteZero.thm_main" -> "InfiniteZero.elementaryPotential_main"',
    ),
  );
});
