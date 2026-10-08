import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { renderToString } from 'katex';
import { mathMacros, normalizeMath, texForReading } from '../lib/math.ts';

const bootstrap = JSON.parse(
  readFileSync(
    new URL('../content/generated/bootstrap.json', import.meta.url),
    'utf8',
  ),
) as {
  tex: Record<string, { source: string }>;
};

await test('display delimiters stay doubled through conversion', () => {
  assert.equal(normalizeMath('\\[x\\]'), '\n$$\nx\n$$\n');
  assert.equal(normalizeMath('a\\\\[2pt]b'), 'a\\\\[2pt]b');
  assert.equal(
    texForReading('\\begin{equation}x\\end{equation}'),
    '\n$$\nx\n$$\n',
  );
});

await test('all curated TeX formulas parse with the manuscript macros', () => {
  let formulas = 0;
  for (const [label, excerpt] of Object.entries(bootstrap.tex)) {
    const reading = normalizeMath(texForReading(excerpt.source));
    for (const match of reading.matchAll(/\$\$([\s\S]*?)\$\$|\$([^$\n]+)\$/g)) {
      const formula = match[1] ?? match[2];
      assert.doesNotThrow(
        () =>
          renderToString(formula, {
            macros: { ...mathMacros },
            displayMode: !!match[1],
            throwOnError: true,
            strict: false,
          }),
        `${label}: ${formula}`,
      );
      formulas++;
    }
  }
  assert.ok(formulas > 20, `the test must visit the formulas, got ${formulas}`);
});
