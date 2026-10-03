import json
import hashlib
import re
from pathlib import Path
import unittest

from generate_data import ADMISSIONS, ROOT, SITE, extract_declarations, helpers, tex_excerpt


class SourceExtractionTests(unittest.TestCase):
    def test_nested_comments_and_next_documentation(self):
        text = '/-- First doc. -/\ntheorem first : True := by\n  /- nested /- theorem fake : False -/ -/\n  trivial\n\n/-- Second doc. -/\ndef second := 2\n\nend Demo\n'
        records = [{"name": "Demo.first", "line": 2, "source_kind": "theorem"},
                   {"name": "Demo.second", "line": 7, "source_kind": "def"}]
        data = extract_declarations(text, records)
        self.assertEqual(data['Demo.first']['doc'], 'First doc.')
        self.assertNotIn('Second doc', data['Demo.first']['source'])
        self.assertTrue(data['Demo.first']['source'].endswith('trivial'))
        self.assertEqual(data['Demo.second']['source'], 'def second := 2')

    def test_commented_tex_theorem_is_ignored(self):
        text = '% \\begin{theorem}\\label{thm:test}\n% Wrong!\n% \\end{theorem}\n\\begin{theorem}\\label{thm:test}\nRight.\n\\end{theorem}'
        excerpt = tex_excerpt(text, 'thm:test')
        self.assertEqual(excerpt['line'], 4)
        self.assertIn('Right.', excerpt['source'])
        self.assertNotIn('Wrong', excerpt['source'])


class SnapshotTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = json.loads((SITE / 'public/data/index.json').read_text())
        cls.by_name = {r['name']: r for r in cls.rows}
        cls.bootstrap = json.loads((SITE / 'content/generated/bootstrap.json').read_text())

    def test_every_declaration_is_a_verbatim_source_slice(self):
        for path in (SITE / 'public/data/modules').glob('*.json'):
            for name, declaration in json.loads(path.read_text()).items():
                row = self.by_name[name]
                lines = (ROOT / row['file']).read_text().splitlines()
                expected = '\n'.join(lines[declaration['line'] - 1:declaration['endLine']])
                self.assertEqual(declaration['source'], expected, name)
                self.assertEqual(declaration['line'], row['line'], name)
                self.assertFalse(declaration['source'].endswith('end InfiniteZero'), name)

    def test_edges_and_statuses_are_exactly_the_lean_audit(self):
        audit = json.loads((ROOT / 'docs/declarations.json').read_text())
        self.assertEqual(len(audit), len(self.rows))
        for row in audit:
            self.assertEqual(row['dependencies'], self.by_name[row['name']]['dependencies'])
            self.assertEqual(row['status'], self.by_name[row['name']]['status'])

    def test_main_has_exactly_the_four_registered_admissions(self):
        queue, seen = ['InfiniteZero.thm_main'], set()
        while queue:
            name = queue.pop()
            if name in seen: continue
            seen.add(name)
            queue.extend(self.by_name[name]['dependencies'])
        admitted = {name for name in seen if self.by_name[name]['status'] in ('admitted', 'open_target')}
        self.assertEqual(admitted, {a[1] for a in ADMISSIONS})

    def test_curated_links_resolve_to_source_declarations(self):
        curated = self.bootstrap['curated']
        names = [e['name'] for e in curated['entries']]
        names += [name for item in curated['main_items'] for name in item['declarations']]
        names += [name for step in curated['assembly_steps'] for name in step['declarations']]
        names += [name for path in curated['reading_paths'] for name in path['names']]
        for name in names:
            # Generated structure projections are grouped with the source owner.
            while name not in self.by_name and '.' in name:
                name = name.rsplit('.', 1)[0]
            self.assertIn(name, self.by_name)

    def test_tex_excerpts_are_verbatim_and_active(self):
        lines = (ROOT / self.bootstrap['curated']['tex_file']).read_text().splitlines()
        for label, excerpt in self.bootstrap['tex'].items():
            self.assertEqual(excerpt['source'], '\n'.join(lines[excerpt['line'] - 1:excerpt['endLine']]))
            self.assertTrue(any('\\label{' + label + '}' in line and not line.lstrip().startswith('%') for line in excerpt['source'].splitlines()))

    def test_english_review_content_and_translation_sources(self):
        self.assertEqual(self.bootstrap['curated']['language'], 'en')
        self.assertEqual(len(self.bootstrap['curated']['entries']), 30)
        self.assertEqual(len(self.bootstrap['translatedDocuments']), 6)
        manifest = json.loads((SITE / 'content/notes/manifest.json').read_text())
        for filename, meta in manifest.items():
            original = ROOT / meta['source']
            self.assertEqual(hashlib.sha256(original.read_bytes()).hexdigest(), meta['sourceSha256'])
            translated = (SITE / 'content/notes/en' / filename).read_text()
            links = lambda text: sorted(re.findall(r'\]\(([^)]+)\)', text))
            self.assertEqual(links(original.read_text()), links(translated), filename)


if __name__ == '__main__':
    unittest.main()
