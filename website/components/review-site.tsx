'use client';
// Scrollable code and SVG regions must remain keyboard-focusable.
/* oxlint-disable jsx-a11y/no-noninteractive-tabindex */
// SVG has no native alternative to its accessible image role.
/* oxlint-disable jsx-a11y/prefer-tag-over-role */

import { useEffect, useMemo, useState } from 'react';
import ReactMarkdown from 'react-markdown';
import remarkMath from 'remark-math';
import remarkGfm from 'remark-gfm';
import rehypeKatex from 'rehype-katex';
import {
  ArrowLeft,
  ArrowRight,
  BookOpen,
  Braces,
  Check,
  ChevronDown,
  Copy,
  Download,
  FileText,
  GitBranch,
  Menu,
  Search,
  ShieldCheck,
  X,
  ZoomIn,
  ZoomOut,
} from 'lucide-react';
import { Button } from '@/components/ui/button';
import { Input } from '@/components/ui/input';
import { Badge } from '@/components/ui/badge';
import { mathMacros, normalizeMath, texForReading } from '@/lib/math';
import {
  admissionAncestors,
  graphDot,
  graphSlice,
  moduleName,
  resolveName,
  route,
  shortName,
  statusLabels,
} from '@/lib/model';
import type { Declaration, Notice, Source } from '@/lib/model';
import type bootstrapData from '@/content/generated/bootstrap.json';

type Bootstrap = typeof bootstrapData;
const MAIN = 'InfiniteZero.thm_main';
const categories = [
  'Statement',
  'Potential',
  'Model',
  'Operator',
  'Proof',
  'Admission',
];
const moduleCache = new Map<string, Record<string, Source>>();
const colors: Record<string, string> = {
  proved: '#28735e',
  definition_or_contract: '#41669c',
  depends_on_admission: '#9a6418',
  admitted: '#b44848',
  open_target: '#8256aa',
};

function Status({ status }: { status: string }) {
  return (
    <Badge variant="outline" className={`status status-${status}`}>
      <span className="status-dot" />
      {statusLabels[status] ?? status}
    </Badge>
  );
}

function download(text: string, name: string, type = 'text/plain') {
  const url = URL.createObjectURL(new Blob([text], { type }));
  const link = document.createElement('a');
  link.href = url;
  link.download = name;
  link.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}

function Markdown({
  text,
  documentName,
}: {
  text: string;
  documentName?: string;
}) {
  const normalized = normalizeMath(text);
  return (
    <ReactMarkdown
      remarkPlugins={[remarkMath, remarkGfm]}
      rehypePlugins={[[rehypeKatex, { strict: false, macros: mathMacros }]]}
      components={{
        a: ({ href, children }) => {
          const target = href?.endsWith('.md')
            ? route('notes', href.split('/').pop()!)
            : href?.startsWith('../InfiniteZero/')
              ? `./sources/${href.slice(3)}`
              : href?.startsWith('http') || href?.startsWith('#')
                ? href
                : documentName
                  ? `./sources/docs/${href}`
                  : href;
          return <a href={target}>{children}</a>;
        },
      }}
    >
      {normalized}
    </ReactMarkdown>
  );
}

function LeanCode({ source, row }: { source: Source; row: Declaration }) {
  const [expanded, setExpanded] = useState(false),
    [copied, setCopied] = useState(false);
  const code =
    !expanded && source.proofOffset
      ? source.source.slice(0, source.proofOffset)
      : source.source;
  const links = useMemo(() => {
    const map = new Map<string, string | null>();
    for (const name of row.dependencies)
      for (const token of [name, shortName(name), name.split('.').pop()!]) {
        map.set(token, map.has(token) && map.get(token) !== name ? null : name);
      }
    return map;
  }, [row]);
  async function copy() {
    try {
      await navigator.clipboard.writeText(source.source);
      setCopied(true);
      setTimeout(() => setCopied(false), 1800);
    } catch {
      download(source.source, `${row.name.split('.').pop()}.lean`);
    }
  }
  return (
    <div className="lean-source">
      <div className="code-toolbar">
        <a href={`./sources/${row.file}`} target="_blank" rel="noreferrer">
          {moduleName(row.file)}.lean · L{source.line}–{source.endLine}
        </a>
        <Button variant="ghost" size="sm" onClick={copy}>
          {copied ? <Check /> : <Copy />}
          {copied ? 'Copied' : 'Copy'}
        </Button>
      </div>
      <pre
        className="code-block"
        tabIndex={0}
        aria-label={`Source Lean : ${shortName(row.name)}`}
      >
        <code>
          {code.split('\n').map((line, index) => (
            <span className="code-line" key={index}>
              <span className="line-number" aria-hidden="true">
                {source.line + index}
              </span>
              <span>
                {line.split(/([\p{L}_][\p{L}\p{N}_'.]*)/u).map((token, i) => {
                  const target = links.get(token);
                  return target ? (
                    <a key={i} href={route('read', target)} title={target}>
                      {token}
                    </a>
                  ) : /^(theorem|lemma|def|structure|where|by|exact|obtain|refine|have|let|fun|Prop|Type|noncomputable|sorry|axiom|if|then|else|classical|simp|intro)$/.test(
                      token,
                    ) ? (
                    <span
                      key={i}
                      className={
                        token === 'sorry' ? 'lean-sorry' : 'lean-keyword'
                      }
                    >
                      {token}
                    </span>
                  ) : (
                    token
                  );
                })}
                {line.length === 0 ? ' ' : ''}
              </span>
            </span>
          ))}
        </code>
      </pre>
      {source.proofOffset !== null && (
        <button
          className="proof-toggle"
          onClick={() => setExpanded(!expanded)}
          aria-expanded={expanded}
        >
          <ChevronDown className={expanded ? 'rotated' : ''} size={16} />
          {expanded
            ? 'Collapse proof'
            : `Expand Lean proof (${source.source.slice(source.proofOffset).split('\n').length} lines)`}
        </button>
      )}
    </div>
  );
}

function TreeNode({
  name,
  rows,
  path = [],
}: {
  name: string;
  rows: Map<string, Declaration>;
  path?: string[];
}) {
  const [open, setOpen] = useState(false);
  const row = rows.get(name);
  if (!row) return null;
  const cycle = path.includes(name);
  return (
    <li>
      <div className="tree-row">
        <button
          onClick={() => setOpen(!open)}
          disabled={!row.dependencies.length || cycle}
          aria-expanded={open}
          aria-label={`Expand ${shortName(name)}`}
        >
          <ChevronDown size={15} className={open ? '' : 'sideways'} />
        </button>
        <span className={`tiny-dot status-${row.status}`} />
        <a href={route('read', name)}>{shortName(name)}</a>
        <span className="muted">{row.dependencies.length}</span>
      </div>
      {open && !cycle && (
        <ul>
          {row.dependencies.map((dep) => (
            <TreeNode key={dep} name={dep} rows={rows} path={[...path, name]} />
          ))}
        </ul>
      )}
    </li>
  );
}

function DependencyGraph({
  row,
  rows,
  ancestors,
}: {
  row: Declaration;
  rows: Map<string, Declaration>;
  ancestors: Map<string, string[]>;
}) {
  const [depth, setDepth] = useState(2),
    [onlyAdmissions, setOnlyAdmissions] = useState(false),
    [zoom, setZoom] = useState(1);
  const graph = useMemo(
    () => graphSlice(rows, row.name, depth, onlyAdmissions, ancestors),
    [rows, row.name, depth, onlyAdmissions, ancestors],
  );
  const nodes = new Map(graph.nodes.map((n) => [n.name, n]));
  return (
    <section className="graph-section">
      <div className="graph-toolbar">
        <label>
          Depth{' '}
          <select
            value={depth}
            onChange={(e) => setDepth(Number(e.target.value))}
          >
            {[1, 2, 3, 4, 6, 10].map((n) => (
              <option key={n}>{n}</option>
            ))}
          </select>
        </label>
        <label className="checkbox-label">
          <input
            type="checkbox"
            checked={onlyAdmissions}
            onChange={(e) => setOnlyAdmissions(e.target.checked)}
          />
          Paths to an admission
        </label>
        <div className="toolbar-spacer" />
        <Button
          variant="outline"
          size="icon"
          aria-label="Zoom out"
          onClick={() => setZoom(Math.max(0.4, zoom - 0.15))}
        >
          <ZoomOut />
        </Button>
        <span className="zoom-label">{Math.round(zoom * 100)} %</span>
        <Button
          variant="outline"
          size="icon"
          aria-label="Zoom in"
          onClick={() => setZoom(Math.min(1.75, zoom + 0.15))}
        >
          <ZoomIn />
        </Button>
        <Button
          variant="outline"
          onClick={() =>
            download(
              graphDot(graph.nodes, graph.edges),
              'dependencies-view.dot',
            )
          }
        >
          <Download />
          DOT
        </Button>
      </div>
      <p className="graph-caption">
        <strong>A → B</strong> means “A uses B”. {graph.nodes.length} nodes
        shown out of {graph.total} in this neighbourhood.
        {graph.total > graph.nodes.length && (
          <strong>
            {' '}
            View limited to 70 nodes: reduce the depth or choose another root.
          </strong>
        )}
      </p>
      <div
        className="graph-canvas"
        tabIndex={0}
        aria-label="Dependency graph, scroll horizontally and vertically"
      >
        <svg
          width={graph.width * zoom}
          height={graph.height * zoom}
          viewBox={`0 0 ${graph.width} ${graph.height}`}
          role="img"
          aria-label={`Dependencies of ${shortName(row.name)}`}
        >
          <defs>
            <marker
              id="arrow"
              markerWidth="8"
              markerHeight="8"
              refX="7"
              refY="4"
              orient="auto"
            >
              <path d="M0,0 L8,4 L0,8" fill="#a6b4c9" />
            </marker>
          </defs>
          {graph.edges.map(([a, b]) => {
            const from = nodes.get(a)!,
              to = nodes.get(b)!;
            return (
              <path
                key={`${a}|${b}`}
                d={`M${from.x + 270},${from.y + 29} C${from.x + 308},${from.y + 29} ${to.x - 38},${to.y + 29} ${to.x - 4},${to.y + 29}`}
                stroke="#a6b4c9"
                strokeWidth="1.2"
                fill="none"
                markerEnd="url(#arrow)"
              />
            );
          })}
          {graph.nodes.map((node) => {
            const label = shortName(node.name);
            const chunks =
              label.length > 32
                ? [
                    label.slice(0, 32),
                    label.slice(32, 62) + (label.length > 62 ? '…' : ''),
                  ]
                : [label];
            return (
              <a
                href={route('graph', node.name)}
                key={node.name}
                aria-label={`Focus on ${label}`}
              >
                <title>
                  {node.name} — {statusLabels[node.status]}
                </title>
                <rect
                  x={node.x}
                  y={node.y}
                  width={270}
                  height={58}
                  rx={6}
                  fill={node.name === row.name ? '#eef3ff' : '#fff'}
                  stroke={node.name === row.name ? '#4263cf' : '#d4dce9'}
                  strokeWidth={node.name === row.name ? 1.7 : 1}
                />
                <rect
                  x={node.x}
                  y={node.y + 11}
                  width={3}
                  height={36}
                  rx={1.5}
                  fill={colors[node.status]}
                />
                {chunks.map((chunk, i) => (
                  <text
                    key={i}
                    x={node.x + 13}
                    y={node.y + (chunks.length === 1 ? 33 : 24 + i * 17)}
                    fill="#25324b"
                    fontFamily="monospace"
                    fontSize={12}
                  >
                    {chunk}
                  </text>
                ))}
              </a>
            );
          })}
        </svg>
      </div>
      <div className="legend">
        {Object.entries(statusLabels)
          .filter(([key]) => key !== 'open_target')
          .map(([key, label]) => (
            <span key={key}>
              <i style={{ background: colors[key] }} />
              {label}
            </span>
          ))}
      </div>
      <div className="tree-panel">
        <h2>Explore the dependency tree</h2>
        <p className="muted">
          Expand a branch to see its direct dependencies. The same lemma may
          appear in several branches.
        </p>
        <ul className="dependency-tree">
          <TreeNode key={row.name} name={row.name} rows={rows} />
        </ul>
      </div>
    </section>
  );
}

function DocumentView({
  name,
  translated,
}: {
  name: string;
  translated: boolean;
}) {
  const [text, setText] = useState(''),
    [error, setError] = useState(false);
  const validName = /^[A-Z0-9_]+\.md$/.test(name);
  useEffect(() => {
    const controller = new AbortController();
    if (!validName) return;
    fetch(translated ? `./notes/en/${name}` : `./sources/docs/${name}`, {
      signal: controller.signal,
    })
      .then((r) => {
        if (!r.ok) throw Error();
        return r.text();
      })
      .then(setText)
      .catch((e) => {
        if (e.name !== 'AbortError') setError(true);
      });
    return () => controller.abort();
  }, [name, validName, translated]);
  return (
    <div className="document-view">
      <a className="back-link" href={route('admissions', MAIN)}>
        <ArrowLeft size={16} />
        Back to admissions
      </a>
      <p className="document-language">
        English repository note.{' '}
        <a href={`./sources/docs/${name}`} target="_blank" rel="noreferrer">
          View repository source
        </a>
      </p>
      {error || !validName ? (
        <p role="alert">This document is not available in this export.</p>
      ) : text ? (
        <div className="markdown-document">
          <Markdown text={text} documentName={name} />
        </div>
      ) : (
        <output>Loading document…</output>
      )}
    </div>
  );
}

export function ReviewSite({ bootstrap }: { bootstrap: Bootstrap }) {
  const [rows, setRows] = useState<Declaration[]>([bootstrap.initialRow]);
  const [ready, setReady] = useState(false),
    [loadError, setLoadError] = useState('');
  const [view, setView] = useState('read'),
    [selected, setSelected] = useState(MAIN),
    [docName, setDocName] = useState('ADMISSIONS.md');
  const [query, setQuery] = useState(''),
    [statusFilter, setStatusFilter] = useState('all'),
    [mobileNav, setMobileNav] = useState(false);
  const [sourceResult, setSourceResult] = useState<{
    name: string;
    source: Source | null;
    error: boolean;
  }>({ name: MAIN, source: bootstrap.initialSource, error: false });
  const [tab, setTab] = useState('reading'),
    [showDoc, setShowDoc] = useState(false);
  const rowMap = useMemo(
    () => new Map(rows.map((row) => [row.name, row])),
    [rows],
  );
  const notices = useMemo(
    () =>
      new Map<string, Notice>(
        bootstrap.curated.entries.map((entry) => [entry.name, entry]),
      ),
    [bootstrap],
  );
  const ancestors = useMemo(
    () =>
      admissionAncestors(
        rows,
        bootstrap.admissions.map((a) => a.name),
      ),
    [rows, bootstrap],
  );
  const row = rowMap.get(selected) ?? bootstrap.initialRow;
  const notice = notices.get(row.name);
  const source =
    selected === MAIN
      ? bootstrap.initialSource
      : (moduleCache.get(moduleName(row.file))?.[selected] ??
        (sourceResult.name === selected ? sourceResult.source : null));
  const sourceError = sourceResult.name === selected && sourceResult.error;
  const isMain =
    row.name === MAIN || row.name === 'InfiniteZero.elementaryPotential_main';

  useEffect(() => {
    const controller = new AbortController();
    fetch('./data/index.json', { signal: controller.signal })
      .then((r) => {
        if (!r.ok) throw Error();
        return r.json() as Promise<Declaration[]>;
      })
      .then((data) => {
        setRows(data);
        setReady(true);
      })
      .catch((e) => {
        if (e.name !== 'AbortError')
          setLoadError(
            'The catalogue could not be loaded. Serve the site over HTTP, then reload this page.',
          );
      });
    return () => controller.abort();
  }, []);
  useEffect(() => {
    function readHash() {
      const [nextView, ...parts] = window.location.hash.slice(1).split('/');
      if (!['read', 'graph', 'admissions', 'notes'].includes(nextView)) return;
      let name;
      try {
        name = decodeURIComponent(parts.join('/')) || MAIN;
      } catch {
        return;
      }
      setView(nextView);
      if (nextView === 'notes') setDocName(name);
      else setSelected(name);
      setMobileNav(false);
      setTab('reading');
      setShowDoc(false);
    }
    readHash();
    window.addEventListener('hashchange', readHash);
    return () => window.removeEventListener('hashchange', readHash);
  }, []);
  useEffect(() => {
    if (!ready || !rowMap.has(selected) || selected === MAIN) return;
    const key = moduleName(row.file);
    if (moduleCache.has(key)) return;
    const controller = new AbortController();
    fetch(`./data/modules/${key}.json`, { signal: controller.signal })
      .then((r) => {
        if (!r.ok) throw Error();
        return r.json() as Promise<Record<string, Source>>;
      })
      .then((data) => {
        moduleCache.set(key, data);
        setSourceResult({
          name: selected,
          source: data[selected],
          error: false,
        });
      })
      .catch((e) => {
        if (e.name !== 'AbortError')
          setSourceResult({ name: selected, source: null, error: true });
      });
    return () => controller.abort();
  }, [selected, row.file, ready, rowMap]);

  const searchResults = useMemo(() => {
    const terms = query.toLocaleLowerCase().trim().split(/\s+/);
    return rows.filter(
      (r) =>
        (statusFilter === 'all' || r.status === statusFilter) &&
        terms.every((term) =>
          `${r.name} ${r.file} ${notices.get(r.name)?.title ?? ''} ${notices.get(r.name)?.summary ?? ''}`
            .toLocaleLowerCase()
            .includes(term),
        ),
    );
  }, [query, rows, notices, statusFilter]);
  const selectedAdmissions = ancestors.get(row.name) ?? [];
  const texMap: Record<
    string,
    { label: string; line: number; endLine: number; source: string }
  > = bootstrap.tex;

  return (
    <div className="site-shell">
      <a href="#main-content" className="skip-link">
        Skip to content
      </a>
      <header className="site-header">
        <div className="brand">
          <span className="brand-mark">∞</span>
          <a href={route('read', MAIN)}>
            Infinite Zero<span>MANUSCRIPT & LEAN</span>
          </a>
        </div>
        <div className="header-context">
          One fixed potential. Infinitely many zeros.
        </div>
        <a
          className="header-link"
          href={`./sources/${bootstrap.curated.tex_file}`}
          download
        >
          <FileText size={16} />
          Manuscript TeX
          <Download size={14} />
        </a>
        <Button
          variant="ghost"
          className="mobile-menu"
          aria-label="Open navigation"
          onClick={() => setMobileNav(!mobileNav)}
        >
          {mobileNav ? <X /> : <Menu />}
        </Button>
      </header>
      <aside
        className={`sidebar ${mobileNav ? 'sidebar-open' : ''}`}
        aria-label="Reading guide and search"
      >
        <div className="sidebar-inner">
          <div className="search-box">
            <Search size={17} />
            <Input
              value={query}
              onChange={(e) => setQuery(e.target.value)}
              placeholder="Search declarations…"
              aria-label="Search all Lean declarations"
            />
            {query && (
              <button onClick={() => setQuery('')} aria-label="Clear search">
                <X size={14} />
              </button>
            )}
          </div>
          <div className="sidebar-caption">
            {bootstrap.metadata.declarations.toLocaleString('en')} declarations
            · {bootstrap.metadata.modules} files
          </div>
          <nav className="primary-nav" aria-label="Site views">
            {[
              { id: 'read', title: 'Side-by-side reading', icon: BookOpen },
              { id: 'graph', title: 'Dependencies', icon: GitBranch },
              { id: 'admissions', title: 'Admissions', icon: ShieldCheck },
            ].map(({ id, title, icon: Icon }) => (
              <a
                key={id}
                href={route(id, selected)}
                aria-current={view === id ? 'page' : undefined}
              >
                <Icon size={17} />
                {title}
                {id === 'admissions' && <span className="nav-count">4</span>}
              </a>
            ))}
          </nav>
          <div className="nav-divider" />
          <label className="filter-label" htmlFor="status-filter">
            Filter by status
          </label>
          <select
            id="status-filter"
            className="status-select"
            value={statusFilter}
            onChange={(e) => setStatusFilter(e.target.value)}
          >
            <option value="all">All statuses</option>
            {Object.entries(statusLabels).map(([key, label]) => (
              <option value={key} key={key}>
                {label}
              </option>
            ))}
          </select>
          {query || statusFilter !== 'all' ? (
            <div className="search-results">
              <div className="group-label">
                {ready
                  ? `${searchResults.length} result${searchResults.length === 1 ? '' : 's'}`
                  : 'Loading catalogue…'}
              </div>
              {searchResults.slice(0, 120).map((r) => (
                <a
                  key={r.name}
                  href={route('read', r.name)}
                  className={r.name === selected ? 'selected' : ''}
                >
                  <span className={`tiny-dot status-${r.status}`} />
                  <span>{shortName(r.name)}</span>
                </a>
              ))}
              {searchResults.length > 120 && (
                <p className="muted">
                  Showing 120 results. Refine your search.
                </p>
              )}
              {ready && !searchResults.length && (
                <p className="muted">No declarations match these filters.</p>
              )}
            </div>
          ) : (
            <nav className="reading-nav" aria-label="Reading guide">
              {categories.map((category, i) => (
                <section key={category}>
                  <h2 className="group-label">
                    <span>{String(i + 1).padStart(2, '0')}</span>
                    {category}
                  </h2>
                  {bootstrap.curated.entries
                    .filter((entry) => entry.category === category)
                    .map((entry) => (
                      <a
                        href={route('read', entry.name)}
                        key={entry.name}
                        className={
                          selected === entry.name && view === 'read'
                            ? 'selected'
                            : ''
                        }
                        title={entry.name}
                      >
                        {entry.title}
                      </a>
                    ))}
                </section>
              ))}
            </nav>
          )}
          <div className="sidebar-footer">
            <span className="live-dot" />
            {bootstrap.metadata.leanVersion.replace(
              'leanprover/lean4:',
              'Lean ',
            )}
            <a href={route('notes', 'STATEMENT_AUDIT.md')}>
              Statement review guide <ArrowRight size={13} />
            </a>
          </div>
        </div>
      </aside>
      <main id="main-content" className="main-area" tabIndex={-1}>
        {loadError && (
          <div role="alert" className="notice-warning">
            {loadError}
          </div>
        )}
        {view === 'notes' ? (
          <DocumentView
            key={docName}
            name={docName}
            translated={bootstrap.translatedDocuments.includes(docName)}
          />
        ) : view === 'admissions' ? (
          <section className="admissions-page">
            <div className="eyebrow">CLASSICAL RESULTS</div>
            <h1>The classical admissions</h1>
            <p className="page-intro">
              The proof of <code>thm_main</code> uses these admitted
              results, each with a Lean statement, a
              mathematical justification and references.
            </p>
            <div className="admission-list">
              {bootstrap.admissions.map((admission) => (
                <article key={admission.id}>
                  <div className="admission-number">{admission.id}</div>
                  <div>
                    <h2>{admission.title}</h2>
                    <p>{notices.get(admission.name)?.summary}</p>
                    <div className="admission-actions">
                      <a href={route('read', admission.name)}>
                        <Braces size={16} />
                        Read the Lean contract
                        <ArrowRight size={15} />
                      </a>
                      <a href={route('notes', admission.document)}>
                        <FileText size={16} />
                        Justification and references
                        <ArrowRight size={15} />
                      </a>
                    </div>
                  </div>
                  <Status status="admitted" />
                </article>
              ))}
            </div>
            <div className="scope-note">
              <h2>What “no admissions” means</h2>
              <p>
                This status means that the audit finds no <code>sorryAx</code>{' '}
                in the declaration’s dependencies. A lemma may still have
                explicit hypotheses. The usual Lean axioms —{' '}
                <code>propext</code>, <code>Classical.choice</code>,{' '}
                <code>Quot.sound</code> — are not project admissions.
              </p>
              <a href={route('notes', 'ADMISSIONS.md')}>
                Read the full register <ArrowRight size={15} />
              </a>
            </div>
          </section>
        ) : (
          <>
            <div className="breadcrumb">
              <a href={route('read', MAIN)}>Main theorem</a>
              <span>/</span>
              <span>
                {view === 'graph'
                  ? 'Dependencies'
                  : (notice?.category ?? moduleName(row.file))}
              </span>
            </div>
            <div className="entry-heading">
              <div>
                <div className="eyebrow">
                  {view === 'graph'
                    ? 'LEAN DEPENDENCIES'
                    : (notice?.tex_labels[0] ?? 'LEAN DECLARATION')}
                </div>
                <h1>
                  {view === 'graph'
                    ? 'The structure of the proof'
                    : (notice?.title ?? shortName(row.name))}
                </h1>
                <div className="qualified-name">
                  {ready && !rowMap.has(selected) ? selected : row.name}
                </div>
              </div>
              <Status status={row.status} />
            </div>
            {ready && !rowMap.has(selected) ? (
              <div role="alert" className="notice-warning">
                This declaration is not in the inventory. Use the search on the
                left to find its current name.
              </div>
            ) : (
              <>
                {view === 'graph' ? (
                  <>
                    <p className="page-intro">
                      Centred on <code>{shortName(row.name)}</code>. Click a
                      node to refocus the graph; use the tree below to open its
                      source.
                    </p>
                    <div className="graph-summary">
                      <a href={route('read', row.name)}>
                        <BookOpen size={16} />
                        Read this declaration
                      </a>
                      <span>{row.dependencies.length} direct dependencies</span>
                      <span>
                        {selectedAdmissions.length} transitive admission(s)
                      </span>
                    </div>
                    {ready ? (
                      <DependencyGraph
                        row={row}
                        rows={rowMap}
                        ancestors={ancestors}
                      />
                    ) : (
                      <output>Loading dependencies…</output>
                    )}
                  </>
                ) : (
                  <>
                    {row.status === 'depends_on_admission' && (
                      <div className="trust-strip">
                        <ShieldCheck size={17} />
                        <span>
                          This proof depends on{' '}
                          {ready ? selectedAdmissions.length : 4} admitted results.
                        </span>
                        <a href={route('admissions', row.name)}>
                          Review them <ArrowRight size={14} />
                        </a>
                      </div>
                    )}
                    {row.status === 'admitted' && (
                      <div className="trust-strip admitted-strip">
                        <ShieldCheck size={17} />
                        <span>
                          Admitted result, marked with <code>sorry</code> in Lean.
                        </span>
                        <a
                          href={route(
                            'notes',
                            bootstrap.admissions.find(
                              (a) => a.name === row.name,
                            )!.document,
                          )}
                        >
                          Justification and references <ArrowRight size={14} />
                        </a>
                      </div>
                    )}
                    <div className="parallel-view">
                      <section className="informal-pane">
                        <div className="pane-heading">
                          <BookOpen size={17} />
                          <h2>The mathematics</h2>
                          <span>INFORMAL</span>
                        </div>
                        <div className="informal-content">
                          <div className="section-kicker">
                            {notice
                              ? 'EXPLANATION'
                              : 'SOURCE DOCUMENTATION'}
                          </div>
                          {notice ? (
                            <p className="math-summary">{notice.summary}</p>
                          ) : source?.doc ? (
                            <div className="source-doc prose">
                              <Markdown text={source.doc} />
                            </div>
                          ) : (
                            <p className="muted">
                              See the Lean statement and its dependencies in
                              the adjacent panel.
                            </p>
                          )}
                          {isMain && (
                            <div className="main-items">
                              {bootstrap.curated.main_items.map((item) => (
                                <article key={item.item}>
                                  <span className="item-ordinal">
                                    {item.item}
                                  </span>
                                  <div>
                                    <h3>{item.title}</h3>
                                    <p>{item.summary}</p>
                                    <div className="item-links">
                                      {item.declarations.map((name) => {
                                        const target = resolveName(
                                          name,
                                          rowMap,
                                        );
                                        return (
                                          <a
                                            key={name}
                                            href={route(
                                              'read',
                                              target ??
                                                (notices.has(name)
                                                  ? name
                                                  : name
                                                      .split('.')
                                                      .slice(0, -1)
                                                      .join('.')),
                                            )}
                                          >
                                            {name.split('.').pop()}{' '}
                                            <ArrowRight size={12} />
                                          </a>
                                        );
                                      })}
                                    </div>
                                  </div>
                                </article>
                              ))}
                            </div>
                          )}
                          {notice && notice.tex_labels.length > 0 && (
                            <div className="tex-section">
                              <div className="section-kicker">
                                IN THE MANUSCRIPT{' '}
                                <span>
                                  ·{' '}
                                  {notice.tex_relation === 'specialisation'
                                    ? 'explicit specialization'
                                    : notice.tex_relation === 'interpretation'
                                      ? 'interpretation'
                                      : notice.tex_relation === 'related'
                                        ? 'related passage — different scope'
                                        : 'correspondence'}
                                </span>
                              </div>
                              <div
                                className="local-tabs"
                                role="tablist"
                                aria-label="TeX excerpt display"
                              >
                                <button
                                  role="tab"
                                  aria-selected={tab === 'reading'}
                                  onClick={() => setTab('reading')}
                                >
                                  Reading
                                </button>
                                <button
                                  role="tab"
                                  aria-selected={tab === 'tex'}
                                  onClick={() => setTab('tex')}
                                >
                                  TeX source
                                </button>
                              </div>
                              {notice.tex_labels.map((label, i) => {
                                const excerpt = texMap[label];
                                return (
                                  <details
                                    className="tex-excerpt"
                                    key={label}
                                    open={i === 0}
                                  >
                                    <summary>
                                      <span>{label}</span>
                                      <span>
                                        L{excerpt.line}–{excerpt.endLine}
                                      </span>
                                    </summary>
                                    {tab === 'tex' ? (
                                      <pre className="raw-tex">
                                        {excerpt.source}
                                      </pre>
                                    ) : (
                                      <div className="tex-render">
                                        <Markdown
                                          text={texForReading(excerpt.source)}
                                        />
                                      </div>
                                    )}
                                  </details>
                                );
                              })}
                              <p className="small-note">
                                Excerpts from the active TeX. The TeX source tab
                                preserves the exact text; the Reading view
                                simplifies its layout.
                              </p>
                            </div>
                          )}
                          {notice && source?.doc && (
                            <details
                              className="doc-details"
                              open={showDoc}
                              onToggle={(e) => setShowDoc(e.currentTarget.open)}
                            >
                              <summary>Read the Lean docstring</summary>
                              <div className="source-doc">
                                <Markdown text={source.doc} />
                              </div>
                            </details>
                          )}
                        </div>
                      </section>
                      <section className="formal-pane">
                        <div className="pane-heading">
                          <Braces size={17} />
                          <h2>The Lean code</h2>
                          <span>FORMAL</span>
                        </div>
                        {sourceError ? (
                          <p className="pane-error" role="alert">
                            Source unavailable in this export.
                          </p>
                        ) : source ? (
                          <LeanCode key={row.name} source={source} row={row} />
                        ) : (
                          <output className="pane-error">
                            Loading source…
                          </output>
                        )}
                        <div className="formal-footnote">
                          Underlined names link to the declarations being used.
                          The code is extracted from the repository; imports and
                          section variables remain in the complete file.
                        </div>
                        <div className="dependency-card">
                          <div className="dependency-title">
                            <h3>
                              Direct dependencies{' '}
                              <span>{row.dependencies.length}</span>
                            </h3>
                            <a href={route('graph', row.name)}>
                              <GitBranch size={15} />
                              View graph
                            </a>
                          </div>
                          <div className="dependency-links">
                            {row.dependencies.length ? (
                              row.dependencies.map((name) => (
                                <a key={name} href={route('read', name)}>
                                  <span
                                    className={`tiny-dot status-${rowMap.get(name)?.status ?? 'definition_or_contract'}`}
                                  />
                                  {shortName(name)}
                                  <ArrowRight size={13} />
                                </a>
                              ))
                            ) : (
                              <p className="muted">
                                No dependencies on other declarations in this
                                project.
                              </p>
                            )}
                          </div>
                        </div>
                        {ready && selectedAdmissions.length > 0 && (
                          <div className="ancestor-list">
                            <h3>Transitive admissions</h3>
                            {bootstrap.admissions
                              .filter((a) =>
                                selectedAdmissions.includes(a.name),
                              )
                              .map((a) => (
                                <a href={route('read', a.name)} key={a.id}>
                                  <span>{a.id}</span>
                                  {a.title}
                                  <ArrowRight size={13} />
                                </a>
                              ))}
                          </div>
                        )}
                      </section>
                    </div>
                    {isMain && (
                      <section className="proof-roadmap">
                        <div className="section-kicker">
                          FOLLOW THE ARGUMENT
                        </div>
                        <h2>
                          From the explicit potential to the three conclusions
                        </h2>
                        <p className="muted">
                          A reading guide; the actual dependencies are shown in
                          the Lean graph.
                        </p>
                        <div className="roadmap-steps">
                          {bootstrap.curated.assembly_steps.map((step, i) => (
                            <article key={step.title}>
                              <span>{String(i + 1).padStart(2, '0')}</span>
                              <h3>{step.title}</h3>
                              <p>{step.text}</p>
                              {step.declarations.map((name) => (
                                <a key={name} href={route('read', name)}>
                                  {name.split('.').pop()}{' '}
                                  <ArrowRight size={12} />
                                </a>
                              ))}
                            </article>
                          ))}
                        </div>
                        <details className="scope-details">
                          <summary>Exact scope of the formalization</summary>
                          <ul>
                            {bootstrap.curated.scope_notes
                              .filter((_, i) => [2, 3, 4].includes(i))
                              .map((note) => (
                                <li key={note}>{note}</li>
                              ))}
                          </ul>
                          <a href={route('notes', 'STATEMENT_AUDIT.md')}>
                            Read the statement audit
                          </a>
                        </details>
                      </section>
                    )}
                  </>
                )}
              </>
            )}
          </>
        )}
        <footer className="page-footer">
          <div>
            <strong>Infinite Zero</strong>
            <span>Manuscript, formal proofs and dependencies</span>
          </div>
          <div>
            <a href={route('notes', 'ADMISSIONS.md')}>Admission register</a>
            <a href="./sources/dependencies.dot" download>
              Full graph · DOT
            </a>
            <details>
              <summary>Snapshot provenance</summary>
              <p>
                Dependencies from the latest Lean audit:{' '}
                <code>docs/declarations.json</code>. Nodes group generated
                projections and constants under their source declaration;
                Mathlib is not drawn. The full DOT file uses the reverse
                convention: dependency → user.
              </p>
              <p>
                Code and line numbers are extracted from the repository when
                the site is generated.
              </p>
              <p>
                Audit fingerprint: <code>{bootstrap.metadata.auditSha256}</code>
              </p>
              <p>
                Source fingerprint:{' '}
                <code>{bootstrap.metadata.sourceSha256}</code>
              </p>
            </details>
          </div>
        </footer>
      </main>
    </div>
  );
}
