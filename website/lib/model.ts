export type Declaration = {
  name: string;
  kind: string;
  file: string;
  line: number;
  status: string;
  dependencies: string[];
};
export type Source = {
  source: string;
  doc: string;
  line: number;
  endLine: number;
  proofOffset: number | null;
};
export type Notice = {
  name: string;
  title: string;
  category: string;
  summary: string;
  tex_labels: string[];
  tex_relation: string;
};
export const statusLabels: Record<string, string> = {
  proved: 'No admissions',
  definition_or_contract: 'Definition / contract',
  depends_on_admission: 'Uses admissions',
  admitted: 'Admitted',
  open_target: 'Unproved',
};
export function shortName(name: string) {
  return name.replace(/^InfiniteZero\./, '');
}
export function moduleName(file: string) {
  return file.split('/').pop()!.replace('.lean', '');
}
export function route(view: string, name: string) {
  return `#${view}/${encodeURIComponent(name)}`;
}
export function resolveName(
  name: string,
  rows: Map<string, Declaration>,
): string | undefined {
  let current = name;
  while (current.includes('.')) {
    if (rows.has(current)) return current;
    current = current.slice(0, current.lastIndexOf('.'));
  }
}

/** Reverse reachability uses audited edges; a reading order is never an edge. */
export function admissionAncestors(rows: Declaration[], admissions: string[]) {
  const reverse = new Map<string, string[]>();
  for (const row of rows)
    for (const dep of row.dependencies) {
      const parents = reverse.get(dep) ?? [];
      parents.push(row.name);
      reverse.set(dep, parents);
    }
  const result = new Map<string, string[]>();
  for (const admission of admissions) {
    const queue = [admission],
      seen = new Set(queue);
    for (let i = 0; i < queue.length; i++) {
      const name = queue[i];
      result.set(name, [...(result.get(name) ?? []), admission]);
      for (const parent of reverse.get(name) ?? [])
        if (!seen.has(parent)) {
          seen.add(parent);
          queue.push(parent);
        }
    }
  }
  return result;
}

/** Breadth-first neighbourhood. All displayed arrows are actual audited edges. */
export function graphSlice(
  rows: Map<string, Declaration>,
  root: string,
  depth: number,
  onlyAdmittedsions: boolean,
  ancestors: Map<string, string[]>,
  limit = 70,
) {
  const distances = new Map<string, number>();
  if (!rows.has(root))
    return { nodes: [], edges: [], total: 0, width: 800, height: 300 };
  const queue = [root];
  distances.set(root, 0);
  for (let i = 0; i < queue.length; i++) {
    const name = queue[i],
      distance = distances.get(name)!;
    if (distance >= depth) continue;
    for (const dep of rows.get(name)!.dependencies) {
      if (!rows.has(dep) || (onlyAdmittedsions && !ancestors.has(dep)))
        continue;
      if (!distances.has(dep)) {
        distances.set(dep, distance + 1);
        queue.push(dep);
      }
    }
  }
  const selected = queue.slice(0, limit),
    present = new Set(selected);
  const levels = new Map<number, string[]>();
  for (const name of selected) {
    const d = distances.get(name)!;
    levels.set(d, [...(levels.get(d) ?? []), name]);
  }
  const largest = Math.max(1, ...[...levels.values()].map((v) => v.length));
  const height = Math.max(340, largest * 94 + 64);
  const nodes = selected.map((name) => {
    const d = distances.get(name)!,
      siblings = levels.get(d)!;
    return {
      ...rows.get(name)!,
      x: 30 + d * 330,
      y:
        height / 2 +
        (siblings.indexOf(name) - (siblings.length - 1) / 2) * 94 -
        29,
    };
  });
  const edges = nodes.flatMap((row) =>
    row.dependencies
      .filter((dep) => present.has(dep))
      .map((dep) => [row.name, dep] as const),
  );
  return {
    nodes,
    edges,
    total: queue.length,
    width: Math.max(800, levels.size * 330 + 20),
    height,
  };
}

export function graphDot(
  nodes: Declaration[],
  edges: readonly (readonly [string, string])[],
) {
  return [
    'digraph Dependencies {',
    '  rankdir=LR;',
    '  node [shape=box];',
    ...nodes.map(
      (n) =>
        `  ${JSON.stringify(n.name)} [label=${JSON.stringify(shortName(n.name))}];`,
    ),
    ...edges.map(([a, b]) => `  ${JSON.stringify(a)} -> ${JSON.stringify(b)};`),
    '}',
  ].join('\n');
}
