// Same meanings as the manuscript preamble. Local aliases used in the
// formalisation-oriented expansions are listed explicitly, never guessed.
export const mathMacros: Record<string, string> = {
  '\\R': '\\mathbb{R}',
  '\\C': '\\mathbb{C}',
  '\\N': '\\mathbb{N}',
  '\\eps': '\\varepsilon',
  '\\dd': '\\,\\mathrm d',
  '\\abs': '\\left|#1\\right|',
  '\\norm': '\\left\\|#1\\right\\|',
  '\\ip': '\\left\\langle #1,#2\\right\\rangle',
  '\\wedgep': '\\mathbin{\\wedge}',
  '\\one': '\\mathbf 1',
  '\\HL': 'H_h^{L}',
  '\\Eo': '\\mathcal E_h^\\circ',
  '\\EE': '\\mathcal E_h',
  '\\phio': '\\phi_h^\\circ',
  '\\phih': '\\phi_h',
  '\\Ho': 'H_h^{\\rm atom}(v^\\circ)',
  '\\Ha': 'H_h^{\\rm atom}',
  '\\Dh': 'D_h',
  '\\ellh': '\\ell_h',
  '\\Gp': 'G_{p,h}',
  '\\Ast': 'A_{*,h}',
  '\\ahat': '\\widehat{\\mathfrak a}_h',
  '\\rh': '\\widehat\\rho_h',
  '\\deltah': '\\widehat\\delta_h',
  ...Object.fromEntries(
    'ABCDEFGHJL PQRSTO'
      .replaceAll(' ', '')
      .split('')
      .map((c) => [`\\c${c}`, `\\mathcal{${c}}`]),
  ),
  ...Object.fromEntries(
    ['supp', 'dist', 'Ran', 'Span', 'spec', 'tr', 'Log'].map((c) => [
      `\\${c}`,
      `\\operatorname{${c === 'Span' ? 'span' : c}}`,
    ]),
  ),
  '\\Rea': '\\operatorname{Re}',
  '\\Ima': '\\operatorname{Im}',
};

/** Reading layout only. The UI also displays the untouched source excerpt. */
export function texForReading(source: string) {
  return source
    .replace(/(?<!\\)%[^\n]*/g, '')
    .replace(/\\label\{[^}]+\}/g, '')
    .replace(
      /\\begin\{(?:theorem|lemma|proposition|corollary|definition|remark)\}(?:\[([^\]]*)\])?/g,
      (_, title) => (title ? `**${title}**\n\n` : ''),
    )
    .replace(
      /\\end\{(?:theorem|lemma|proposition|corollary|definition|remark)\}/g,
      '',
    )
    .replace(/\\begin\{enumerate\}(?:\[[^\n]*\])?/g, '\n')
    .replace(/\\end\{enumerate\}/g, '')
    .replace(/\\item\s*/g, '\n1. ')
    .replace(/\\(?:Cref|cref|ref)\{([^}]+)\}/g, '`$1`')
    .replace(/\\(?:sub)*section\{([^}]+)\}/g, '**$1**')
    .replace(/\\begin\{equation\*?\}/g, () => '\n$$\n')
    .replace(/\\end\{equation\*?\}/g, () => '\n$$\n')
    .replace(/\\begin\{align\*?\}/g, () => '\n$$\n\\begin{aligned}')
    .replace(/\\end\{align\*?\}/g, () => '\\end{aligned}\n$$\n');
}

export function normalizeMath(text: string) {
  // Replacement callbacks preserve two dollars (a replacement string would
  // interpret $$ as an escaped single dollar).
  return text
    .replace(/(?<!\\)\\\[/g, () => '\n$$\n')
    .replace(/(?<!\\)\\\]/g, () => '\n$$\n')
    .replace(/(?<!\\)\\\(/g, '$')
    .replace(/(?<!\\)\\\)/g, '$');
}
