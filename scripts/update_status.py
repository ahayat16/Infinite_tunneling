#!/usr/bin/env python3
"""Regenerate the declaration inventory and dependency graph from Lean's environment.

No third-party Python package is required. Run after `lake build`.
"""
from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
OPEN_TARGETS = set()
FINAL_TARGETS = {
    "InfiniteZero.CuspParameters.mainConclusion",
    "InfiniteZero.elementaryPotential_main",
    "InfiniteZero.thm_main",
}


def source_declarations():
    records = {}
    pattern = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected)\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|opaque|axiom)\s+([\w'.]+)")
    for path in sorted((ROOT / "InfiniteZero").glob("*.lean")):
        scopes = []
        for line_number, line in enumerate(strip_comments(path.read_text()).splitlines(), 1):
            match = re.match(r"^namespace\s+([\w.]+)\s*$", line)
            if match:
                scopes.append(("namespace", match[1]))
                continue
            match = re.match(r"^(?:noncomputable\s+)?section(?:\s+([\w.]+))?\s*$", line)
            if match:
                scopes.append(("section", match[1]))
                continue
            if re.match(r"^end(?:\s+[\w.]+)?\s*$", line):
                if scopes:
                    scopes.pop()
                continue
            match = pattern.match(line)
            if match:
                declared_name = match[2]
                name = (declared_name[len("_root_."):] if declared_name.startswith("_root_.") else
                        ".".join([*[n for kind, n in scopes if kind == "namespace"], declared_name]))
                records[name] = {
                    "name": name,
                    "source_kind": match[1],
                    "file": str(path.relative_to(ROOT)),
                    "line": line_number,
                }
    return records


def strip_comments(text):
    """Preserve line numbers while removing Lean's nested and line comments."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == "\\" and i + 1 < len(text):
                i += 1
                out.append(text[i])
            elif text[i] == '"':
                quoted = False
            i += 1
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
        elif pair == "--":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        else:
            quoted = text[i] == '"'
            out.append(text[i])
            i += 1
    return "".join(out)


def main():
    process = subprocess.run(
        ["lake", "env", "lean", "scripts/ExportAudit.lean"],
        cwd=ROOT, text=True, capture_output=True, check=False,
    )
    if process.returncode:
        raise SystemExit(process.stdout + process.stderr)
    compiled = {}
    for line in process.stdout.splitlines():
        if line.startswith("AUDIT_JSON "):
            row = json.loads(line[len("AUDIT_JSON "):])
            compiled[row["name"]] = row
    source = source_declarations()
    aliases = {}
    for name in source:
        if name in compiled:
            aliases[name] = name
        else:
            candidates = [n for n in compiled if n.startswith("_private.") and n.endswith("." + name)]
            if len(candidates) == 1:
                aliases[candidates[0]] = name
                compiled[name] = compiled[candidates[0]]
    missing = sorted(set(source) - set(compiled))
    if missing:
        raise SystemExit(f"Declarations missing from compiled environment: {missing}")

    # Collapse generated projections/recursors to their public source declaration.
    # Edges retain actual references in the elaborated type or proof/value.
    ordered_names = sorted(source, key=len, reverse=True)

    def owner(name):
        if name in aliases:
            return aliases[name]
        return next((n for n in ordered_names if name == n or name.startswith(n + ".")), None)

    rows = []
    for name, record in sorted(source.items()):
        data = compiled[name]
        ax = sorted(data["axioms"])
        direct = "sorryAx" in data["dependencies"] or data["kind"] == "axiom"
        if name in OPEN_TARGETS and direct:
            status = "open_target"
        elif direct:
            status = "admitted"
        elif "sorryAx" in ax:
            status = "depends_on_admission"
        elif record["source_kind"] in {"theorem", "lemma"}:
            status = "proved"
        else:
            status = "definition_or_contract"
        deps = sorted({o for dep in data["dependencies"] if (o := owner(dep)) and o != name})
        rows.append({**record, "status": status, "axioms": ax, "dependencies": deps})

    admitted = [r["name"] for r in rows if r["status"] == "admitted"]
    expected = ["InfiniteZero.classical_radial_low_levels",
                "InfiniteZero.classical_standard_landau_resolvent",
                "InfiniteZero.magnetic_realization"]
    if admitted != expected:
        raise SystemExit(f"Admission registry needs review: expected {expected}, found {admitted}")
    # Also inspect generated/private/otherwise unlisted constants, so an unused
    # admission cannot evade the registry merely by avoiding a source keyword.
    for cname, data in compiled.items():
        if "sorryAx" in data["dependencies"] or data["kind"] == "axiom":
            if owner(cname) not in set(expected) | OPEN_TARGETS:
                raise SystemExit(f"Unregistered admitted constant: {cname}")
        if set(data["dependencies"]) & OPEN_TARGETS:
            raise SystemExit(f"An unfinished target is being used as an input: {cname}")
    unexpected = sorted({a for r in rows for a in r["axioms"]} -
                        {"propext", "Classical.choice", "Quot.sound", "sorryAx"})
    if unexpected:
        raise SystemExit(f"Unexpected axioms: {unexpected}")
    for row in rows:
        if "sorryAx" in row["axioms"] and row["name"] not in {
            "InfiniteZero.classical_radial_harmonic",
            "InfiniteZero.classical_radial_low_levels",
            "InfiniteZero.classical_standard_landau_resolvent",
            "InfiniteZero.free_landau_resolvent_kernel", "InfiniteZero.magnetic_realization",
            "InfiniteZero.radial_core_spectral_data",
            "InfiniteZero.CuspParameters.radialCore_kernel",
            "InfiniteZero.CuspParameters.radialCore_normalization_lower",
            "InfiniteZero.CuspParameters.atomicGround_weighted_decomposition",
            "InfiniteZero.CuspParameters.atomicGround_fine_weighted_decomposition",
            "InfiniteZero.CuspParameters.atomicGround_fine_response_data",
            "InfiniteZero.CuspParameters.atomicGround_fine_response_jets",
            "InfiniteZero.CuspParameters.atomicGround_scattered_source_jets",
            "InfiniteZero.CuspParameters.atomicGround_source_profiles",
            "InfiniteZero.CuspParameters.atomicGround_source_L1",
            "InfiniteZero.CuspParameters.atomicGround_component_source_L1",
            "InfiniteZero.CuspParameters.atomicGround_inactive_cells",
            "InfiniteZero.CuspParameters.atomicGround_inactive_relative",
            "InfiniteZero.CuspParameters.atomicGround_inactive_relative_tex",
            "InfiniteZero.CuspParameters.canonical_inactive_relative_tex",
            "InfiniteZero.CuspParameters.atomicGround_active_scattered_relative",
            "InfiniteZero.CuspParameters.atomicGround_active_incoming_reduction",
            "InfiniteZero.CuspParameters.canonicalHopping_asymptotic",
            "InfiniteZero.CuspParameters.exists_canonicalHopping_asymptotic_separation",
            "InfiniteZero.CuspParameters.canonicalOverlap_decay",
            "InfiniteZero.CuspParameters.canonicalOverlap_tendsto",
            "InfiniteZero.CuspParameters.doubleWell_complement_coercivity",
            "InfiniteZero.CuspParameters.doubleWell_parityGrounds",
            "InfiniteZero.CuspParameters.doubleWell_parityEnergy_continuous",
            "InfiniteZero.CuspParameters.doubleWell_signedSplitting_continuous",
            "InfiniteZero.CuspParameters.doubleWell_global_minmax",
            "InfiniteZero.CuspParameters.doubleWell_spectral_realization",
            "InfiniteZero.CuspParameters.doubleWell_twoModeRealization",
            "InfiniteZero.CuspParameters.canonicalHopping_continuous",
            "InfiniteZero.CuspParameters.radialCore_fine_forcing_derivatives",
            "InfiniteZero.CuspParameters.eventual_atomicGround_properties",
            "InfiniteZero.CuspParameters.atomic_source_regime",
            "InfiniteZero.CuspParameters.canonicalAtomicState_agmon_tail",
            "InfiniteZero.CuspParameters.atomicGroundEnergy_exponential_comparison",
            "InfiniteZero.CuspParameters.atomicGroundVectors_exponential_comparison",
            "InfiniteZero.thm_main_variational_from_analytic_data",
            "InfiniteZero.thm_main_from_analytic_data",
            *FINAL_TARGETS,
            *OPEN_TARGETS
        }:
            raise SystemExit(f"Unexpected admission dependency: {row['name']}")

    # The final proof must derive every original estimate from exactly the
    # three registered classical interfaces. A new direct or hidden admission
    # cannot be legitimized merely by assigning the final theorem a new status.
    by_name = {row["name"]: row for row in rows}
    for target in FINAL_TARGETS:
        if target not in by_name or by_name[target]["status"] != "depends_on_admission":
            raise SystemExit(f"Final theorem is missing or has an unexpected status: {target}")
        seen, pending = set(), [target]
        while pending:
            name = pending.pop()
            if name not in seen:
                seen.add(name)
                pending.extend(by_name[name]["dependencies"])
        actual = {name for name in seen if by_name[name]["status"] in {"admitted", "open_target"}}
        if actual != set(expected):
            raise SystemExit(f"Final theorem admission ancestry mismatch for {target}: {sorted(actual)}")

    DOCS.mkdir(exist_ok=True)
    (DOCS / "declarations.json").write_text(json.dumps(rows, ensure_ascii=False, indent=2) + "\n")
    colors = {"admitted": "#f6aaaa", "depends_on_admission": "#ffd18a",
              "proved": "#bce8ba", "definition_or_contract": "#c7dbef",
              "open_target": "#e5bbef"}
    dot = ["digraph LeanDependencies {", "  rankdir=LR;", '  node [shape=box, style=filled];']
    for r in rows:
        label = (r["name"][len("InfiniteZero."):] if r["name"].startswith("InfiniteZero.")
                 else r["name"])
        dot.append(f'  "{r["name"]}" [label="{label}", fillcolor="{colors[r["status"]]}"];')
        for dep in r["dependencies"]:
            dot.append(f'  "{dep}" -> "{r["name"]}";')
    dot.append("}")
    (DOCS / "dependencies.dot").write_text("\n".join(dot) + "\n")

    counts = {s: sum(r["status"] == s for r in rows) for s in colors}
    lines = [
        "# Lean-verified inventory", "",
        "Generated by `python3 scripts/update_status.py` from compiled constants. "
        "Dependencies include types and proofs/definitions. "
        "Generated projections are grouped under their structure.", "",
        f"- Theorems without admissions: **{counts['proved']}**.",
        f"- Definitions and contracts (no existence assertion): **{counts['definition_or_contract']}**.",
        f"- Direct admissions: **{counts['admitted']}**.",
        f"- Unproved final targets (`sorry`, forbidden as inputs): **{counts['open_target']}**.",
        f"- Theorems depending on an admission: **{counts['depends_on_admission']}**.", "",
        "A theorem without `sorryAx` may have explicit analytic hypotheses. "
        "In particular, `thm_main_of_analytic_data` does not prove the existence of its data. "
        "`elementaryPotential_main` proves the conclusion for the potential fixed by `elementaryParameters`; "
        "`thm_main` deduces the manuscript's unconditional target. Neither proof has a direct `sorry`. "
        "Their only transitive admissions are exactly A002–A004, checked by the audit. "
        "The original tunneling estimates and relative spectral errors are constructed in Lean.", "",
        "See [the admissions](ADMISSIONS.md), [the readable graph](DEPENDENCIES.md), "
        "[the full graph](dependencies.dot), and [the detailed data](declarations.json).", "",
        "| Declaration | Status | Source |", "|---|---|---|",
    ]
    labels = {"admitted": "**ADMITTED**", "depends_on_admission": "**DEPENDS ON ADMISSIONS**",
              "proved": "Proved under its hypotheses", "definition_or_contract": "Definition / contract",
              "open_target": "**UNPROVED TARGET**"}
    for r in rows:
        short = (r["name"][len("InfiniteZero."):] if r["name"].startswith("InfiniteZero.")
                 else r["name"])
        link = f"../{r['file']}#L{r['line']}"
        lines.append(f"| `{short}` | {labels[r['status']]} | [{r['file']}:{r['line']}]({link}) |")
    (DOCS / "STATUS.md").write_text("\n".join(lines) + "\n")
    print(json.dumps(counts, ensure_ascii=False))
    print("Updated docs/STATUS.md, declarations.json, dependencies.dot")


if __name__ == "__main__":
    main()
