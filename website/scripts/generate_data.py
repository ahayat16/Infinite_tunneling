#!/usr/bin/env python3
"""Build the read-only website snapshot from source files and the Lean audit.

Consumes docs/declarations.json and extracts source excerpts. Refresh the audit
with the repository's update_status.py after changing proofs.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import runpy
import shutil
from collections import Counter, defaultdict

SITE = Path(__file__).resolve().parents[1]
ROOT = SITE.parent
PUBLIC = SITE / "public"
AUDIT = ROOT / "docs/declarations.json"
helpers = runpy.run_path(str(ROOT / "scripts/update_status.py"))
strip_comments = helpers["strip_comments"]

ADMISSIONS = [
    ("A002", "InfiniteZero.magnetic_realization", "Magnetic operator realization", "CLASSICAL_OPERATOR_REALIZATION.md"),
    ("A003", "InfiniteZero.free_landau_resolvent_kernel", "Free Landau resolvent", "CLASSICAL_LANDAU_RESOLVENT.md"),
    ("A004", "InfiniteZero.radial_core_spectral_data", "Radial core spectrum", "RADIAL_HARMONIC_CONTRACT.md"),
    ("A005", "InfiniteZero.classical_elliptic_interior_estimate", "Interior elliptic estimate", "CLASSICAL_ELLIPTIC_INTERIOR.md"),
]


def dump(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, ensure_ascii=False, separators=(",", ":")) + "\n")


def extract_declarations(text, records):
    """Retain verbatim declaration lines, removing following top-level commands."""
    lines = text.splitlines()
    masked = strip_comments(text).splitlines()
    result = {}
    ordered = sorted(records, key=lambda r: r["line"])
    for i, row in enumerate(ordered):
        start = row["line"] - 1
        stop = ordered[i + 1]["line"] - 1 if i + 1 < len(ordered) else len(lines)
        for j in range(start + 1, stop):
            if re.match(r"^(?:end(?:\s|$)|namespace\s|(?:noncomputable\s+)?section(?:\s|$)|variable\s|open\s|attribute\s|#)", masked[j]):
                stop = j
                break
        while stop > start and not masked[stop - 1].strip():
            stop -= 1
        prefix = "\n".join(lines[:start]).rstrip()
        # The immediately preceding documentation comment, not a proof comment.
        doc = ""
        if prefix.endswith("-/"):
            begin = prefix.rfind("/--")
            if begin >= 0 and "-/" not in prefix[begin + 3:-2]:
                doc = prefix[begin + 3:-2].strip()
        source = "\n".join(lines[start:stop])
        proof = re.search(r":=\s*by\b", strip_comments(source)) if row["source_kind"] in {"theorem", "lemma"} else None
        result[row["name"]] = {"source": source, "doc": doc, "line": start + 1,
                                "endLine": stop, "proofOffset": proof.end() if proof else None}
    return result


def tex_excerpt(text, label):
    """Smallest enclosing numbered environment; sections get a short excerpt.

    Commented-out labels are ignored. No TeX interpretation is used for edges.
    """
    lines = text.splitlines()
    active = [re.split(r"(?<!\\)%", line, maxsplit=1)[0] for line in lines]
    matches = [i for i, line in enumerate(active) if "\\label{" + label + "}" in line]
    if len(matches) != 1:
        raise ValueError(f"Expected one active TeX label: {label}, found {matches}")
    at = matches[0]
    stack = []
    environments = {"theorem", "lemma", "proposition", "corollary", "definition", "equation", "equation*", "align", "align*", "remark"}
    for i in range(at + 1):
        for m in re.finditer(r"\\(begin|end)\{([^}]+)\}", active[i]):
            if m[1] == "begin": stack.append((m[2], i))
            elif stack and stack[-1][0] == m[2]: stack.pop()
    enclosing = next(((env, i) for env, i in reversed(stack) if env in environments), None)
    start = enclosing[1] if enclosing else at
    stop = min(len(lines), at + 12)
    if enclosing:
        end = "\\end{" + enclosing[0] + "}"
        stop = next((i + 1 for i in range(at, len(lines)) if end in active[i]), stop)
    else:
        stop = next((i for i in range(at + 1, stop) if not active[i].strip()), stop)
        # A section's opening paragraph may contain a displayed equation. Never
        # leave that environment half open at the short-excerpt boundary.
        opened = []
        for i in range(start, len(lines)):
            for m in re.finditer(r"\\(begin|end)\{([^}]+)\}", active[i]):
                if m[1] == "begin": opened.append(m[2])
                elif opened and opened[-1] == m[2]: opened.pop()
            if i + 1 >= stop and not opened:
                stop = i + 1
                break
    return {"label": label, "line": start + 1, "endLine": stop, "source": "\n".join(lines[start:stop])}


def main():
    rows = json.loads(AUDIT.read_text())
    current = helpers["source_declarations"]()
    if set(current) != {r["name"] for r in rows}:
        raise SystemExit("Declaration inventory changed. Run scripts/update_status.py first.")
    curated = json.loads((SITE / "content/reading.json").read_text())
    for entry in curated["entries"]:
        if entry["name"] not in current:
            raise SystemExit(f"Unknown curated declaration: {entry['name']}")
    admitted = {r["name"] for r in rows if r["status"] == "admitted"}
    if admitted != {a[1] for a in ADMISSIONS}:
        raise SystemExit("Admission list changed; update the website's review guide.")
    by_file = defaultdict(list)
    index = []
    for row in rows:
        source = current[row["name"]]
        if source["source_kind"] != row["source_kind"]:
            raise SystemExit(f"Declaration kind changed: {row['name']}")
        if any(dep not in current for dep in row["dependencies"]):
            raise SystemExit(f"Unknown dependency: {row['name']}")
        by_file[source["file"]].append(source)
        index.append({"name": row["name"], "kind": row["source_kind"], "file": source["file"],
                      "line": source["line"], "status": row["status"], "dependencies": row["dependencies"]})
    source_digest = hashlib.sha256()
    main_source = None
    for file, declarations in sorted(by_file.items()):
        text = (ROOT / file).read_text()
        source_digest.update(file.encode() + b"\0" + text.encode())
        extracted = extract_declarations(text, declarations)
        dump(PUBLIC / "data/modules" / (Path(file).stem + ".json"), extracted)
        if "InfiniteZero.thm_main" in extracted:
            main_source = extracted["InfiniteZero.thm_main"]
        target = PUBLIC / "sources" / file
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
    tex_file = curated["tex_file"]
    tex_text = (ROOT / tex_file).read_text()
    excerpts = {label: tex_excerpt(tex_text, label) for entry in curated["entries"] for label in entry["tex_labels"]}
    # Re-extract the theorem, rather than shipping a duplicated stale excerpt.
    curated.pop("theorem_excerpt", None)
    curated["entries"] = [{k: v for k, v in entry.items() if k not in {"audit_line", "audit_status", "line_note", "tex_refs"}} for entry in curated["entries"]]
    docs_path = PUBLIC / "sources/docs"
    docs_path.mkdir(parents=True, exist_ok=True)
    for file in (ROOT / "docs").glob("*.md"):
        shutil.copyfile(file, docs_path / file.name)
    translations = json.loads((SITE / "content/notes/manifest.json").read_text())
    for filename, translation in translations.items():
        if hashlib.sha256((ROOT / translation["source"]).read_bytes()).hexdigest() != translation["sourceSha256"]:
            raise SystemExit(f"English review copy needs synchronization after source change: {filename}")
        target = PUBLIC / "notes/en" / filename
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(SITE / "content/notes/en" / filename, target)
    tex_target = PUBLIC / "sources" / tex_file
    tex_target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(ROOT / tex_file, tex_target)
    shutil.copyfile(ROOT / "docs/dependencies.dot", PUBLIC / "sources/dependencies.dot")
    shutil.copyfile(AUDIT, PUBLIC / "sources/declarations.json")
    metadata = {"declarations": len(rows), "edges": sum(len(r["dependencies"]) for r in rows),
                "modules": len(by_file), "counts": dict(Counter(r["status"] for r in rows)),
                "auditSha256": hashlib.sha256(AUDIT.read_bytes()).hexdigest(),
                "sourceSha256": source_digest.hexdigest(), "auditSource": "docs/declarations.json",
                "leanVersion": (ROOT / "lean-toolchain").read_text().strip()}
    bootstrap = {"curated": curated, "tex": excerpts, "metadata": metadata,
                 "translatedDocuments": sorted(translations),
                 "admissions": [{"id": a, "name": n, "title": t, "document": d} for a, n, t, d in ADMISSIONS],
                 "initialRow": next(r for r in index if r["name"] == "InfiniteZero.thm_main"), "initialSource": main_source}
    dump(SITE / "content/generated/bootstrap.json", bootstrap)
    dump(PUBLIC / "data/index.json", index)
    dump(PUBLIC / "data/metadata.json", metadata)
    print(f"Website snapshot: {len(rows)} declarations, {metadata['edges']} dependency edges, {len(admitted)} admissions.")


if __name__ == "__main__":
    main()
