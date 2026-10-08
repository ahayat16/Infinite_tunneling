#!/usr/bin/env python3
"""Keep the static reader portable to a subdirectory (including GitHub Pages).

Vinext beta.5 prepends '/' to some already-relative Vite asset references in
its RSC/preload manifest. Normalize only that exact generated prefix. The
source application and its module imports are unchanged.
"""
from pathlib import Path
import re

OUT = Path(__file__).resolve().parents[1] / "dist/client"


def main():
    index = OUT / "index.html"
    if not index.exists():
        raise SystemExit("Static prerender did not produce dist/client/index.html")
    count = 0
    for path in OUT.rglob("*"):
        if path.suffix in {".html", ".rsc", ".json", ".js"}:
            source = path.read_text()
            fixed = source.replace("/./_next/", "./_next/")
            if fixed != source:
                path.write_text(fixed)
                count += 1
    for url in re.findall(r'(?:src|href)="([^" ]+\.(?:js|css))"', index.read_text()):
        if not url.startswith("./"):
            raise SystemExit(f"Non-portable static asset URL: {url}")
        if not (OUT / url).is_file():
            raise SystemExit(f"Missing static asset: {url}")
    (OUT / ".nojekyll").touch()
    print(f"Static export checked; normalized asset references in {count} files.")


if __name__ == "__main__":
    main()
