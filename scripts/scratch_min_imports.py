"""Scratch only: settle minimal imports for SixExponentials one dependency layer at a time.

Each file starts with `public import Mathlib`, its project imports and a trailing
`#min_imports`. Layers are built bottom-up; after a layer builds, each of its files
gets the import block Mathlib's `#min_imports` reports, so the next layer is measured
against final imports rather than against all of Mathlib.
"""

import json
import re
import subprocess
import sys
from pathlib import Path

PROJECT = "SixExponentials"
DIR = Path("LeanPool") / PROJECT
LAYERS = [
    ["Defs", "Liouville", "HouseBounds", "SiegelLemma", "CauchyEstimate"],
    ["CharacterIndependence", "AuxiliaryFunction", "GridEstimate"],
    ["DescentStep"],
    ["NumberField"],
    ["Main"],
    ["Statement"],
]
DELETE = {"̵", "̶", "̸"}
INSERT = {"̲"}
HEADER = re.compile(
    rf"^(?:warning|info): (?:\./)?LeanPool/{PROJECT}/(\w+)\.lean:\d+:\d+: "
    r"Imports (?:can be reduced|are minimal, but can be normalized):"
)


def decode(text: str) -> str:
    out, i = [], 0
    while i < len(text):
        ch = text[i]
        mark = text[i + 1] if i + 1 < len(text) else ""
        if mark in DELETE:
            i += 2
            continue
        if mark in INSERT:
            out.append(ch)
            i += 2
            continue
        if ch not in DELETE and ch not in INSERT:
            out.append(ch)
        i += 1
    return "".join(out)


def suggestions(log: str) -> dict[str, list[str]]:
    lines = log.split("\n")
    found = {}
    for i, line in enumerate(lines):
        match = HEADER.match(line)
        if not match:
            continue
        body, j = [], i + 1
        while j < len(lines) and lines[j].startswith("  "):
            body.append(lines[j][2:])
            j += 1
        found[match.group(1)] = [x.strip() for x in decode("\n".join(body)).split("\n") if x.strip()]
    return found


def rewrite(name: str, block: list[str]) -> None:
    path = DIR / f"{name}.lean"
    lines = path.read_text(encoding="utf-8").split("\n")
    idx = [i for i, l in enumerate(lines) if re.match(r"^(public )?import ", l)]
    lines[idx[0] : idx[-1] + 1] = block
    text = "\n".join(lines)
    text = re.sub(r"\n+#min_imports\n*\Z", "\n", text)
    path.write_text(text, encoding="utf-8")


def main() -> int:
    final = {}
    for layer in LAYERS:
        modules = [f"LeanPool.{PROJECT}.{m}" for m in layer]
        proc = subprocess.run(
            [str(Path.home() / ".elan/bin/lake"), "build", *modules],
            capture_output=True, text=True,
        )
        log = proc.stdout + proc.stderr
        found = suggestions(log)
        missing = [m for m in layer if m not in found]
        if missing:
            print(log[-6000:])
            print(f"no #min_imports suggestion for {missing}", file=sys.stderr)
            return 1
        for name in layer:
            rewrite(name, found[name])
            final[name] = found[name]
            print(f"{name}: {found[name]}")
    Path("six-imports.json").write_text(json.dumps(final, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
