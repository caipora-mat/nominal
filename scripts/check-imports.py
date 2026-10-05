#!/usr/bin/env python3
"""Fail if a supported Lean source is outside its library umbrella's closure."""

from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent
sources = {}
for library in ("Nominal", "Instances", "Examples"):
    for path in [root / f"{library}.lean", *(root / library).rglob("*.lean")]:
        sources[".".join(path.relative_to(root).with_suffix("").parts)] = path


def closure(modules):
    reached = set()
    pending = list(modules)
    while pending:
        module = pending.pop()
        if module in reached or module not in sources:
            continue
        reached.add(module)
        for line in sources[module].read_text().splitlines():
            match = re.fullmatch(r"import\s+([\w.]+)\s*", line)
            if match:
                pending.append(match.group(1))
    return reached


for roots in (("Nominal", "Instances"), ("Examples",)):
    expected = {name for name in sources if name.split(".")[0] in roots}
    missing = expected - closure(roots)
    if missing:
        raise SystemExit(f"Missing from {roots} import closure: {sorted(missing)}")
    print(f"{', '.join(roots)}: all {len(expected)} source modules reached")
