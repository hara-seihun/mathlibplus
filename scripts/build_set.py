#!/usr/bin/env python3
"""Keep the built library equal to the verified library.

`MathlibPlus.lean` is the library root: `lake build` builds exactly the modules
it imports, transitively. This script decides what belongs in that import list.

A module is *unverified* when the kernel has not accepted it under this
project's axiom policy — it does not elaborate, it needs more memory than the
build allows, it rests on `native_decide` (which introduces
`Lean.ofReduceBool`), or it imports something that does. Unverified modules stay
in the tree, carry a marker comment saying so, are listed in `unverified.txt`
with the reason, and are left out of the root module, so `lake build` is green
and everything it produces is kernel-clean.

`unverified.txt` is both input and output. Lines whose reason is a *seed*
reason are read back in as facts a build discovered; `native_decide` seeds are
re-detected from source on every run; the `-downstream` reasons are derived and
rewritten. Nothing else is remembered, so repairing a module and rerunning is
all it takes to put it back in the library.

    scripts/build_set.py            regenerate unverified.txt, markers, root
    scripts/build_set.py --check    exit 1 if any of the three is out of date
    scripts/build_set.py --add MOD=REASON ...   record a new seed first
"""
from __future__ import annotations

import argparse
import collections
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIB = ROOT / "MathlibPlus"
ROOT_MODULE = ROOT / "MathlibPlus.lean"
REGISTRY = ROOT / "unverified.txt"

# Reasons a build (or a human reading its log) discovers and this script keeps.
SEED_REASONS = {
    "does-not-elaborate": "does not elaborate against the pinned Mathlib",
    "missing-import": "imports a module that is not in the tree",
    "too-heavy": "needs more memory than the build allows",
}
# Reasons this script derives itself, and therefore always rewrites.
DERIVED_REASONS = {
    "native-decide": "rests on native_decide, so it carries Lean.ofReduceBool",
    "downstream": "imports an unverified module",
}
MARKER = "-- UNVERIFIED ({reason}): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt."
MARKER_RE = re.compile(r"^-- UNVERIFIED \([a-z-]+\):.*\n", re.MULTILINE)
NATIVE_RE = re.compile(r"\bnative_decide\b")


def module_of(path: pathlib.Path) -> str:
    return str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")


def load_tree() -> tuple[dict[str, pathlib.Path], dict[str, list[str]]]:
    modules = {module_of(p): p for p in sorted(LIB.rglob("*.lean"))}
    imports: dict[str, list[str]] = {}
    for name, path in modules.items():
        text = path.read_text(errors="replace")
        imports[name] = [
            line.split()[1]
            for line in text.splitlines()
            if line.startswith("import ") and line.split()[1].startswith("MathlibPlus")
        ]
    return modules, imports


def read_seeds() -> dict[str, str]:
    seeds: dict[str, str] = {}
    if REGISTRY.exists():
        for line in REGISTRY.read_text().splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            module, _, reason = line.partition("\t")
            if reason.strip() in SEED_REASONS:
                seeds[module.strip()] = reason.strip()
    return seeds


def compute(modules, imports, seeds) -> dict[str, str]:
    """module -> reason, seeds first, then everything that imports them."""
    excluded: dict[str, str] = {}
    for module, reason in seeds.items():
        if module in modules:
            excluded[module] = reason
    for module, path in modules.items():
        if module in excluded:
            continue
        body = MARKER_RE.sub("", path.read_text(errors="replace"))
        if NATIVE_RE.search(body):
            excluded[module] = "native-decide"
    # A module that imports something unverified inherits its status.
    importers = collections.defaultdict(set)
    for module, imported in imports.items():
        for target in imported:
            importers[target].add(module)
    stack = list(excluded)
    while stack:
        for downstream in importers.get(stack.pop(), ()):
            if downstream not in excluded:
                excluded[downstream] = "downstream"
                stack.append(downstream)
    # An import of a module that does not exist at all is its own defect.
    for module, imported in imports.items():
        if module in excluded:
            continue
        if any(target not in modules for target in imported):
            excluded[module] = "missing-import"
    return excluded


def render_registry(excluded: dict[str, str]) -> str:
    by_reason = collections.Counter(excluded.values())
    lines = [
        "# Modules that are in this tree but not in the built library.",
        "#",
        "# Regenerate with scripts/build_set.py. Each line is a module and why the",
        "# kernel has not accepted it; every one of them is a repair worth making,",
        "# and repairing one is what puts it back into MathlibPlus.lean.",
        "#",
    ]
    for reason, blurb in {**SEED_REASONS, **DERIVED_REASONS}.items():
        lines.append(f"#   {reason:<20} {blurb} ({by_reason.get(reason, 0)})")
    lines.append("#")
    lines.append(f"# {len(excluded)} unverified modules.")
    lines.append("")
    for module in sorted(excluded):
        lines.append(f"{module}\t{excluded[module]}")
    return "\n".join(lines) + "\n"


def render_root(modules, excluded) -> str:
    header = [
        "-- MathlibPlus root module: every module the kernel has accepted.",
        "--",
        "-- Generated by scripts/build_set.py. `lake build` builds exactly this",
        "-- import list, so what the library ships is what elaborates cleanly under",
        "-- {propext, Classical.choice, Quot.sound}. Modules left out are listed,",
        "-- with the reason, in unverified.txt.",
        "",
    ]
    body = [f"import {m}" for m in sorted(modules) if m not in excluded]
    return "\n".join(header + body) + "\n"


def apply_markers(modules, excluded) -> list[str]:
    touched = []
    for module, path in modules.items():
        text = path.read_text(errors="replace")
        stripped = MARKER_RE.sub("", text)
        wanted = (
            MARKER.format(reason=excluded[module]) + "\n" + stripped
            if module in excluded
            else stripped
        )
        if wanted != text:
            path.write_text(wanted)
            touched.append(module)
    return touched


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="report staleness, change nothing")
    parser.add_argument("--add", nargs="*", default=[], metavar="MOD=REASON",
                        help=f"record a seed before regenerating; reasons: {', '.join(SEED_REASONS)}")
    args = parser.parse_args()

    modules, imports = load_tree()
    seeds = read_seeds()
    for item in args.add:
        module, _, reason = item.partition("=")
        if reason not in SEED_REASONS:
            parser.error(f"{reason!r} is not a seed reason ({', '.join(SEED_REASONS)})")
        seeds[module] = reason

    excluded = compute(modules, imports, seeds)
    registry = render_registry(excluded)
    root = render_root(modules, excluded)

    if args.check:
        stale = []
        if not REGISTRY.exists() or REGISTRY.read_text() != registry:
            stale.append("unverified.txt")
        if ROOT_MODULE.read_text() != root:
            stale.append("MathlibPlus.lean")
        for module, path in modules.items():
            text = path.read_text(errors="replace")
            has = bool(MARKER_RE.match(text))
            if has != (module in excluded):
                stale.append(f"marker in {module}")
        if stale:
            print("out of date: " + ", ".join(stale[:10]) + ("…" if len(stale) > 10 else ""))
            return 1
        print(f"build set is current: {len(modules) - len(excluded)} built, {len(excluded)} unverified")
        return 0

    REGISTRY.write_text(registry)
    ROOT_MODULE.write_text(root)
    touched = apply_markers(modules, excluded)
    print(f"{len(modules) - len(excluded)} modules built, {len(excluded)} unverified "
          f"({len(touched)} marker{'' if len(touched) == 1 else 's'} changed)")
    for reason, count in sorted(collections.Counter(excluded.values()).items()):
        print(f"  {reason:<20} {count}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
