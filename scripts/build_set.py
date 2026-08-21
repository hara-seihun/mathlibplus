#!/usr/bin/env python3
"""Keep the built library equal to the verified library.

`lakefile.toml` names every module of the library as a root, so `lake build`
compiles each of them on its own rather than importing them all into one
environment — which this tree cannot do, because the same declaration name
appears in more than one module. This script decides which roots belong to the
library and which to the quarantine beside it.

A module is *unverified* when the kernel has not accepted it under this
project's axiom policy — it does not elaborate, it needs more memory than the
build allows, it rests on `native_decide` (which introduces
`Lean.ofReduceBool`), or it imports something that does. Unverified modules stay
in the tree, carry a marker comment saying so, are listed in `unverified.txt`
with the reason, and are roots of the `Unverified` library rather than of
`MathlibPlus` — so `lake build` is green, everything it produces is
kernel-clean, and a module under repair is still `lake build`-able by name.

`unverified.txt` is both input and output. Lines whose reason is a *seed*
reason are read back in as facts a build discovered; `native_decide` seeds are
re-detected from source on every run; the `-downstream` reasons are derived and
rewritten. Nothing else is remembered, so repairing a module and rerunning is
all it takes to put it back in the library.

    scripts/build_set.py            regenerate unverified.txt, markers, lakefile
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
LAKEFILE = ROOT / "lakefile.toml"
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


def render_lakefile(modules, excluded) -> str:
    verified = [m for m in sorted(modules) if m not in excluded]
    quarantined = sorted(excluded)
    roots = lambda names: "\n".join(f'  "{n}",' for n in names)
    return f"""\
# Generated by scripts/build_set.py — edit that, not this.
#
# Every module is a root of its own, because the same declaration name appears
# in more than one module here and a single umbrella environment cannot hold
# them all. `lake build` therefore means "every module of the library compiles",
# and it is expected to exit 0.
#
# MathlibPlus is what the kernel has accepted; Unverified is the {len(quarantined)} modules
# it has not, listed with a reason each in unverified.txt. Only the first is a
# default target, but a quarantined module can still be built by name while it
# is being repaired.

name = "MathlibPlus"
defaultTargets = ["MathlibPlus"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.33.0"

[[lean_lib]]
name = "MathlibPlus"
# A few modules elaborate into tens of gigabytes and will take a machine down
# with them. The cap turns that into an ordinary build error for the one module
# instead of an OOM kill for the whole build.
moreLeanArgs = ["-M", "8192"]
roots = [
{roots(verified)}
]

[[lean_lib]]
name = "Unverified"
moreLeanArgs = ["-M", "8192"]
roots = [
{roots(quarantined)}
]
"""


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
    lakefile = render_lakefile(modules, excluded)

    if args.check:
        stale = []
        if not REGISTRY.exists() or REGISTRY.read_text() != registry:
            stale.append("unverified.txt")
        if LAKEFILE.read_text() != lakefile:
            stale.append("lakefile.toml")
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
    LAKEFILE.write_text(lakefile)
    touched = apply_markers(modules, excluded)
    print(f"{len(modules) - len(excluded)} modules built, {len(excluded)} unverified "
          f"({len(touched)} marker{'' if len(touched) == 1 else 's'} changed)")
    for reason, count in sorted(collections.Counter(excluded.values()).items()):
        print(f"  {reason:<20} {count}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
