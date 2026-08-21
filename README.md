# MathlibPlus

A Lean 4 library of machine-checked mathematics produced by an autonomous
research system: **8,243 modules, ~508k lines**, pinned to Lean `v4.33.0` and
Mathlib `v4.33.0`.

**What builds is what the kernel accepted.** `MathlibPlus.lean` imports the
8,096 modules that elaborate cleanly under `{propext, Classical.choice,
Quot.sound}`, and `lake build` builds exactly those. The remaining 147 are still
in the tree, each carrying a marker comment and a line in
[`unverified.txt`](unverified.txt) saying why the kernel has not accepted it.
They are submitted, not verified, and repairing one is what puts it back into
the library.

Every declaration here was formalized by an agent, reviewed, and kernel-checked
before it was allowed in. The 2,368 commits are that admission history, one
batch at a time.

## What is in it

- **`MathlibPlus/`** — the proved tree: theorems, definitions, disproofs, and
  reductions, organized by subject (`Algebra/`, `Combinatorics/`,
  `GroupTheory/`, `NumberTheory/`, `Analysis/`, `CategoryTheory/`, …). File
  names are admission-batch artifacts (`Claim38444.lean`), not a curated
  taxonomy — navigate by declaration name or by searching statements, not by
  browsing directories.
- **`MathlibPlus/Open/`** — the *proof-free* registry: open problems and
  conjectures written as elaborated `Prop`-valued definitions. These are
  statements the system had formalized but not proved. They typecheck; they
  are not theorems.
- **`MathlibPlus.lean`** — an umbrella module importing every library file.
- **`NumberTheory/`, `Open/`** — three files that sit outside the library tree
  and are therefore never built by `lake build MathlibPlus`. They predate the
  `MathlibPlus/` layout and are kept as provenance.

A representative entry — the whole library reads like this:

```lean
/-- A finite-group support cannot meet a left stabilizer when the support omits
identity: invariance under left multiplication by a support element forces all
positive powers of that element into the support. -/
theorem nonlinearSupport_disjoint_leftStabilizer_claim38444
    {G : Type*} [Finite G] [Group G]
    (N L : Set G) (hone : (1 : G) ∉ N)
    (hstab : ∀ a ∈ L, (fun x : G => a * x) '' N = N) :
    N ∩ L = ∅ := by
```

## The unverified 147

This is a research artifact rather than a curated library, and its defects are
published rather than hidden — but they are quarantined rather than left in the
build. [`unverified.txt`](unverified.txt) is the list, with a reason each:

- **116 modules rest on `native_decide`**, which delegates to compiled code and
  introduces `Lean.ofReduceBool`. Under this project's axiom policy that is not
  a kernel proof, so they are out of the library until their decision
  procedures are replaced.
- **19 more import one of those**, and inherit the axiom with it.
- **8 no longer elaborate** against the pinned Mathlib, from ordinary bit-rot
  during the system's own lifetime — `Unknown identifier`, `unknown tactic`, a
  missing instance.
- **2 import files that never existed.**
  `MathlibPlus/Combinatorics/Claim35734.lean` imports
  `MathlibPlus.Combinatorics.Claim31610`, and
  `MathlibPlus/Open/Research/VarianceArea60237.lean` imports
  `MathlibPlus.Open.Research.ProbabilitySupport`. Neither target is in the tree
  or anywhere in its history.
- **2 elaborate into tens of gigabytes.**
  `MathlibPlus/GroupTheory/Claim43656.lean` passes 13 GB on its own. The
  lakefile caps Lean at 8 GB per module (`-M 8192`) so one of these fails by
  itself instead of taking the build host down with it.

Declaration names are still duplicated across the tree — each module was
kernel-checked *in isolation*, so a collision only surfaces when something
imports both partners. Importing a single module is always safe; that is what
the root module and the ledger's `search_decls` are for.

There is **no `sorry` and no `axiom`** declaration anywhere in the tree.

### Keeping the two sets apart

```sh
scripts/build_set.py           # regenerate unverified.txt, the markers, and the root
scripts/build_set.py --check   # exit 1 if any of the three is out of date
```

The script derives the `native_decide` set and everything downstream of it from
the source, keeps the reasons a build discovered, writes the marker comment at
the top of every unverified module, and regenerates `MathlibPlus.lean` from
what is left. Repair a module, rerun it, and the module rejoins the library.

## Building

```sh
lake exe cache get                              # Mathlib oleans; from source it is hours
lake build MathlibPlus                          # the verified library; exits 0
lake build MathlibPlus.GroupTheory.Claim38444   # or one module
```

A full build of the verified set on a 24-core machine (Lean v4.33.0, Mathlib
from cache) is about two hours and 900 MB of oleans. `lake build MathlibPlus`
is expected to exit 0: a failure means either a repair regressed or a module
belongs in `unverified.txt`, and both are worth knowing immediately.

An unverified module can still be built by name, which is how you work on
repairing one.

Lake in this toolchain has **no `-j` flag**; `LEAN_NUM_THREADS` is what bounds
concurrent module jobs. On a memory-constrained machine set it (6 is a good
start), because the default is one `lean` per core and each one holds Mathlib.

## Provenance

MathlibPlus was the Lean tree of a private autonomous mathematics system
(2026), where an admission pipeline was the only writer: a proposed module was
kernel-checked, reviewed for fidelity against the claim it purported to prove,
checked for declaration-name collisions, and committed as part of a batch, or
rejected. That system was decommissioned in August 2026 and its research ledger
migrated to the open ledger at [math.seihun.com](https://math.seihun.com),
which is where this library's mathematics is indexed, searchable, and still
being extended.

That ledger's `check_lean` tool runs Lean 4 against the same pinned Mathlib and
returns the exact statements a proof establishes together with the axioms they
rest on — the easiest way to check anything here, or anything you build on it,
without installing a toolchain.
