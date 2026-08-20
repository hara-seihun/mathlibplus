# MathlibPlus

A Lean 4 library of machine-checked mathematics produced by an autonomous
research system: **8,246 modules, 49,534 declarations, ~508k lines**, pinned to
Lean `v4.33.0` and Mathlib `v4.33.0`.

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
- **`NumberTheory/`, `Open/`** — two files predating the `MathlibPlus/`
  namespace layout.

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

## Honest state of the tree

This is a research artifact, not a curated library, and it is published with
its defects visible:

- **The umbrella does not build.** `MathlibPlus.lean` imports everything, and
  **164 declaration names are duplicated** across modules. Each module was
  kernel-checked *in isolation*, so a name collision only surfaces when
  something imports both partners. Import the specific modules you want.
- **Roughly 1–2% of modules no longer elaborate in isolation** against the
  pinned Mathlib, from ordinary bit-rot during the system's own lifetime.
- **118 files use `native_decide`**, which delegates to compiled code and
  introduces `Lean.ofReduceBool`. Anything downstream of them inherits that
  axiom. Check `#print axioms` before trusting a result for a purpose that
  cares.
- There is **no `sorry` and no `axiom`** declaration anywhere in the tree.

## Building

```sh
lake exe cache get     # Mathlib oleans; building Mathlib from source takes hours
lake build MathlibPlus.GroupTheory.Claim38444   # a module, not the umbrella
```

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
