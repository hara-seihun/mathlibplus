import Mathlib

/-!
# MathlibPlus

Local research library downstream of mathlib (dependency, never a fork).

Conventions:

* `MathlibPlus.<Area>` — definitions and kernel-checked theorems. General material is
  a candidate for upstreaming to mathlib.
* `MathlibPlus.Open` — the open-problem registry: formally stated `Prop`s with **no
  proofs**. Quarantined; nothing outside `Open` may depend on anything inside it.
* Formal obstructions are ordinary theorems in their area, registered in the ledger
  keyed to (node, approach); they must target the exact registry declaration.
* The canonical identity of every mathematical object and statement in the wider
  system is its declaration name in this library (or upstream mathlib).

Admission is serial via `admission/admit.py`. Workers elaborate their own files
against the shared precompiled environment and never build the library themselves.
-/

namespace MathlibPlus

/-- Marker theorem: the library builds. Remove once real content lands. -/
theorem system_alive : 1 + 1 = 2 := rfl

end MathlibPlus
