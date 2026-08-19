import Mathlib

namespace MathlibPlus.Combinatorics.Claim31509

/-!
The finite arithmetic receipt for the raw prefilter family.  Its carrier types
are supplied with the exact source counts; the source-specific signed-edge,
disjointness, antipodal, and stationary-mask constructions are not silently
reconstructed here.
-/

def prefilterFamilyCount : Prop :=
  ∀ {E P M : Type*} [Fintype E] [Fintype P] [Fintype M],
    Fintype.card E = 140 →
    Fintype.card P = 7_119 →
    Fintype.card M = 2 ^ 10 →
    Fintype.card E = 140 ∧
      Fintype.card P = 7_119 ∧
      Fintype.card (P × M) = 7_289_856

end MathlibPlus.Combinatorics.Claim31509
