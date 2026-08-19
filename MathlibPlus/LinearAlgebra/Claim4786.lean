import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim4786

noncomputable section

/-- Claim 4786: the explicit source-coordinate map has a bijective triangular
matrix whenever the zeroth source coordinate is positive. -/
def source_coordinate_map_bijective_claim4786 : Prop :=
  ∀ (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
      (N : ℕ),
    ∀ hN : 0 < N,
      ∀ h : Fin N → K,
        0 < h ⟨0, Nat.zero_lt_of_lt hN⟩ →
        Function.Bijective
          (fun c : Fin N → K =>
            fun k : Fin N =>
              ∑ i : Fin N,
                c i *
                  if k.1 ≤ i.1 then
                    h ⟨i.1 - k.1,
                      lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
                  else 0)

end

end MathlibPlus.LinearAlgebra.Claim4786
