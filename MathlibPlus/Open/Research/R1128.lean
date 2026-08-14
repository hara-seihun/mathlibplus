import Mathlib

namespace MathlibPlus.Open.Research.R1128

/-- A support-four `𝔽₇` translation profile on the 39 nonidentity base
fibres. -/
def supportFourProfile (f : Fin 39 → ZMod 7) : Prop :=
  Set.ncard {i : Fin 39 | f i ≠ 0} = 4

/-- Canonical representative of a global `𝔽₇ˣ`-scalar orbit: the first
nonzero coordinate is normalized to one. -/
def scalarNormalizedProfile (f : Fin 39 → ZMod 7) : Prop :=
  supportFourProfile f ∧
    ∃ i : Fin 39, f i = 1 ∧ ∀ j : Fin 39, j < i → f j = 0

abbrev ScalarNormalizedSupportFour :=
  {f : Fin 39 → ZMod 7 // scalarNormalizedProfile f}

noncomputable instance : Fintype ScalarNormalizedSupportFour :=
  Fintype.ofFinite _

/-- Scalar-normalized support-four profiles give the quotient by global
`𝔽₇ˣ` multiplication, with the exact packet count. -/
def scalarNormalizedSupportFourProfileCount : Prop :=
  (∀ f : Fin 39 → ZMod 7, supportFourProfile f →
    ∃! g : ScalarNormalizedSupportFour,
      ∃ u : (ZMod 7)ˣ, ∀ i : Fin 39,
        g.1 i = (u : ZMod 7) * f i) ∧
  Fintype.card ScalarNormalizedSupportFour =
    Nat.choose 39 4 * 6 ^ 3 ∧
  Nat.choose 39 4 * 6 ^ 3 = 17766216

end MathlibPlus.Open.Research.R1128
