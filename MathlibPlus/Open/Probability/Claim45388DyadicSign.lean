import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Probability.Claim45388DyadicSign

abbrev SignTriple := Fin 3 → ℤ

def signPatterns : Fin 8 → SignTriple :=
  ![ ![-1, -1, -1], ![-1, -1, 1], ![-1, 1, -1], ![-1, 1, 1],
     ![1, -1, -1], ![1, -1, 1], ![1, 1, -1], ![1, 1, 1] ]

def dyadicWeights : Fin 8 → ℚ :=
  ![29 / 64, 1 / 64, 1 / 64, 1 / 64,
    1 / 64, 1 / 64, 1 / 64, 29 / 64]

noncomputable def dyadicMass (x : SignTriple) : ℚ :=
  ∑ i : Fin 8, if signPatterns i = x then dyadicWeights i else 0

def signMean (x : SignTriple) : ℚ :=
  ((x 0 : ℤ) : ℚ) / 3 +
    ((x 1 : ℤ) : ℚ) / 3 +
    ((x 2 : ℤ) : ℚ) / 3

/-- Claim 45388: the exact eight-point dyadic sign law, its mean coordinate,
and invariance under coordinate permutations and simultaneous sign reversal. -/
def claim45388_exactDyadicSignLaw : Prop :=
  (∑ i : Fin 8, dyadicWeights i = 1) ∧
    (∀ i : Fin 8, dyadicMass (signPatterns i) = dyadicWeights i) ∧
    (∀ x : SignTriple, dyadicMass x ≠ 0 →
      ∃ i : Fin 8, x = signPatterns i) ∧
    (∀ σ : Equiv.Perm (Fin 3), ∀ x : SignTriple,
      dyadicMass (x ∘ σ) = dyadicMass x) ∧
    (∀ x : SignTriple,
      dyadicMass (fun i => -x i) = dyadicMass x)

end MathlibPlus.Open.Probability.Claim45388DyadicSign
