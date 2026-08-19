import MathlibPlus.Open.ResearchFormalization.R0503Claim26003

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0503Claim25996

noncomputable section

open MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001

abbrev Index := MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001.Index
abbrev Composition := MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001.Composition
abbrev IntervalFn (N : ℕ) := Index N → ℚ

def antisymmetric25996 {N : ℕ} (v : IntervalFn N) : Prop :=
  ∀ t : Index N, v t = -v (reflectIndex N t)

def cubicAtMost25996 {N : ℕ} (v : IntervalFn N) : Prop :=
  ∃ c : Fin 4 → ℚ,
    ∀ t : Index N,
      v t = ∑ i : Fin 4, c i * (t.1 : ℚ) ^ i.1

def symmetricQuadraticDirection25996
    (N : ℕ) (C lam : ℚ) : IntervalFn N :=
  fun t =>
    (C + lam * (t.1 : ℚ) * ((t.1 : ℚ) - (N : ℚ))) / 2

def normalizedPairFunction25996
    (N : ℕ) (C lam : ℚ) (h : IntervalFn N) : IntervalFn N :=
  fun t => h t - symmetricQuadraticDirection25996 N C lam t

def antisymmetricResidueFunction25996
    (N : ℕ) (C lam : ℚ) (h k : IntervalFn N) : IntervalFn N :=
  let h₀ := normalizedPairFunction25996 N C lam h
  fun t => h₀ t + 2 * k t + k (reflectIndex N t)

def pairResidue25996
    (N : ℕ) (v : IntervalFn N) (μ : Composition 5 N) : ℚ :=
  blockSum 2 v μ - blockSum 1 v μ

/-- Claim 25996: after the valid symmetric quadratic direction is removed
    pointwise from the pair function, the remaining pair residue is an
    antisymmetric cubic and its two-zero/five-active functional is constant. -/
def pairResidueAntisymmetricCubic_claim25996 : Prop :=
  ∀ (N : ℕ), 7 ≤ N →
    ∀ (f h k : IntervalFn N),
      sevenFactorAnnihilator N f h k →
        ∃ C lam : ℚ,
          (∀ t : Index N,
            h t + h (reflectIndex N t) + 3 * k t +
                3 * k (reflectIndex N t) =
              C + lam * (t.1 : ℚ) * ((t.1 : ℚ) - (N : ℚ))) ∧
          let v := antisymmetricResidueFunction25996 N C lam h k
          antisymmetric25996 v ∧
            cubicAtMost25996 v ∧
              ∃ c : ℚ, ∀ μ : Composition 5 N,
                pairResidue25996 N v μ = c

end

end MathlibPlus.Open.ResearchFormalization.R0503Claim25996
