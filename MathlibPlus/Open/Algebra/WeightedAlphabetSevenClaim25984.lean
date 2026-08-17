import Mathlib
import MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim25984

noncomputable section

abbrev Index := MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001.Index
abbrev Composition := MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001.Composition

private def reflectIndex (N : ℕ) (t : Index N) : Index N :=
  ⟨N - t.1, Nat.sub_le _ _⟩

/-- The six-part middle residual on the same fixed-total subset-sum carrier as
The six-factor statement. -/
def middleResidual (N : ℕ) (s : Index N → ℚ) (μ : Composition 6 N) : ℚ :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001.blockSum 3 s μ -
    2 * MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001.blockSum 2 s μ +
      2 * MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001.blockSum 1 s μ

private def symmetricPart (N : ℕ) (k : Index N → ℚ) : Index N → ℚ :=
  fun t => (k t + k (reflectIndex N t)) / 2

private def antisymmetricPart (N : ℕ) (k : Index N → ℚ) : Index N → ℚ :=
  fun t => (k t - k (reflectIndex N t)) / 2

/-- Claim 25984: the symmetric part of the triple block, after the lower
seven-factor directions have been removed, is the fixed-total six-factor
middle residual and hence has the reflective quartic normal form. -/
def claim25984 : Prop :=
  ∀ (N : ℕ), 7 ≤ N →
    ∀ (f h k : Index N → ℚ),
      MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001.sevenFactorAnnihilator
          N f h k →
        let s := symmetricPart N k
        let a := antisymmetricPart N k
        (∀ t, k t = s t + a t) ∧
          (∀ t, s (reflectIndex N t) = s t) ∧
          (∀ t, a (reflectIndex N t) = -a t) ∧
          (∃ C : ℚ,
            (∀ μ : Composition 6 N, middleResidual N s μ = C) ∧
              (∃ (d₀ d₁ d₂ : ℚ),
                ∀ t, s t =
                  d₀ + d₁ * (t.1 : ℚ) * ((N - t.1 : ℕ) : ℚ) +
                    d₂ * ((t.1 : ℚ) * ((N - t.1 : ℕ) : ℚ)) ^ 2))

end

end MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim25984
