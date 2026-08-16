import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.MatchingPencilError15118

noncomputable section

/-- Euclidean norm of a finite complex vector. -/
noncomputable def vectorTwoNorm {d : ℕ} (v : Fin d → ℂ) : ℝ :=
  Real.sqrt (∑ i : Fin d, ‖v i‖ ^ 2)

/-- The spectral operator norm on a finite complex matrix. -/
noncomputable def spectralTwoNorm {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  sSup (Set.range (fun v : {v : Fin m → ℂ // vectorTwoNorm v = 1} =>
    vectorTwoNorm (Matrix.mulVec A v.1)))

/-- The smallest singular value in the same Euclidean variational convention. -/
noncomputable def smallestSingularValue {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  sInf (Set.range (fun v : {v : Fin m → ℂ // vectorTwoNorm v = 1} =>
    vectorTwoNorm (Matrix.mulVec A v.1)))

/-- The block Hankel matrix whose entries are vector Taylor coefficients. -/
def blockHankel {d L K : ℕ} (c : ℕ → Fin d → ℂ)
    (n₀ ν : ℕ) : Matrix (Fin L × Fin d) (Fin K) ℂ :=
  fun ij j => c (n₀ + ij.1.val + j.val + ν) ij.2

/-- The certified matching-pencil error bound.  The observed and exact pivots
are extracted from the same matching block-Hankel rows and columns; the exact
pivot is consequently a conclusion, rather than supplied exact data. -/
def claim_15118_certified_matching_pencil_error : Prop :=
  ∀ (d r L K n₀ : ℕ),
    0 < r →
    r ≤ L →
    r ≤ K →
    ∀ (cExact cObserved : ℕ → Fin d → ℂ)
      (ε : ℕ → ℝ)
      (I : Fin r → Fin L × Fin d)
      (J : Fin r → Fin K),
      Function.Injective I →
      Function.Injective J →
      Matrix.rank (blockHankel (L := L) (K := K) cExact n₀ 0) = r →
      (∀ n : ℕ, 0 ≤ ε n) →
      (∀ n : ℕ, vectorTwoNorm (fun a =>
        cObserved n a - cExact n a) ≤ ε n) →
      let H₀ := blockHankel cExact n₀ 0
      let H₁ := blockHankel cExact n₀ 1
      let Htilde₀ := blockHankel cObserved n₀ 0
      let Htilde₁ := blockHankel cObserved n₀ 1
      let G₀ : Matrix (Fin r) (Fin r) ℂ := fun a b => H₀ (I a) (J b)
      let G₁ : Matrix (Fin r) (Fin r) ℂ := fun a b => H₁ (I a) (J b)
      let Gtilde₀ : Matrix (Fin r) (Fin r) ℂ := fun a b => Htilde₀ (I a) (J b)
      let Gtilde₁ : Matrix (Fin r) (Fin r) ℂ := fun a b => Htilde₁ (I a) (J b)
      let η₀ : ℝ := Real.sqrt (∑ i : Fin L, ∑ j : Fin K,
        ε (n₀ + i.val + j.val) ^ 2)
      let η₁ : ℝ := Real.sqrt (∑ i : Fin L, ∑ j : Fin K,
        ε (n₀ + i.val + j.val + 1) ^ 2)
      let sigmaTilde : ℝ := smallestSingularValue Gtilde₀
      sigmaTilde > η₀ →
      ∃ A : Matrix (Fin r) (Fin r) ℂ,
        Matrix.det Gtilde₀ ≠ 0 ∧
          Matrix.det G₀ ≠ 0 ∧
            A = G₁ * G₀⁻¹ ∧
              let Ahat : Matrix (Fin r) (Fin r) ℂ := Gtilde₁ * Gtilde₀⁻¹
              let eA : ℝ :=
                (η₁ + η₀ * spectralTwoNorm Ahat) / (sigmaTilde - η₀)
              spectralTwoNorm (Ahat - A) ≤ eA

end
end MathlibPlus.Open.ResearchFormalization.MatchingPencilError15118
