import MathlibPlus.Open.NewResearch2.RationalHankel15104_15107

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.NewResearch2.RationalHankelCertification15117

noncomputable section

open MathlibPlus.Open.NewResearch2.RationalHankelStructure

/-- The Euclidean norm on a finite complex vector. -/
def euclideanNorm {ι : Type*} [Fintype ι] (x : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖x i‖ ^ 2)

/-- The induced Euclidean/operator 2-norm of a finite complex matrix. -/
noncomputable def operatorNorm2 {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : ℝ :=
  sSup {s : ℝ | ∃ x : n → ℂ,
    euclideanNorm x = 1 ∧ s = euclideanNorm (M.mulVec x)}

/-- Singular values of a finite complex matrix, with the zero-based index of
Mathlib's finite-support singular-value sequence. -/
noncomputable def singularValue {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (M : Matrix m n ℂ) (k : ℕ) : ℝ :=
  (Matrix.toEuclideanLin M).singularValues k

/-- A block-Hankel window at an arbitrary starting coefficient. -/
def windowBlockHankel {d L K : ℕ} (c : ℕ → Fin d → ℂ)
    (n₀ ν : ℕ) : Matrix (Fin L × Fin d) (Fin K) ℂ :=
  blockHankel (fun n i => c (n₀ + n) i) ν

/-- The finite index set on which the rectangular matrix has its singular
values. -/
def singularIndexCount (d L K : ℕ) : ℕ :=
  min (Fintype.card (Fin L × Fin d)) (Fintype.card (Fin K))

/-- Certified rank detection under noise.  The exact sequence is the Taylor
coefficient sequence represented by the reduced rational numerator and
minimal denominator; the conclusion counts the thresholded singular values
and bounds every remaining finite singular value. -/
def claim_15117 : Prop :=
  ∀ (d : ℕ) (P : Fin d → Polynomial ℂ) (Q : Polynomial ℂ),
    Q ≠ 0 → Q.coeff 0 = 1 →
      (∀ i : Fin d, (P i).degree < Q.degree) →
      let Qstar := reducedDenominator P Q
      let Pstar := reducedNumerator P Q
      let r := Qstar.natDegree
      ∀ (L K n₀ : ℕ) (ctilde : ℕ → Fin d → ℂ) (ε : ℕ → ℝ),
        0 < r → r ≤ L → r ≤ K →
        (∀ n : ℕ,
          0 ≤ ε n ∧
            euclideanNorm
              (fun i : Fin d =>
                ctilde n i - vectorTaylorCoeff Pstar Qstar n i) ≤ ε n) →
        let HR := windowBlockHankel (L := L) (K := K)
          (vectorTaylorCoeff Pstar Qstar) n₀ 0
        let Htilde := windowBlockHankel (L := L) (K := K) ctilde n₀ 0
        let η₀ := Real.sqrt
          (∑ i : Fin L, ∑ j : Fin K,
            ε (n₀ + i.val + j.val) ^ 2)
        Matrix.rank HR = r →
        operatorNorm2 (Htilde - HR) ≤ η₀ →
        singularValue HR (r - 1) > 3 * η₀ →
        (Finset.filter
            (fun k : Fin (singularIndexCount d L K) =>
              2 * η₀ < singularValue Htilde k.val)
            Finset.univ).card = r ∧
          (∀ k : Fin (singularIndexCount d L K),
            r ≤ k.val → singularValue Htilde k.val ≤ η₀)

end
end MathlibPlus.Open.NewResearch2.RationalHankelCertification15117
