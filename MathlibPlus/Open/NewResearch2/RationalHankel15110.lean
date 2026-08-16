import Mathlib
import MathlibPlus.Open.NewResearch2.RationalHankel15104_15107

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.RationalHankel15110

noncomputable section

/-- The coefficient sequence of the displayed one-input, d-output
realization c_n = C A^n b. -/
def realizationCoefficient {d r : ℕ}
    (C : Matrix (Fin d) (Fin r) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (b : Fin r → ℂ) (n : ℕ) : Fin d → ℂ :=
  C.mulVec ((A ^ n).mulVec b)

/-- The block observability matrix with time block first and output channel
second in its row carrier. -/
def observabilityMatrix {d r L : ℕ}
    (C : Matrix (Fin d) (Fin r) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin L × Fin d) (Fin r) ℂ :=
  fun row state => (C * (A ^ row.1.val)) row.2 state

/-- The block controllability matrix K_K = [b, Ab, ..., A^(K-1)b]. -/
def controllabilityMatrix {r K : ℕ}
    (A : Matrix (Fin r) (Fin r) ℂ)
    (b : Fin r → ℂ) : Matrix (Fin r) (Fin K) ℂ :=
  fun state col => (A ^ col.val).mulVec b state

/-- Minimality of the finite observability and controllability windows used in
the admitted realization statement. -/
def minimalRealization {d r L K : ℕ}
    (C : Matrix (Fin d) (Fin r) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (b : Fin r → ℂ) : Prop :=
  Matrix.rank (observabilityMatrix (L := L) C A) = r ∧
    Matrix.rank (controllabilityMatrix (K := K) A b) = r

/-- Claim 15110: in a minimal realization the two exact block-Hankel
factorizations hold, and every matching invertible row/column pivot factors as
G0=XY and G1=XAY, yielding the stated similarity formula. -/
def claim_15110 : Prop :=
  ∀ (d r L K : ℕ)
    (C : Matrix (Fin d) (Fin r) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (b : Fin r → ℂ),
    r ≤ L → r ≤ K →
      minimalRealization (L := L) (K := K) C A b →
        let c : ℕ → Fin d → ℂ := realizationCoefficient C A b
        let O := observabilityMatrix (L := L) C A
        let Kmat := controllabilityMatrix (K := K) A b
        let H₀ :=
          MathlibPlus.Open.NewResearch2.RationalHankelStructure.blockHankel c 0
        let H₁ :=
          MathlibPlus.Open.NewResearch2.RationalHankelStructure.blockHankel c 1
        H₀ = O * Kmat ∧
          H₁ = O * A * Kmat ∧
          Matrix.rank O = r ∧ Matrix.rank Kmat = r ∧
            ∀ (I : Fin r → (Fin L × Fin d)) (J : Fin r → Fin K),
              Function.Injective I → Function.Injective J →
                Matrix.det (H₀.submatrix I J) ≠ 0 →
                  let G₀ := H₀.submatrix I J
                  let G₁ := H₁.submatrix I J
                  let X : Matrix (Fin r) (Fin r) ℂ :=
                    fun a state => O (I a) state
                  let Y : Matrix (Fin r) (Fin r) ℂ :=
                    fun state b' => Kmat state (J b')
                  G₀ = X * Y ∧
                    G₁ = X * A * Y ∧
                      Matrix.det X ≠ 0 ∧ Matrix.det Y ≠ 0 ∧
                        G₁ * G₀⁻¹ = X * A * X⁻¹

end

end MathlibPlus.Open.NewResearch2.RationalHankel15110
