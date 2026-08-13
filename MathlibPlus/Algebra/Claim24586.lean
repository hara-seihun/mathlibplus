import Mathlib

namespace MathlibPlus.Algebra.Claim24586

/-- The three monic split quadratics in Claim 24586 obey the displayed
second-difference relation.  The monic normalization is made explicit. -/
theorem splitQuadraticRelation (Y : ℝ) :
    let X : Polynomial ℝ := Polynomial.X
    let C₀ : Polynomial ℝ := (X - Polynomial.C (7 * Y)) *
      (X - Polynomial.C (9 * Y))
    let C₁ : Polynomial ℝ := (X - Polynomial.C (3 * Y)) *
      (X - Polynomial.C (13 * Y))
    let C₂ : Polynomial ℝ := (X - Polynomial.C Y) *
      (X - Polynomial.C (15 * Y))
    C₀ - 2 * C₁ + C₂ = 0 := by
  dsimp
  have hfactor (a b : ℝ) :
      (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) =
        Polynomial.X ^ 2 - Polynomial.C (a + b) * Polynomial.X +
          Polynomial.C (a * b) := by
    have hXC (x : ℝ) : Polynomial.X * Polynomial.C x = x • Polynomial.X := by
      rw [mul_comm, Polynomial.C_mul']
    have hCX (x : ℝ) : Polynomial.C x * Polynomial.X = x • Polynomial.X :=
      Polynomial.C_mul' x Polynomial.X
    calc
      (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) =
          Polynomial.X * Polynomial.X - Polynomial.X * Polynomial.C b -
            Polynomial.C a * Polynomial.X + Polynomial.C a * Polynomial.C b := by ring
      _ = Polynomial.X ^ 2 - b • Polynomial.X - a • Polynomial.X +
            Polynomial.C (a * b) := by
        rw [hXC, hCX, ← Polynomial.C_mul]
        simp only [pow_two]
      _ = Polynomial.X ^ 2 - Polynomial.C (a + b) * Polynomial.X +
            Polynomial.C (a * b) := by
        rw [Polynomial.C_mul']
        rw [add_smul]
        ring
  have h0 := hfactor (7 * Y) (9 * Y)
  have h1 := hfactor (3 * Y) (13 * Y)
  have h2 := hfactor Y (15 * Y)
  have h0' :
      (Polynomial.X - Polynomial.C (7 * Y)) * (Polynomial.X - Polynomial.C (9 * Y)) =
        Polynomial.X ^ 2 - Polynomial.C (Y * 16) * Polynomial.X +
          Polynomial.C (Y ^ 2 * 63) := by
    convert h0 using 1 <;> ring
  have h1' :
      (Polynomial.X - Polynomial.C (3 * Y)) * (Polynomial.X - Polynomial.C (13 * Y)) =
        Polynomial.X ^ 2 - Polynomial.C (Y * 16) * Polynomial.X +
          Polynomial.C (Y ^ 2 * 39) := by
    convert h1 using 1 <;> ring
  have h2' :
      (Polynomial.X - Polynomial.C Y) * (Polynomial.X - Polynomial.C (15 * Y)) =
        Polynomial.X ^ 2 - Polynomial.C (Y * 16) * Polynomial.X +
          Polynomial.C (Y ^ 2 * 15) := by
    convert h2 using 1 <;> ring
  have hconst : Polynomial.C (Y ^ 2 * 63) -
      2 * Polynomial.C (Y ^ 2 * 39) + Polynomial.C (Y ^ 2 * 15) = 0 := by
    let A : ℝ := Y ^ 2 * 63
    let B : ℝ := Y ^ 2 * 39
    let C : ℝ := Y ^ 2 * 15
    have hscalar : A - 2 * B + C = 0 := by
      dsimp [A, B, C]
      ring
    have hmap := congrArg Polynomial.C hscalar
    rw [Polynomial.C_add, Polynomial.C_sub] at hmap
    have h2B : Polynomial.C (2 * B) = 2 * Polynomial.C B := by
      rw [Polynomial.C_mul, Polynomial.C_ofNat]
    rw [h2B] at hmap
    simpa [A, B, C] using hmap
  linear_combination h0' - 2 * h1' + h2' + hconst

/-- The six displayed roots are distinct away from the zero parameter. -/
theorem sixRootsPairwiseDistinct (Y : ℝ) (hY : Y ≠ 0) :
    List.Pairwise (· ≠ ·)
      [7 * Y, 9 * Y, 3 * Y, 13 * Y, Y, 15 * Y] := by
  simp only [List.pairwise_cons]
  norm_num [hY]

/-- The numerical diversity gate in Claim 24586. -/
theorem diversityGate : (6 : ℕ) ≥ 3 := by norm_num

end MathlibPlus.Algebra.Claim24586
