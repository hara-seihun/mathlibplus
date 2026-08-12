import Mathlib

namespace MathlibPlus.GroupTheory

/--
The generator-level centrality of the half-turn in the D₁₂ presentation from
admitted claim 26787.  The extracted claim supplies the presentation
relations; commuting with both generators is the precise centrality statement
needed here.
-/
theorem dihedralHalfTurn_claim26787
    {G : Type*} [Group G] (r s : G)
    (hr : r ^ 6 = 1) (hs : s ^ 2 = 1)
    (hrel : s * r * s = r⁻¹) :
    Commute (r ^ 3) r ∧ Commute (r ^ 3) s := by
  have hss : s * s = 1 := by simpa [pow_two] using hs
  have hsr : s * r = r⁻¹ * s := by
    calc
      s * r = s * r * (s * s) := by rw [hss]; simp
      _ = (s * r * s) * s := by group
      _ = r⁻¹ * s := by rw [hrel]
  have hpow : ∀ n : ℕ, s * r ^ n = (r⁻¹) ^ n * s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          s * r ^ (n + 1) = (s * r ^ n) * r := by simp [pow_succ, mul_assoc]
          _ = ((r⁻¹) ^ n * s) * r := by rw [ih]
          _ = (r⁻¹) ^ n * (s * r) := by simp [mul_assoc]
          _ = (r⁻¹) ^ n * (r⁻¹ * s) := by rw [hsr]
          _ = (r⁻¹) ^ (n + 1) * s := by rw [pow_succ]; simp [mul_assoc]
  have hinv : r⁻¹ = r ^ 5 := by
    calc
      r⁻¹ = r⁻¹ * 1 := by simp
      _ = r⁻¹ * r ^ 6 := by rw [hr]
      _ = r ^ 5 := by group
  have hinvpow : (r⁻¹) ^ 3 = r ^ 3 := by
    rw [hinv, ← pow_mul]
    rw [show 5 * 3 = 6 * 2 + 3 by norm_num, pow_add, pow_mul, hr]
    simp
  constructor
  · exact (Commute.refl r).pow_left 3
  · have hpow3 := hpow 3
    rw [hinvpow] at hpow3
    exact hpow3.symm

end MathlibPlus.GroupTheory
