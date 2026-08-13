import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-- The cardinality and density consequence of adjoining one point outside a
half-sized subset in the coordinate model of a binary vector space.  The
source's affine-hyperplane structure is not needed for this consequence and is
therefore left outside the formal core. -/
theorem selectedSetDensity_claim36594
    {r : ℕ} (hr : 0 < r) (A : Set (Fin r → ZMod 2))
    (m : Fin r → ZMod 2)
    (hA : A.ncard = 2 ^ (r - 1)) (hm : m ∉ A) :
    (Set.ncard (A ∪ {m}) = 2 ^ (r - 1) + 1) ∧
      (((Set.ncard (A ∪ {m}) : ℚ) /
          (Fintype.card (Fin r → ZMod 2) : ℚ)) - (1 / 2 : ℚ) =
        1 / (Fintype.card (Fin r → ZMod 2) : ℚ)) := by
  have hUnion : A ∪ {m} = insert m A := by
    ext x
    simp [eq_comm]
  have hS : Set.ncard (A ∪ {m}) = A.ncard + 1 := by
    rw [hUnion]
    exact Set.ncard_insert_of_notMem hm
  have hcard : Fintype.card (Fin r → ZMod 2) = 2 ^ r := by
    simp
  have hrpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    have hr' : r = (r - 1) + 1 := by omega
    calc
      2 ^ r = 2 ^ ((r - 1) + 1) := by
        congr 1
      _ = 2 ^ (r - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (r - 1) := Nat.mul_comm _ _
  constructor
  · rw [hS, hA]
  · rw [hS, hA, hcard]
    have hpowQ : ((2 ^ r : ℕ) : ℚ) =
        2 * ((2 ^ (r - 1) : ℕ) : ℚ) := by
      exact_mod_cast hrpow
    rw [hpowQ]
    field_simp
    norm_num [Nat.cast_add]

end MathlibPlus.Combinatorics
