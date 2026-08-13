import MathlibPlus.LinearAlgebra.Claim10825

namespace MathlibPlus.LinearAlgebra

/-- The two-vector Jordan relation gives the exact all-depth paired recurrence. -/
theorem allDepthPairedRecurrence_claim10826
    {R V : Type*} [Field R] [AddCommGroup V] [Module R V]
    (A : V →ₗ[R] V) (Khat P : V) (Delta a b : R)
    (hK : A Khat = Delta • Khat + (a * b) • P)
    (hP : A P = Delta • P) :
    ∀ m : ℕ, 1 ≤ m →
      (A ^ m) Khat =
        Delta ^ m • Khat +
          ((m : R) * a * b * Delta ^ (m - 1)) • P := by
  have hPpow : ∀ m : ℕ, (A ^ m) P = Delta ^ m • P := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply, hP,
        map_smul, ih]
      rw [smul_smul, pow_succ, mul_comm]
  have hpos : ∀ k : ℕ,
      (A ^ (k + 1)) Khat =
        Delta ^ (k + 1) • Khat +
          (((k + 1 : ℕ) : R) * a * b * Delta ^ k) • P := by
    intro k
    induction k with
    | zero =>
        simpa [pow_one, one_smul, mul_smul] using hK
    | succ k ih =>
        rw [show k + 1 + 1 = (k + 1) + 1 by omega,
          pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply, hK,
          map_add, map_smul, map_smul, ih, hPpow]
        simp only [smul_smul, pow_succ, Nat.cast_add, Nat.cast_one]
        module
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simpa [Nat.succ_eq_add_one] using hpos k

end MathlibPlus.LinearAlgebra
