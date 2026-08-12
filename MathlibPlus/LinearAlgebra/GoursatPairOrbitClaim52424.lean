import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 52424: the orbit of the zero ordered pair under the shared and
block-dependent translations is exactly the Goursat image relation. -/
theorem goursatPairOrbit_claim52424
    {p : ℕ} [Fact p.Prime]
    {A W Block : Type*}
    [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup W] [Module (ZMod p) W]
    [Fintype Block] [DecidableEq Block]
    [FiniteDimensional (ZMod p) A] [FiniteDimensional (ZMod p) W]
    (φ : Block → W →ₗ[ZMod p] A) (b c : Block) (_hbc : b ≠ c) :
    {q : A × A | ∃ a : A, ∃ w : W,
      q = (a + φ b w, a + φ c w)} =
      {q : A × A | q.1 - q.2 ∈ LinearMap.range (φ b - φ c)} := by
  ext q
  constructor
  · rintro ⟨a, w, rfl⟩
    refine ⟨w, ?_⟩
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · intro hq
    rcases hq with ⟨w, hw⟩
    refine ⟨q.2 - φ c w, w, ?_⟩
    have hdiff : q.1 - q.2 = (φ b - φ c) w := hw.symm
    have hsum := congrArg (fun r : A => r + q.2) hdiff
    dsimp at hsum ⊢
    rw [sub_add_cancel] at hsum
    apply Prod.ext
    · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
    · simp [sub_eq_add_neg]

end MathlibPlus.LinearAlgebra
