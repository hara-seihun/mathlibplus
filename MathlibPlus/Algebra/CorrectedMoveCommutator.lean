import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim30680

/-- In the standard affine two-step model, the commutator of two corrected moves
fixes the plane coordinate and translates the central coordinate by the
alternating pairing of their coefficient and displacement vectors. -/
theorem correctedMove_commutator
    {R : Type*} [CommRing R]
    (A_s d_s A_r d_r : Fin 2 → R) :
    let T_s : ((Fin 2 → R) × R) → ((Fin 2 → R) × R) :=
      fun p => (p.1 + d_s, p.2 + dotProduct A_s p.1)
    let T_r : ((Fin 2 → R) × R) → ((Fin 2 → R) × R) :=
      fun p => (p.1 + d_r, p.2 + dotProduct A_r p.1)
    let T_s_inv : ((Fin 2 → R) × R) → ((Fin 2 → R) × R) :=
      fun p => (p.1 - d_s, p.2 - dotProduct A_s (p.1 - d_s))
    let T_r_inv : ((Fin 2 → R) × R) → ((Fin 2 → R) × R) :=
      fun p => (p.1 - d_r, p.2 - dotProduct A_r (p.1 - d_r))
    ∀ p, (T_s ∘ T_r ∘ T_s_inv ∘ T_r_inv) p =
      (p.1, p.2 + dotProduct A_s d_r - dotProduct A_r d_s) := by
  dsimp
  intro p
  congr 1
  · funext i
    simp [Function.comp_def]
    ring
  · simp [Function.comp_def, dotProduct]
    ring

end MathlibPlus.Algebra.Claim30680
