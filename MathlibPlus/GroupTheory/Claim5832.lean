import MathlibPlus.Basic

namespace MathlibPlus.GroupTheory.Claim5832

/-- The character shear on an additive copy of `C₂` is an involutive additive
bijection, hence an additive automorphism. -/
theorem characterShear_isAutomorphism_claim5832
    {H : Type*} [AddCommGroup H] (χ : H →+ ZMod 2) :
    ∃ α : (H × ZMod 2) ≃+ (H × ZMod 2),
      (∀ (x : H) (e : ZMod 2), α (x, e) = (x, e + χ x)) ∧
        (∀ p, α (α p) = p) := by
  let f : H × ZMod 2 → H × ZMod 2 := fun p => (p.1, p.2 + χ p.1)
  have hchar (x : H) : χ x + χ x = 0 := by
    calc
      χ x + χ x = 2 • χ x := by rw [two_nsmul]
      _ = ((2 : ZMod 2) * χ x) := by
        norm_num [nsmul_eq_mul]
      _ = 0 := by
        rw [show (2 : ZMod 2) = 0 from CharP.cast_eq_zero (ZMod 2) 2]
        simp
  have hinv : Function.Involutive f := by
    intro p
    rcases p with ⟨x, e⟩
    dsimp [f]
    apply Prod.ext
    · rfl
    · rw [add_assoc, hchar, add_zero]
  have hadd : ∀ p q, f (p + q) = f p + f q := by
    intro p q
    rcases p with ⟨x, e⟩
    rcases q with ⟨y, d⟩
    dsimp [f]
    simp only [AddMonoidHom.map_add]
    abel
  have hbij : Function.Bijective f := by
    constructor
    · intro p q hpq
      have h := congrArg f hpq
      rw [hinv p, hinv q] at h
      exact h
    · intro p
      exact ⟨f p, hinv p⟩
  let α : (H × ZMod 2) ≃+ (H × ZMod 2) :=
    AddEquiv.mk (Equiv.ofBijective f hbij) hadd
  refine ⟨α, ?_, ?_⟩
  · intro x e
    rfl
  · intro p
    exact hinv p

end MathlibPlus.GroupTheory.Claim5832
