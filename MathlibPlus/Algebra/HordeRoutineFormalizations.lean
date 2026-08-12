import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-!
Formalizations of admitted claims 19810 and 50622.
-/

/-- Claim 19810: the kernel of an algebra homomorphism is an ideal. -/
theorem kernel_isIdeal_claim19810
    {R S : Type*} [Semiring R] [Semiring S] (γ : R →+* S) :
    ∃ I : Ideal R, ∀ x, x ∈ I ↔ γ x = 0 := by
  exact ⟨RingHom.ker γ, fun x => Iff.rfl⟩

/-- Claim 50622: the effective-divisor character is the unique map whose value
on a divisor is the product of the assigned factor values, and it is
multiplicative for divisor addition. -/
theorem divisorCharacter_claim50622
    {ι M : Type*} [CommMonoid M] (τ : ι → M) :
    ∃! χ : (ι →₀ ℕ) → M,
      χ 0 = 1 ∧
      (∀ d e, χ (d + e) = χ d * χ e) ∧
      (∀ d, χ d = d.prod (fun i n => τ i ^ n)) := by
  classical
  let f : (ι →₀ ℕ) → M := fun d => d.prod (fun i n => τ i ^ n)
  have hf_zero : f 0 = 1 := by
    simp [f]
  have hf_add : ∀ d e, f (d + e) = f d * f e := by
    intro d e
    dsimp [f]
    rw [Finsupp.prod_add_index]
    · intro i hi
      simp
    · intro i hi a b
      rw [pow_add]
  refine ⟨f, ⟨hf_zero, hf_add, fun d => rfl⟩, ?_⟩
  intro χ hχ
  funext d
  exact hχ.2.2 d

end MathlibPlus.Algebra
