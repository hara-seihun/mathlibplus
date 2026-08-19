import Mathlib

namespace MathlibPlus.GraphTheory.Claim5512

/-- Claim 5512: an automorphism carrying one deleted vertex to another
transports the two induced deletion graphs isomorphically. -/
def automorphic_vertex_deletion_iso_claim5512 : Prop :=
  ∀ {V : Type*} [Fintype V]
    (G : SimpleGraph V) (φ : G ≃g G) (u v : V),
    φ u = v →
      Nonempty
        ((G.induce {w : V | w ≠ u}) ≃g
          (G.induce {w : V | w ≠ v}))

end MathlibPlus.GraphTheory.Claim5512

namespace MathlibPlus.LinearAlgebra

/-- Claim 5579: the finrank of a finite represented subspace span is a
normalized, monotone, submodular natural-valued rank function. -/
theorem representedSubspaceRank_polymatroid_claim5579
    (K V B : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    [Fintype B] [DecidableEq B] [FiniteDimensional K V]
    (U : B → Submodule K V) :
    let r : Finset B → ℕ := fun J => Module.finrank K ↥(J.sup U)
    r ∅ = 0 ∧
      (∀ J J' : Finset B, J ⊆ J' → r J ≤ r J') ∧
      (∀ J J' : Finset B, r (J ∪ J') + r (J ∩ J') ≤ r J + r J') := by
  let r : Finset B → ℕ := fun J => Module.finrank K ↥(J.sup U)
  have hnorm : r ∅ = 0 := by
    simp [r, Finset.sup_empty]
  have hmono : ∀ J J' : Finset B, J ⊆ J' → r J ≤ r J' := by
    intro J J' hJJ'
    exact Submodule.finrank_mono (Finset.sup_mono hJJ')
  have hsub : ∀ J J' : Finset B,
      r (J ∪ J') + r (J ∩ J') ≤ r J + r J' := by
    intro J J'
    let SJ : Submodule K V := J.sup U
    let SJ' : Submodule K V := J'.sup U
    have hinter : (J ∩ J').sup U ≤ SJ ⊓ SJ' := by
      refine le_inf ?_ ?_
      · exact Finset.sup_mono Finset.inter_subset_left
      · exact Finset.sup_mono Finset.inter_subset_right
    have hinterrank : Module.finrank K ↥((J ∩ J').sup U) ≤
        Module.finrank K ↥(SJ ⊓ SJ') :=
      Submodule.finrank_mono hinter
    calc
      r (J ∪ J') + r (J ∩ J') =
          Module.finrank K ↥(SJ ⊔ SJ') +
            Module.finrank K ↥((J ∩ J').sup U) := by
            simp only [r, SJ, SJ']
            rw [Finset.sup_union]
      _ ≤ Module.finrank K ↥(SJ ⊔ SJ') +
            Module.finrank K ↥(SJ ⊓ SJ') :=
            Nat.add_le_add_left hinterrank _
      _ = Module.finrank K ↥SJ + Module.finrank K ↥SJ' :=
            Submodule.finrank_sup_add_finrank_inf_eq SJ SJ'
      _ = r J + r J' := by rfl
  exact ⟨hnorm, hmono, hsub⟩

end MathlibPlus.LinearAlgebra

namespace MathlibPlus.Algebra

/-- Claim 5629: the nonzero attachment coefficient gives the exact parabola,
and a nonzero quadratic degree polynomial has at most two distinct natural
zeros when the attachment coefficient vanishes. -/
theorem fundamentalFilterZeroSets_claim5629
    (a b c : ℝ) :
    (∀ (h q : ℝ) (d : ℕ), h ≠ 0 →
      (a + b * (d : ℝ) + c * (d.choose 2 : ℝ) + h * q = 0 ↔
        q = -h⁻¹ * (a + b * (d : ℝ) + c * (d.choose 2 : ℝ)))) ∧
    (∀ h : ℝ, h = 0 → ¬ (a = 0 ∧ b = 0 ∧ c = 0) →
      ∀ (d₁ d₂ d₃ : ℕ), d₁ ≠ d₂ → d₁ ≠ d₃ → d₂ ≠ d₃ →
        (a + b * (d₁ : ℝ) + c * (d₁.choose 2 : ℝ) = 0) →
        (a + b * (d₂ : ℝ) + c * (d₂.choose 2 : ℝ) = 0) →
        (a + b * (d₃ : ℝ) + c * (d₃.choose 2 : ℝ) = 0) → False) := by
  constructor
  · intro h q d hh
    constructor
    · intro hzero
      field_simp [hh] at hzero ⊢
      nlinarith [hzero]
    · intro hq
      rw [hq]
      field_simp [hh]
      ring
  · intro h _hhzero hnonzero d₁ d₂ d₃ h12 h13 h23 h1 h2 h3
    let p : Polynomial ℝ :=
      Polynomial.C (c / 2) * Polynomial.X ^ 2 +
        Polynomial.C (b - c / 2) * Polynomial.X + Polynomial.C a
    have hpne : p ≠ 0 := by
      intro hp
      have hc : c / 2 = 0 := by
        have hh := congrArg (fun r : Polynomial ℝ => r.coeff 2) hp
        simpa [p] using hh
      have hb : b - c / 2 = 0 := by
        have hh := congrArg (fun r : Polynomial ℝ => r.coeff 1) hp
        simpa [p] using hh
      have ha : a = 0 := by
        have hh := congrArg (fun r : Polynomial ℝ => r.coeff 0) hp
        simpa [p] using hh
      apply hnonzero
      constructor
      · exact ha
      constructor
      · nlinarith [hb, hc]
      · nlinarith [hc]
    let S : Finset ℝ := {(d₁ : ℝ), (d₂ : ℝ), (d₃ : ℝ)}
    have hcast12 : (d₁ : ℝ) ≠ d₂ := by exact_mod_cast h12
    have hcast13 : (d₁ : ℝ) ≠ d₃ := by exact_mod_cast h13
    have hcast23 : (d₂ : ℝ) ≠ d₃ := by exact_mod_cast h23
    have hScard : S.card = 3 := by
      simp [S, hcast12, hcast13, hcast23]
    have h1' := h1
    have h2' := h2
    have h3' := h3
    rw [Nat.cast_choose_two] at h1'
    rw [Nat.cast_choose_two] at h2'
    rw [Nat.cast_choose_two] at h3'
    have hroot1 : p.eval (d₁ : ℝ) = 0 := by
      dsimp [p]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      nlinarith [h1']
    have hroot2 : p.eval (d₂ : ℝ) = 0 := by
      dsimp [p]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      nlinarith [h2']
    have hroot3 : p.eval (d₃ : ℝ) = 0 := by
      dsimp [p]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      nlinarith [h3']
    have hsub : S.val ⊆ p.roots := by
      intro z hz
      change z ∈ S at hz
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · simpa [Polynomial.mem_roots hpne] using hroot1
      · simpa [Polynomial.mem_roots hpne] using hroot2
      · simpa [Polynomial.mem_roots hpne] using hroot3
    have hcardle := Polynomial.card_le_degree_of_subset_roots hsub
    have hq2 : (Polynomial.C (c / 2) * Polynomial.X ^ 2).natDegree ≤ 2 := by
      simpa using Polynomial.natDegree_C_mul_X_pow_le (c / 2) 2
    have hq1 : (Polynomial.C (b - c / 2) * Polynomial.X).natDegree ≤ 1 := by
      simpa using Polynomial.natDegree_C_mul_X_pow_le (b - c / 2) 1
    have hdeg : p.natDegree ≤ 2 := by
      dsimp [p]
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · apply (Polynomial.natDegree_add_le _ _).trans
        exact max_le hq2 (hq1.trans (by omega))
      · simp
    have : S.card ≤ p.natDegree := by
      simpa [Multiset.card_coe, hScard] using hcardle
    omega

end MathlibPlus.Algebra

namespace MathlibPlus.Order

/-- Claim 5783: finite-region candidate domination and a genuine analytic-tail
handoff give strict maximality and uniqueness at the attained point. -/
theorem unique_attained_maximizer_of_strict_finite_tail
    {α : Type*} [DecidableEq α]
    (domain : Set α) (finitePart : Finset α) (coefficient : α → ℝ)
    (xStar : α) (height : α → ℝ) (handoff : ℝ)
    (_hxStar : xStar ∈ domain)
    (hcover : ∀ ⦃x : α⦄, x ∈ domain →
      height x < handoff ∨ handoff ≤ height x)
    (hfinite : ∀ ⦃x : α⦄, x ∈ domain → height x < handoff →
      x ≠ xStar →
        ∃ y : α, y ∈ finitePart ∧ coefficient x < coefficient y ∧
          (y = xStar ∨ coefficient y < coefficient xStar))
    (htail : ∀ ⦃x : α⦄, x ∈ domain → handoff ≤ height x →
      coefficient x < coefficient xStar) :
    (∀ ⦃x : α⦄, x ∈ domain → x ≠ xStar →
      coefficient x < coefficient xStar) ∧
      (∀ ⦃x : α⦄, x ∈ domain →
        coefficient x = coefficient xStar → x = xStar) := by
  have hstrict : ∀ ⦃x : α⦄, x ∈ domain → x ≠ xStar →
      coefficient x < coefficient xStar := by
    intro x hx hne
    rcases hcover hx with hlow | hhigh
    · rcases hfinite hx hlow hne with ⟨y, _hy, hxy, hy⟩
      rcases hy with rfl | hy
      · exact hxy
      · exact hxy.trans hy
    · exact htail hx hhigh
  refine ⟨hstrict, ?_⟩
  intro x hx heq
  by_contra hne
  exact (ne_of_lt (hstrict hx hne)) heq

end MathlibPlus.Order
