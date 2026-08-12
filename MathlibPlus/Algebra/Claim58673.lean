import MathlibPlus.Algebra.TranslationPeriod

namespace MathlibPlus.Algebra.Claim58673

open MathlibPlus.Algebra.TranslationPeriod

private theorem translateSet_eq_translateSet_iff_sub_mem_period
    {A : Type*} [AddCommGroup A] (X : Set A) (u v : A) :
    translateSet X u = translateSet X v ↔
      u - v ∈ periodSubgroup X := by
  constructor
  · intro h
    change translateSet X (u - v) = X
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hyv : x + u ∈ translateSet X v := by
        rw [← h]
        exact ⟨x, hx, rfl⟩
      rcases hyv with ⟨z, hz, hzu⟩
      change z + v = x + u at hzu
      change x + (u - v) ∈ X
      have hzx : x + (u - v) = z := by
        calc
          x + (u - v) = (x + u) - v := (add_sub_assoc x u v).symm
          _ = (z + v) - v := by rw [← hzu]
          _ = z := add_sub_cancel_right z v
      rw [hzx]
      exact hz
    · intro hy
      have hyv : y + v ∈ translateSet X u := by
        rw [h]
        exact ⟨y, hy, rfl⟩
      rcases hyv with ⟨x, hx, hxy⟩
      change x + u = y + v at hxy
      refine ⟨x, hx, ?_⟩
      change x + (u - v) = y
      calc
        x + (u - v) = (x + u) - v := (add_sub_assoc x u v).symm
        _ = (y + v) - v := by rw [hxy]
        _ = y := add_sub_cancel_right y v
  · intro hp
    change translateSet X (u - v) = X at hp
    have hneg : v - u ∈ periodSubgroup X := by
      have := (periodSubgroup X).neg_mem hp
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hpneg : translateSet X (v - u) = X := hneg
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x + (u - v) ∈ X := by
        rw [← hp]
        exact ⟨x, hx, rfl⟩
      refine ⟨x + (u - v), hx', ?_⟩
      abel
    · rintro ⟨x, hx, rfl⟩
      have hx' : x + (v - u) ∈ X := by
        rw [← hpneg]
        exact ⟨x, hx, rfl⟩
      refine ⟨x + (v - u), hx', ?_⟩
      abel

/-- The exact slice-level criterion behind the quotient-identity transport.
The source's surjectivity and normalization hypotheses are retained as explicit
parameters; the displayed equivalence itself uses only the additive group laws. -/
theorem exactSliceCriterion
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (π : C →+ B) (_hπ : Function.Surjective π)
    (s : B → A) (_hs0 : s 0 = 0) (S : Set (A × C)) :
    (∀ x : B, ∀ c : C,
      translateSet {a : A | (a, c) ∈ S} (s (x + π c) - s x) =
        translateSet {a : A | (a, c) ∈ S} (s (π c))) ↔
    (∀ x : B, ∀ c : C,
      s (x + π c) - s x - s (π c) ∈
        periodSubgroup {a : A | (a, c) ∈ S}) := by
  constructor
  · intro h x c
    exact (translateSet_eq_translateSet_iff_sub_mem_period
      {a : A | (a, c) ∈ S} (s (x + π c) - s x) (s (π c))).mp (h x c)
  · intro h x c
    exact (translateSet_eq_translateSet_iff_sub_mem_period
      {a : A | (a, c) ∈ S} (s (x + π c) - s x) (s (π c))).mpr (h x c)

end MathlibPlus.Algebra.Claim58673
