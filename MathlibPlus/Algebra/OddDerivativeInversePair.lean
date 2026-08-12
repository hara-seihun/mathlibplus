import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Abel

namespace MathlibPlus.Algebra.OddDerivativeInversePair

/-- The odd finite-difference, span, and inverse-pair identities from claim 53186. -/
theorem oddDerivative_inversePairIdentities
    {K U W : Type*} [Ring K] [AddCommGroup U] [AddCommGroup W]
    [Module K W] (f : U → K) (v : W) (_hzero : f 0 = 0)
    (hodd : ∀ a : U, f (-a) = -f a) :
    let D : U → U → K := fun a x => f (x + a) - f x - f a
    let H : U → Submodule K W :=
      fun a => Submodule.span K (Set.range (fun x => D a x • v))
    (∀ a x : U, D (-a) x = -D a (x - a)) ∧
      (∀ a : U, H (-a) = H a) ∧
      ∀ B : U → Set W, (∀ a : U, B (-a) = -B a) →
        (∀ w : U × W,
          (w.2 ∈ B w.1) ↔ ((-w.1, -w.2).2 ∈ B (-w.1))) ∧
        (∀ a : U, ∀ w : W,
          (∃ b : W, b ∈ B a ∧ w = b + f a • v) ↔
            (∃ b : W, b ∈ B (-a) ∧ (-w) = b + f (-a) • v)) := by
  let D : U → U → K := fun a x => f (x + a) - f x - f a
  let H : U → Submodule K W :=
    fun a => Submodule.span K (Set.range (fun x => D a x • v))
  change (∀ a x : U, D (-a) x = -D a (x - a)) ∧
      (∀ a : U, H (-a) = H a) ∧
      ∀ B : U → Set W, (∀ a : U, B (-a) = -B a) →
        (∀ w : U × W,
          (w.2 ∈ B w.1) ↔ ((-w.1, -w.2).2 ∈ B (-w.1))) ∧
        (∀ a : U, ∀ w : W,
          (∃ b : W, b ∈ B a ∧ w = b + f a • v) ↔
            (∃ b : W, b ∈ B (-a) ∧ (-w) = b + f (-a) • v))
  have hD : ∀ a x : U, D (-a) x = -D a (x - a) := by
    intro a x
    dsimp [D]
    rw [hodd]
    simp only [sub_eq_add_neg, neg_neg, add_assoc, add_left_comm, add_comm,
      sub_add_cancel]
    abel
  have hDrev : ∀ a x : U, D a x = -D (-a) (x + a) := by
    intro a x
    have hx := hD a (x + a)
    rw [show (x + a) - a = x by abel] at hx
    calc
      D a x = -(-D a x) := by simp
      _ = -D (-a) (x + a) := by rw [hx]
  have hH : ∀ a : U, H (-a) = H a := by
    intro a
    apply le_antisymm
    · apply (Submodule.span_le).2
      intro z hz
      rcases hz with ⟨x, rfl⟩
      change D (-a) x • v ∈ H a
      rw [hD]
      simpa only [neg_smul] using H a |>.neg_mem (Submodule.subset_span ⟨x - a, rfl⟩)
    · apply (Submodule.span_le).2
      intro z hz
      rcases hz with ⟨x, rfl⟩
      change D a x • v ∈ H (-a)
      rw [hDrev]
      simpa only [neg_smul] using H (-a) |>.neg_mem (Submodule.subset_span ⟨x + a, rfl⟩)
  refine ⟨hD, hH, ?_⟩
  intro B hB
  have hBmem : ∀ (a : U) (w : W), w ∈ B a ↔ -w ∈ B (-a) := by
    intro a w
    rw [hB, Set.mem_neg]
    simp
  constructor
  · intro w
    exact hBmem w.1 w.2
  · intro a w
    constructor
    · rintro ⟨b, hb, hw⟩
      refine ⟨-b, (hBmem a b).mp hb, ?_⟩
      rw [hw, hodd]
      simp only [neg_add, neg_smul]
    · rintro ⟨b, hb, hw⟩
      have hb' : -b ∈ B a := by
        simpa only [neg_neg] using (hBmem (-a) b).mp hb
      refine ⟨-b, hb', ?_⟩
      have hw' := congrArg Neg.neg hw
      rw [hodd] at hw'
      simpa only [neg_add, neg_smul, neg_neg] using hw'

end MathlibPlus.Algebra.OddDerivativeInversePair
