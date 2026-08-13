import Mathlib

/-!
# Boolean symmetric-difference fibres (claim 21562)

The packet names Boolean spaces `U`, `V`, `C`, and `Q` without defining them.
This module records the canonical full-cube instance: vectors are functions
`Fin n → Bool`, addition is pointwise `Bool.xor`, and `n` is the dimension.
-/

namespace MathlibPlus.Combinatorics.Claim21562

/-- The kernel of pointwise Boolean symmetric difference is the diagonal. -/
theorem xor_kernel (n : ℕ) (x y : Fin n → Bool) :
    ((fun i => x i ^^ y i) = (fun _ => false)) ↔ y = x := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    cases hx : x i <;> cases hy : y i <;> simp [hx, hy] at hi ⊢
  · intro h
    subst y
    funext i
    exact Bool.xor_self _

/-- Every fibre of pointwise Boolean symmetric difference has `2^n` elements. -/
theorem xor_fiber_card (n : ℕ) (c : Fin n → Bool) :
    Fintype.card {p : (Fin n → Bool) × (Fin n → Bool) //
      (fun i => p.1 i ^^ p.2 i) = c} = 2 ^ n := by
  have xor_cancel : ∀ a b d : Bool, (a ^^ b) = (a ^^ d) → b = d := by
    intro a b d h
    cases a <;> simp_all
  let e : {p : (Fin n → Bool) × (Fin n → Bool) //
      (fun i => p.1 i ^^ p.2 i) = c} → (Fin n → Bool) := fun p => p.1.1
  have he : Function.Bijective e := by
    constructor
    · intro p q hpq
      rcases p with ⟨⟨xp, yp⟩, hp⟩
      rcases q with ⟨⟨xq, yq⟩, hq⟩
      dsimp [e] at hpq
      have hfirst : xp = xq := hpq
      have hsecond : yp = yq := by
        funext i
        refine xor_cancel (xp i) (yp i) (yq i) ?_
        calc
          (xp i ^^ yp i) = c i := congrFun hp i
          _ = (xq i ^^ yq i) := (congrFun hq i).symm
          _ = (xp i ^^ yq i) := by rw [hfirst]
      exact Subtype.ext (Prod.ext hfirst hsecond)
    · intro x
      let y : Fin n → Bool := fun i => x i ^^ c i
      have hy : (fun i => x i ^^ y i) = c := by
        funext i
        dsimp [y]
        rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
      refine ⟨(⟨(x, y), hy⟩ : {p : (Fin n → Bool) × (Fin n → Bool) //
        (fun i => p.1 i ^^ p.2 i) = c}), ?_⟩
      rfl
  rw [Fintype.card_congr (Equiv.ofBijective e he), Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

end MathlibPlus.Combinatorics.Claim21562
