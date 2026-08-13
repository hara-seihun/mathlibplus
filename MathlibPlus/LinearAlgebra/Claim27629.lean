import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- The pointed block operator is injective whenever its Schur-complement
operator `E - D²` is injective.  This is the elimination step in claim 27629. -/
theorem blockOperator_injective_claim27629
    {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (D E : V →ₗ[R] V)
    (hED : Function.Injective (E - D.comp D)) :
    Function.Injective (fun p : V × V =>
      (D p.1 + E p.2, p.1 + D p.2)) := by
  rintro ⟨f, g⟩ ⟨f', g'⟩ h
  have h₁ : D f + E g = D f' + E g' := congrArg Prod.fst h
  have h₂ : f + D g = f' + D g' := congrArg Prod.snd h
  have hD : D (f + D g) = D (f' + D g') := congrArg D h₂
  have hD' : D f + D (D g) = D f' + D (D g') := by
    simpa only [map_add] using hD
  have hED' : E g - D (D g) = E g' - D (D g') := by
    calc
      E g - D (D g) = (D f + E g) - (D f + D (D g)) := by abel
      _ = (D f' + E g') - (D f' + D (D g')) := by rw [h₁, hD']
      _ = E g' - D (D g') := by abel
  have hED'' : (E - D.comp D) g = (E - D.comp D) g' := by
    simpa only [LinearMap.sub_apply, LinearMap.comp_apply] using hED'
  have hgg' : g = g' := hED hED''
  have hff' : f = f' := by
    apply add_right_cancel (b := D g)
    simpa [hgg'] using h₂
  exact Prod.ext hff' hgg'

end MathlibPlus.LinearAlgebra
