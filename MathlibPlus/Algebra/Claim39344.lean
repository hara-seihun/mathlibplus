import Mathlib

namespace MathlibPlus.Algebra.Claim39344

/-- A triangular chart with no carry into the top coordinate centralizes the two
coordinate translations.  The chart's base map is arbitrary; this is the exact
universal algebraic core of admitted claim 39344. -/
theorem zeroTopChart_centralizes_coordinateTranslations
    {H : Type*} (m : H → ZMod 3) (g : H → H) :
    let q : ((ZMod 3 × ZMod 3) × H) → ((ZMod 3 × ZMod 3) × H) :=
      fun p => ((p.1.1, p.1.2 + m p.2), g p.2)
    let τz : ((ZMod 3 × ZMod 3) × H) → ((ZMod 3 × ZMod 3) × H) :=
      fun p => ((p.1.1 + 1, p.1.2), p.2)
    let τw : ((ZMod 3 × ZMod 3) × H) → ((ZMod 3 × ZMod 3) × H) :=
      fun p => ((p.1.1, p.1.2 + 1), p.2)
    Function.comp q τz = Function.comp τz q ∧
      Function.comp q τw = Function.comp τw q := by
  dsimp
  constructor
  · funext p
    rcases p with ⟨⟨z, w⟩, h⟩
    simp
  · funext p
    rcases p with ⟨⟨z, w⟩, h⟩
    simp [add_assoc, add_comm, add_left_comm]

end MathlibPlus.Algebra.Claim39344
