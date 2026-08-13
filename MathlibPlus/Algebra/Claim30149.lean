import Mathlib

namespace MathlibPlus.Algebra.Claim30149

/-- The circle-translation multiplication law, written pointwise.  The
assumptions expose exactly commutativity, associativity, and distributivity;
no nilpotence assumption is used. -/
theorem gamma_comp_claim30149
    {A : Type*} [NonUnitalNonAssocRing A]
    (hassoc : ∀ x a b : A, (x * a) * b = x * (a * b))
    (hcomm : ∀ a b : A, a * b = b * a)
    (a b x : A) :
    (x + x * b) + (x + x * b) * a =
      x + x * (a + b + a * b) := by
  rw [add_mul, hassoc x b a, hcomm b a]
  simp only [mul_add, add_assoc]
  abel

/-- The same circle-translation law as equality of the corresponding
functions. -/
theorem gamma_comp_as_functions_claim30149
    {A : Type*} [NonUnitalNonAssocRing A]
    (hassoc : ∀ x a b : A, (x * a) * b = x * (a * b))
    (hcomm : ∀ a b : A, a * b = b * a)
    (a b : A) :
    (fun z : A => z + z * a) ∘ (fun z : A => z + z * b) =
      (fun z : A => z + z * (a + b + a * b)) := by
  funext x
  exact gamma_comp_claim30149 hassoc hcomm a b x

/-- The set of points reached from `x` by all circle translations is the
explicit right ideal coset `x + xA`. -/
theorem gamma_directed_orbit_claim30149
    {A : Type*} [NonUnitalNonAssocRing A] (x : A) :
    Set.range (fun a : A => x + x * a) =
      {y : A | ∃ a : A, y = x + x * a} := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

/-- Every circle translation fixes zero, so the zero stabilizer inside the
circle-translation parameter family is the whole parameter family. -/
theorem gamma_zero_stabilizer_claim30149
    {A : Type*} [NonUnitalNonAssocRing A] :
    {a : A | (0 : A) + 0 * a = 0} = Set.univ := by
  ext a
  simp

/-- After adjoining inversion, the paired orbit is the union of the direct
orbit and its additive negatives. -/
theorem gamma_paired_orbit_claim30149
    {A : Type*} [NonUnitalNonAssocRing A] (x : A) :
    Set.range (fun a : A => x + x * a) ∪
        Set.range (fun a : A => -(x + x * a)) =
      {y : A | ∃ a : A, y = x + x * a ∨ y = -(x + x * a)} := by
  ext y
  constructor
  · intro hy
    rcases hy with hy | hy
    · rcases hy with ⟨a, rfl⟩
      exact ⟨a, Or.inl rfl⟩
    · rcases hy with ⟨a, rfl⟩
      exact ⟨a, Or.inr rfl⟩
  · rintro ⟨a, hya | hya⟩
    · exact Or.inl ⟨a, hya.symm⟩
    · exact Or.inr ⟨a, hya.symm⟩

end MathlibPlus.Algebra.Claim30149
