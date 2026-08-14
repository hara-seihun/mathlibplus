import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

abbrev BinaryThreeSpace := Fin 3 → ZMod 2
abbrev NineCyclicSpace := ZMod 9
abbrev BinaryNineSet := BinaryThreeSpace × NineCyclicSpace

def productTranslationSet : Set (Equiv.Perm BinaryNineSet) :=
  {t | ∃ a : BinaryNineSet, ∀ x, t x = x + a}

def conjugatePermutationSet (h : Equiv.Perm BinaryNineSet)
    (T : Set (Equiv.Perm BinaryNineSet)) : Set (Equiv.Perm BinaryNineSet) :=
  {g | ∃ t, t ∈ T ∧ g = h⁻¹ * t * h}

def regularPermutationSet (T : Set (Equiv.Perm BinaryNineSet)) : Prop :=
  ∀ x y : BinaryNineSet, ∃! t, t ∈ T ∧ t x = y

def c9Orbit (v : BinaryThreeSpace) : Set BinaryNineSet :=
  {x | x.1 = v}

def emptyRelationConjugator (h : Equiv.Perm BinaryNineSet) : Prop :=
  ∀ x y : BinaryNineSet, False ↔ False

/-- R-4506, the explicit non-automorphism product conjugator preserving the
characteristic C9 orbit partition, including its empty-relation instance. -/
def claim52980 : Prop :=
  ∃ q : BinaryThreeSpace ≃ BinaryThreeSpace,
    ∃ p : NineCyclicSpace ≃ NineCyclicSpace,
      q 0 = 0 ∧ p 0 = 0 ∧
      (¬∀ x y : BinaryThreeSpace, q (x + y) = q x + q y) ∧
      (¬∀ x y : NineCyclicSpace, p (x + y) = p x + p y) ∧
      let h : Equiv.Perm BinaryNineSet := Equiv.prodCongr q p
      regularPermutationSet productTranslationSet ∧
      regularPermutationSet (conjugatePermutationSet h productTranslationSet) ∧
      (∀ v : BinaryThreeSpace,
        Set.image h (c9Orbit v) = c9Orbit (q v)) ∧
      emptyRelationConjugator h

end MathlibPlus.Open.ResearchFormalization
