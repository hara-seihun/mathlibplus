import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization

attribute [local instance] Classical.propDecidable Classical.decEq

section BinaryTimesNine

abbrev binaryVector (r : ℕ) := Fin r → ZMod 2
abbrev binaryTimesNine (r : ℕ) := binaryVector r × ZMod 9

def linearlyIndependentSet {r : ℕ} (A : Set (binaryVector r)) : Prop :=
  LinearIndependent (R := ZMod 2) (fun a : A => (a : binaryVector r))

def embeddedConnection {r : ℕ} (A : Set (binaryVector r)) : Set (binaryTimesNine r) :=
  {g | ∃ a, a ∈ A ∧ g = (a, 0)}

def additiveInverseClosed {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ S → -x ∈ S

def additiveCayleyAdj {G : Type*} [AddGroup G]
    (S : Set G) (x y : G) : Prop :=
  x - y ∈ S

def additiveCayleyGraphIso {G : Type*} [AddGroup G]
    (S T : Set G) (e : G ≃ G) : Prop :=
  ∀ x y, additiveCayleyAdj S x y ↔ additiveCayleyAdj T (e x) (e y)

def additiveCayleyCI {G : Type*} [AddCommGroup G]
    (S : Set G) : Prop :=
  S ⊆ (Set.univ : Set G) \ {0} ∧
    additiveInverseClosed S ∧
    ∀ T : Set G,
      T ⊆ (Set.univ : Set G) \ {0} →
      additiveInverseClosed T →
      ∀ e : G ≃ G,
        additiveCayleyGraphIso S T e →
          ∃ α : G ≃+ G, α '' S = T

/-- CI property for the binary-vector times cyclic-nine family. -/
def claim59832 : Prop :=
  ∀ (r : ℕ) (A : Set (binaryVector r)),
    linearlyIndependentSet A →
      additiveCayleyCI (embeddedConnection A)

end BinaryTimesNine

end MathlibPlus.Open.ResearchFormalization

end
