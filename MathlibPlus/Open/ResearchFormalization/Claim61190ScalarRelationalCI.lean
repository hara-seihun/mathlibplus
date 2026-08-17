import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim61190

noncomputable section

abbrev ScalarGroup := ZMod 13 × ZMod 3

/-- The scalar action used in `E(C_13,3)`, with the second coordinate in
`ZMod 3` represented by its canonical exponent. -/
def scalarCoefficient (i : ZMod 3) : ZMod 13 :=
  (3 : ZMod 13) ^ i.val

/-- The displayed semidirect-product multiplication. -/
def scalarMul (x y : ScalarGroup) : ScalarGroup :=
  (x.1 + scalarCoefficient x.2 * y.1, x.2 + y.2)

/-- The inverse in the displayed semidirect-product coordinates. -/
def scalarInv (x : ScalarGroup) : ScalarGroup :=
  (-((3 : ZMod 13) ^ ((3 - x.2.val) % 3)) * x.1, -x.2)

def scalarIdentity : ScalarGroup := (0, 0)

def identityFree (S : Set ScalarGroup) : Prop :=
  scalarIdentity ∉ S

def inverseClosed (S : Set ScalarGroup) : Prop :=
  ∀ ⦃x : ScalarGroup⦄, x ∈ S ↔ scalarInv x ∈ S

/-- A binary Cayley relation for the displayed multiplication. -/
def cayleyRelation (S : Set ScalarGroup)
    (x y : ScalarGroup) : Prop :=
  ∃ s ∈ S, scalarMul (scalarInv x) y = s

/-- A simultaneous isomorphism of all labelled Cayley relations. -/
def simultaneousCayleyIsomorphism {I : Type*}
    (S T : I → Set ScalarGroup) (e : ScalarGroup ≃ ScalarGroup) : Prop :=
  ∀ i x y,
    cayleyRelation (S i) x y ↔ cayleyRelation (T i) (e x) (e y)

/-- A group automorphism of the displayed coordinate group. -/
def scalarAutomorphism (α : ScalarGroup ≃ ScalarGroup) : Prop :=
  (α scalarIdentity = scalarIdentity) ∧
    ∀ x y, α (scalarMul x y) = scalarMul (α x) (α y)

/-- Claim 61190: simultaneous CI for every finite labelled tuple of
identity-free inverse-closed symmetric Cayley relations on `E(C_13,3)`. -/
def claim61190_simultaneousScalarRelationalCI : Prop :=
  ∀ {I : Type*} [Fintype I]
    (S T : I → Set ScalarGroup),
    (∀ i, identityFree (S i) ∧ inverseClosed (S i)) ∧
      (∀ i, identityFree (T i) ∧ inverseClosed (T i)) →
      ∀ e : ScalarGroup ≃ ScalarGroup,
        simultaneousCayleyIsomorphism S T e →
        ∃ α : ScalarGroup ≃ ScalarGroup,
          scalarAutomorphism α ∧ ∀ i, α '' S i = T i

end

end MathlibPlus.Open.ResearchFormalization.Claim61190
