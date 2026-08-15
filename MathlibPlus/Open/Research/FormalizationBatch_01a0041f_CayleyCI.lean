import Mathlib

namespace MathlibPlus.Open.Research

noncomputable section

abbrev TernaryVector (r : ℕ) := Fin r → ZMod 3

def inverseClosed (S : Finset (TernaryVector r)) : Prop :=
  ∀ x, x ∈ S → -x ∈ S

def identityFree (S : Finset (TernaryVector r)) : Prop :=
  (0 : TernaryVector r) ∉ S

def spansTernary (S : Finset (TernaryVector r)) : Prop :=
  Submodule.span (R := ZMod 3) (↑S : Set (TernaryVector r)) = ⊤

def ordinaryCayleyGraph (S : Finset (TernaryVector r)) :
    SimpleGraph (TernaryVector r) :=
  SimpleGraph.fromRel (fun x y => x ≠ y ∧ (y - x ∈ S ∨ x - y ∈ S))

def linearTransport (S T : Finset (TernaryVector r)) : Prop :=
  ∃ A : TernaryVector r ≃ₗ[ZMod 3] TernaryVector r,
    A '' (↑S : Set (TernaryVector r)) = (↑T : Set (TernaryVector r))

/-- The rank-six/seven elementary-abelian Cayley CI statement. -/
def claim_59777 : Prop :=
  ∀ r : ℕ, (r = 6 ∨ r = 7) →
    ∀ S T : Finset (TernaryVector r),
      identityFree S → inverseClosed S → spansTernary S →
      S.card = 2 * (r + 1) →
      identityFree T → inverseClosed T →
      ∀ e : ordinaryCayleyGraph S ≃g ordinaryCayleyGraph T,
        linearTransport S T

end
end MathlibPlus.Open.Research
