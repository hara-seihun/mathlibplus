import MathlibPlus.Open.ResearchFormalization.R0983Claim27893
import MathlibPlus.Open.ResearchFormalizationBatch_01a001b7_8151_7192_bf7c_77d39208c988

namespace MathlibPlus.Open.ResearchFormalization.R0983Claim27901

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0983
open MathlibPlus.Open.ResearchFormalizationBatch_01a001b7_8151_7192_bf7c_77d39208c988

/-- The normalized relative-derivative permutation on `A × B`, written as
`f⁻¹ ∘ (translation by -f g) ∘ f ∘ (translation by g)`. -/
def normalizedRelativeDerivativePerm27901
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p : A → Equiv.Perm B) (g : A × B) : Equiv.Perm (A × B) :=
  let f := fiberMap27893 p
  (Equiv.addRight g).trans
    (f.trans
      ((Equiv.addRight (-(f g))).trans f.symm))

def normalizedRelativeDerivativeGroup27901
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p : A → Equiv.Perm B) : Subgroup (Equiv.Perm (A × B)) :=
  Subgroup.closure (Set.range (normalizedRelativeDerivativePerm27901 p))

/-- An orbit of the full normalized relative-derivative group. -/
def derivativeOrbit27901
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p : A → Equiv.Perm B) (x : A × B) : Set (A × B) :=
  {y | ∃ h : normalizedRelativeDerivativeGroup27901 p,
    (h : Equiv.Perm (A × B)) x = y}

def derivativeGroupInvariant27901
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p : A → Equiv.Perm B) (S : Set (A × B)) : Prop :=
  ∀ h : normalizedRelativeDerivativeGroup27901 p,
    (h : Equiv.Perm (A × B)) '' S = S

def inverseClosed27901 {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (S : Set (A × B)) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

def isUnionOfDerivativeOrbits27901
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p : A → Equiv.Perm B) (S : Set (A × B)) : Prop :=
  S = {y | ∃ x, x ∈ S ∧ y ∈ derivativeOrbit27901 p x}

/-- Claim 27901: every derivative-invariant directed connection set is a
union of the exact derivative-group orbits and is fixed by the normalized
identity-base fibre map; inverse-closed sets give the undirected instance. -/
def claim27901 : Prop :=
  ∀ (A B : Type*) [Fintype A] [AddCommGroup A]
    [Fintype B] [AddCommGroup B],
    (∀ a : A, a + a = 0) →
    Odd (Fintype.card B) →
    ∀ (p : A → Equiv.Perm B),
      p 0 = Equiv.refl B →
      let f := normalizedIdentityBaseFiberMap A B p
      ∀ S : Set (A × B),
        derivativeGroupInvariant27901 p S →
        isUnionOfDerivativeOrbits27901 p S ∧
          f '' S = S ∧
          (inverseClosed27901 S → f '' S = S)

end
end MathlibPlus.Open.ResearchFormalization.R0983Claim27901
