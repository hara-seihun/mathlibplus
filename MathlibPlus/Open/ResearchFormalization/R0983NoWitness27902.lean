import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a001b7_8151_7192_bf7c_77d39208c988

namespace MathlibPlus.Open.ResearchFormalization.R0983NoWitness

noncomputable section

private def normalizedMap
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p : A → Equiv.Perm B) : A × B → A × B :=
  fun ab => (ab.1, p ab.1 ab.2)

private def normalizedMapInv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p : A → Equiv.Perm B) : A × B → A × B :=
  fun ab => (ab.1, (p ab.1).symm ab.2)

private def normalizedRelativeDerivative
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p : A → Equiv.Perm B) (c g : A × B) : A × B :=
  normalizedMapInv p
    (normalizedMap p (c + g) - normalizedMap p g)

private def derivativeCriterion
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p : A → Equiv.Perm B) (S : Set (A × B)) : Prop :=
  ∀ g : A × B,
    (fun c : A × B => normalizedRelativeDerivative p c g) '' S = S

private def inverseClosed {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  ∀ x, x ∈ S → -x ∈ S

/-- Claim 27902: on every finite elementary-two base and finite odd-order
abelian fiber, the normalized identity-base fiber map fixes every directed
connection set satisfying the exact relative-derivative criterion, and hence
every inverse-closed undirected one as well. -/
def claim27902_noIdentityBaseOddFiberCIWitness
    {A B : Type*} [Fintype A] [AddCommGroup A]
    [Fintype B] [AddCommGroup B]
    (elementaryTwo : ∀ a : A, a + a = 0)
    (oddOrder : Odd (Fintype.card B))
    (p : A → Equiv.Perm B)
    (normalized : p 0 = Equiv.refl B) : Prop :=
  let f := normalizedMap p
  (∀ a : A, a + a = 0) ∧ Odd (Fintype.card B) ∧
    p 0 = Equiv.refl B ∧
    (∀ S : Set (A × B),
    derivativeCriterion p S → f '' S = S) ∧
    (∀ S : Set (A × B),
      derivativeCriterion p S → inverseClosed S → f '' S = S) ∧
    (¬ ∃ S : Set (A × B), derivativeCriterion p S ∧ f '' S ≠ S) ∧
    (¬ ∃ S : Set (A × B),
      derivativeCriterion p S ∧ inverseClosed S ∧ f '' S ≠ S)

end

end MathlibPlus.Open.ResearchFormalization.R0983NoWitness
