import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0983

abbrev C2 := ZMod 2

def fiberDerivative (p : C2 → Equiv.Perm C2)
    (a u t x : C2) : C2 :=
  (p a).symm (p (a + u) (x + t) - p u t)

def derivativeStep (p : C2 → Equiv.Perm C2)
    (u t : C2) (x : C2 × C2) : C2 × C2 :=
  (x.1, fiberDerivative p x.1 u t x.2)

def derivativeOrbit (p : C2 → Equiv.Perm C2)
    (x : C2 × C2) : Set (C2 × C2) :=
  {y | Relation.ReflTransGen
    (fun z w => ∃ u t : C2, w = derivativeStep p u t z) x y}

def displacementSubgroup {B : Type*} [AddCommGroup B]
    (p : Equiv.Perm B) : AddSubgroup B :=
  AddSubgroup.closure {t - p t + p 0 | t : B}

/-- Claim 27903: the explicit C₂/C₂ profile has trivial displacement and
 identity normalized derivatives, while its nontrivial fiber permutation moves
 a singleton derivative orbit. -/
def oddOrderHypothesisIsSharp_claim27903 : Prop := by
  classical
  let p0 : Equiv.Perm C2 := Equiv.refl C2
  let p1 : Equiv.Perm C2 := Equiv.addRight 1
  let p : C2 → Equiv.Perm C2 := fun a => if a = 0 then p0 else p1
  let W := displacementSubgroup p1
  exact
    W = ⊥ ∧
      (∀ u t : C2, ∀ x : C2 × C2,
        derivativeStep p u t x = x) ∧
        ∃ f : Equiv.Perm (C2 × C2),
          (∀ a b : C2,
            f (a, b) = (a, if a = 0 then b else b + 1)) ∧
          (∀ x : C2 × C2,
            derivativeOrbit p x = ({x} : Set (C2 × C2))) ∧
          f (1, 0) ≠ (1, 0)

end MathlibPlus.Open.ResearchFormalization.R0983
