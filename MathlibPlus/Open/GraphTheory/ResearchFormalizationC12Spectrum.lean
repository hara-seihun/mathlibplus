import Mathlib

open scoped Classical BigOperators

namespace MathlibPlus.Open.GraphTheory

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

def c12Root : ℂ := Complex.exp (2 * Real.pi * Complex.I / 12)

def c12ConnectionSet : Finset (ZMod 12) := {1, 2, -2, -1}

def c12FourierEigenvalue (k : ZMod 12) : ℂ :=
  Finset.sum c12ConnectionSet
    (fun s => c12Root ^ ((k.val * s.val) % 12))

def c12EigenClass (k : ZMod 12) : Finset (ZMod 12) :=
  Finset.univ.filter (fun j => c12FourierEigenvalue j = c12FourierEigenvalue k)

def c12ExpectedClasses : Finset (Finset (ZMod 12)) :=
  {({0} : Finset (ZMod 12)),
    ({1, 11} : Finset (ZMod 12)),
    ({2, 6, 10} : Finset (ZMod 12)),
    ({3, 4, 8, 9} : Finset (ZMod 12)),
    ({5, 7} : Finset (ZMod 12))}

def c12ConnectionPreserved (e : ZMod 12 ≃+ ZMod 12) : Prop :=
  ∀ s : ZMod 12, s ∈ c12ConnectionSet ↔ e s ∈ c12ConnectionSet

def c12IsAdditiveCoset (A : Finset (ZMod 12)) : Prop :=
  ∃ H : AddSubgroup (ZMod 12), ∃ a : ZMod 12,
    ∀ x : ZMod 12, x ∈ A ↔ ∃ h : H, x = a + h.1

def c12UnionOfCosets (A : Finset (ZMod 12)) : Prop :=
  ∃ H : AddSubgroup (ZMod 12), H ≠ ⊥ ∧ H ≠ ⊤ ∧
    ∀ x : ZMod 12, ∀ h : H, x ∈ A ↔ x + h.1 ∈ A

def c12AdditiveCayleyGraph (S : Set (ZMod 12)) : SimpleGraph (ZMod 12) :=
  SimpleGraph.fromRel (fun x y => y - x ∈ S)

def c12FixedConnectionCI : Prop :=
  ∀ T : Set (ZMod 12),
    (∀ x, x ∈ c12ConnectionSet → -x ∈ c12ConnectionSet) →
    (∀ x, x ∈ T → -x ∈ T) →
    (0 : ZMod 12) ∉ (c12ConnectionSet : Set (ZMod 12)) →
    0 ∉ T →
    ∀ f : ZMod 12 ≃ ZMod 12,
      (∀ x y, y - x ∈ (c12ConnectionSet : Set (ZMod 12)) ↔
        f y - f x ∈ T) →
      ∃ α : ZMod 12 ≃+ ZMod 12,
        α '' (c12ConnectionSet : Set (ZMod 12)) = T

/-- The complete exact spectral partition, its non-coset cell, and the
connection-set stabilizer/orbit data for the cyclic order twelve example. -/
def claim47008 : Prop :=
  (Finset.univ.image c12EigenClass = c12ExpectedClasses) ∧
  (c12EigenClass 3 = ({3, 4, 8, 9} : Finset (ZMod 12))) ∧
  (¬ c12IsAdditiveCoset (c12EigenClass 3)) ∧
  ((∀ e : ZMod 12 ≃+ ZMod 12, c12ConnectionPreserved e →
      (∀ x, e x = x) ∨ (∀ x, e x = -x)) ∧
    c12ConnectionPreserved (AddEquiv.refl (ZMod 12)) ∧
    c12ConnectionPreserved (AddEquiv.neg (ZMod 12)) ∧
    (∀ e : ZMod 12 ≃+ ZMod 12, c12ConnectionPreserved e →
      e 3 = 3 ∨ e 3 = 9)) ∧
  (¬ c12UnionOfCosets c12ConnectionSet) ∧
  (AddSubgroup.closure (c12ConnectionSet : Set (ZMod 12)) = ⊤) ∧
  c12FixedConnectionCI

end

end MathlibPlus.Open.GraphTheory
