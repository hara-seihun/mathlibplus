import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Research.GroupTheory.R1343OrbitFiber41142

abbrev Base := Fin 3 → ZMod 2
abbrev Voltage (r : ℕ) := Fin r → ZMod 3
abbrev FiberState (r : ℕ) := Base × Voltage r

def profileMap {r : ℕ}
    (σ : Base ≃ Base) (s : Base → Voltage r) : FiberState r → FiberState r :=
  fun x => (σ x.1, x.2 + s x.1)

def baseDerivative
    (σ : Base ≃ Base) (u a : Base) : Base :=
  σ.symm (σ (a + u) + σ u)

def voltageDerivative {r : ℕ}
    (σ : Base ≃ Base) (s : Base → Voltage r)
    (u a : Base) : Voltage r :=
  s (a + u) - s u - s (baseDerivative σ u a)

def derivativeMap {r : ℕ}
    (σ : Base ≃ Base) (s : Base → Voltage r) (u : Base)
    (x : FiberState r) : FiberState r :=
  (baseDerivative σ u x.1,
    x.2 + voltageDerivative σ s u x.1)

def derivativeStepRelation {r : ℕ}
    (σ : Base ≃ Base) (s : Base → Voltage r)
    (x y : FiberState r) : Prop :=
  ∃ u : Base,
    derivativeMap σ s u x = y ∨ derivativeMap σ s u y = x

def derivativeOrbit {r : ℕ}
    (σ : Base ≃ Base) (s : Base → Voltage r)
    (x : FiberState r) : Set (FiberState r) :=
  {y | Relation.ReflTransGen
      (derivativeStepRelation σ s) x y}

/-- Claim 41142: every normalized fiber-preserving profile fixes every orbit
of the complete normalized relative-derivative carrier. -/
def claim41142 : Prop :=
  ∀ (r : ℕ) (σ : Base ≃ Base) (s : Base → Voltage r),
    σ 0 = 0 → s 0 = 0 →
      ∀ x : FiberState r,
        Set.image (profileMap σ s) (derivativeOrbit σ s x) =
          derivativeOrbit σ s x

end MathlibPlus.Open.Research.GroupTheory.R1343OrbitFiber41142
