import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.R1845

noncomputable section

abbrev F3 := ZMod 3
abbrev F3Pair := Fin 2 → F3
abbrev F3Quad := Fin 4 → F3

def pairOf (v w : F3) : F3Pair := ![v, w]

def NormalizedCarry :=
  {q : F3Pair → F3 // q (0 : F3Pair) = 0}

deriving instance Fintype for NormalizedCarry

def carryMap (q : F3Pair → F3) (z : F3Quad) : F3Quad :=
  let x := z 0
  let u := z 1
  let v := z 2
  let w := z 3
  ![x + v ^ 2 * w, u + q (pairOf v w), v, v + w]

def carryInverse (q : F3Pair → F3) (z : F3Quad) : F3Quad :=
  let x := z 0
  let u := z 1
  let v := z 2
  let w := z 3
  ![x - v ^ 2 * (w - v), u - q (pairOf v (w - v)), v, w - v]

def translationMap (t : F3Quad) : F3Quad → F3Quad :=
  fun z => z + t

def lowerTranslationFamily : Set (F3Quad → F3Quad) :=
  {f | ∃ t : F3Quad, ∀ z, f z = translationMap t z}

def conjugateTranslationFamily (q : F3Pair → F3) : Set (F3Quad → F3Quad) :=
  {f | ∃ t : F3Quad, ∀ z,
    f z = carryMap q (translationMap t (carryInverse q z))}

def IsFunctionGroup (F : Set (F3Quad → F3Quad)) : Prop :=
  (fun z => z) ∈ F ∧
  (∀ f ∈ F, ∀ g ∈ F, (fun z => f (g z)) ∈ F) ∧
  (∀ f ∈ F, ∃ g ∈ F, (∀ z, g (f z) = z) ∧ (∀ z, f (g z) = z))

/-- Claim 32843: normalized carries and the marked translation pair. -/
def normalizedCarryChart_claim32843 : Prop :=
  Nat.card NormalizedCarry = 3 ^ 8 ∧
  (∀ q : NormalizedCarry, ∀ z : F3Quad,
    carryInverse q.1 (carryMap q.1 z) = z ∧
    carryMap q.1 (carryInverse q.1 z) = z) ∧
  IsFunctionGroup lowerTranslationFamily ∧
  Set.ncard lowerTranslationFamily = 3 ^ 4 ∧
  (∀ q : NormalizedCarry,
    IsFunctionGroup (conjugateTranslationFamily q.1) ∧
    Set.ncard (conjugateTranslationFamily q.1) = 3 ^ 4 ∧
    (∀ f, f ∈ conjugateTranslationFamily q.1 ↔
      ∃ t : F3Quad, ∀ z,
        f z = carryMap q.1 (translationMap t (carryInverse q.1 z))))

end
end MathlibPlus.Open.LinearAlgebra.R1845
