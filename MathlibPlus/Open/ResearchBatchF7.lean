import Mathlib

namespace MathlibPlus.Open.ResearchBatchF7

noncomputable section

abbrev V7 := ZMod 7 × ZMod 7
abbrev G4684 := ZMod 3 × V7

def f7Nonzero : Set (ZMod 7) :=
  {a | 1 ≤ a.val ∧ a.val ≤ 6}

def exponentRange : Set ℕ := Set.Icc 1 6

def triangularMap (c d : ZMod 7) (k l : ℕ) : V7 → V7 :=
  fun p =>
    let x := p.1
    let y := p.2
    (x + c * y ^ k, y + d * (x + c * y ^ k) ^ l)

def triangularInverse (c d : ZMod 7) (k l : ℕ) : V7 → V7 :=
  fun p =>
    let x := p.1
    let y := p.2 - d * p.1 ^ l
    (x - c * y ^ k, y)

def scalarAction (i : ZMod 3) (v : V7) : V7 :=
  ((2 : ZMod 7) ^ i.val * v.1, (2 : ZMod 7) ^ i.val * v.2)

def semidirectMul (g h : G4684) : G4684 :=
  (g.1 + h.1, g.2 + scalarAction g.1 h.2)

def semidirectOne : G4684 := (0, (0, 0))

def semidirectGroupAxioms : Prop :=
  (∀ a b c, semidirectMul (semidirectMul a b) c = semidirectMul a (semidirectMul b c)) ∧
    (∀ g, semidirectMul semidirectOne g = g ∧ semidirectMul g semidirectOne = g) ∧
    (∀ g, ∃ h, semidirectMul g h = semidirectOne ∧ semidirectMul h g = semidirectOne)

def layerExtension (c d : ZMod 7) (k l : ℕ) : G4684 → G4684 :=
  fun g =>
    if g.1 = 0 then (0, triangularMap c d k l g.2) else g

def groupAutomorphismOfLayeredCarrier (φ : G4684 → G4684) : Prop :=
  Function.Bijective φ ∧
    (∀ g h, φ (semidirectMul g h) = semidirectMul (φ g) (φ h)) ∧
    (∀ g, (φ g).1 = g.1) ∧ φ semidirectOne = semidirectOne

/-- Two inverse triangular shears over `F₇`, followed by the normalized
layer extension on the concrete scalar semidirect carrier. -/
def twoWayTriangularMapsOverF7 : Prop :=
  semidirectGroupAxioms ∧
    ∀ (c d : ZMod 7) (k l : ℕ),
      c ∈ f7Nonzero → d ∈ f7Nonzero → k ∈ exponentRange → l ∈ exponentRange →
        Function.LeftInverse (triangularInverse c d k l) (triangularMap c d k l) ∧
          Function.RightInverse (triangularInverse c d k l) (triangularMap c d k l) ∧
          Function.Bijective (triangularMap c d k l) ∧
          Function.Bijective (layerExtension c d k l) ∧
          layerExtension c d k l semidirectOne = semidirectOne

def scalarLinearMap (a : ZMod 7) : V7 →ₗ[ZMod 7] V7 :=
  a • LinearMap.id

def layerMap (A : V7 ≃ₗ[ZMod 7] V7) (z : V7) : G4684 → G4684 :=
  fun g =>
    if g.1 = 0 then
      (0, A g.2)
    else if g.1 = 1 then
      (1, A g.2 + z)
    else
      (2, A g.2 + z + (2 : ZMod 7) • z)

def quotientInvertingCaseExcluded : Prop :=
  ¬ ∃ A : V7 ≃ₗ[ZMod 7] V7,
    A.toLinearMap.comp (scalarLinearMap 2) =
      (scalarLinearMap 4).comp A.toLinearMap

/-- The affine layer maps induced by all linear `A` and translations `z`, and
exclusion of the quotient-inverting alternative. -/
def scalarSemidirectAutomorphisms : Prop :=
  semidirectGroupAxioms ∧
    (∀ (A : V7 ≃ₗ[ZMod 7] V7) (z : V7),
      groupAutomorphismOfLayeredCarrier (layerMap A z)) ∧
    quotientInvertingCaseExcluded

end
end MathlibPlus.Open.ResearchBatchF7
