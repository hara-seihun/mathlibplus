import Mathlib

namespace MathlibPlus.Open.ResearchBatch.R1542Claims

abbrev W (p : ℕ) := Fin 3 → ZMod p
abbrev H (p : ℕ) := ZMod p × ZMod 3
abbrev G (p : ℕ) := W p × H p

 def omegaPower {p : ℕ} (ω : ZMod p) (i : ZMod 3) : ZMod p :=
  ω ^ i.val

def scalarCubeRoot {p : ℕ} (ω : ZMod p) : Prop :=
  ω ≠ 1 ∧ ω ^ 3 = 1

def hMul {p : ℕ} (ω : ZMod p) (x y : H p) : H p :=
  (x.1 + omegaPower ω x.2 * y.1, x.2 + y.2)

def hInv {p : ℕ} (ω : ZMod p) (x : H p) : H p :=
  (-(omegaPower ω (-x.2)) * x.1, -x.2)

def hZero {p : ℕ} : H p := (0, 0)

def gMul {p : ℕ} (ω : ZMod p) (x y : G p) : G p :=
  (x.1 + omegaPower ω x.2.2 • y.1, hMul ω x.2 y.2)

def gInv {p : ℕ} (ω : ZMod p) (x : G p) : G p :=
  (-(omegaPower ω (-x.2.2)) • x.1, hInv ω x.2)

def gZero {p : ℕ} : G p := (0, hZero)

def scalarGroupLaw {p : ℕ} (ω : ZMod p) : Prop :=
  (∀ x y z : G p, gMul ω (gMul ω x y) z = gMul ω x (gMul ω y z)) ∧
    (∀ x : G p,
      gMul ω (gZero) x = x ∧ gMul ω x (gZero) = x ∧
        gMul ω (gInv ω x) x = gZero ∧ gMul ω x (gInv ω x) = gZero)

def dot3 {p : ℕ} (x y : W p) : ZMod p :=
  ∑ i, x i * y i

def slopeValue {p : ℕ} (t : Fin 5) : ZMod p :=
  t.val

def hSlope {p : ℕ} (ω : ZMod p) (t : Fin 5) : H p :=
  ((1 - ω) * slopeValue t, 1)

def nSlope {p : ℕ} (t : Fin 5) : W p :=
  ![1, slopeValue t, (slopeValue t) ^ 2]

def directionPlane {p : ℕ} (ω : ZMod p) (a : ZMod p) : Set (W p) :=
  {w | dot3 ![1, a, a ^ 2] w = 0}

def plane {p : ℕ} (ω : ZMod p) (t : Fin 5) : Set (W p) :=
  directionPlane ω (slopeValue t)

def tau {p : ℕ} (h : H p) : W p :=
  ![h.1 ^ 4, -4 * h.1 ^ 3, 6 * h.1 ^ 2]

def normalizedBijection {p : ℕ} : G p → G p :=
  fun g => (g.1 + tau g.2, g.2)

def basis {p : ℕ} (i : Fin 3) : W p :=
  fun j => if i = j then 1 else 0

def marker {p : ℕ} : Set (W p) :=
  {w |
    w = basis 0 ∨ w = -basis 0 ∨
    w = basis 1 ∨ w = -basis 1 ∨
    w = basis 2 ∨ w = -basis 2 ∨
    w = basis 0 + basis 2 ∨ w = -(basis 0 + basis 2) ∨
    w = basis 0 + (2 : ZMod p) • basis 1 + (3 : ZMod p) • basis 2 ∨
    w = -(basis 0 + (2 : ZMod p) • basis 1 + (3 : ZMod p) • basis 2)}

def markerSection {p : ℕ} : Set (G p) :=
  {g | g.1 ∈ marker ∧ g.2 = hZero}

def planeSection {p : ℕ} (ω : ZMod p) (t : Fin 5) : Set (G p) :=
  {g | g.1 ∈ plane ω t ∧ g.2 = hSlope ω t}

def inverseSection {p : ℕ} (ω : ZMod p) (t : Fin 5) : Set (G p) :=
  gInv ω '' planeSection ω t

def sourceConnection {p : ℕ} (ω : ZMod p) : Set (G p) :=
  markerSection ∪ ⋃ t : Fin 5, (planeSection ω t ∪ inverseSection ω t)

def targetConnection {p : ℕ} (ω : ZMod p) : Set (G p) :=
  normalizedBijection '' sourceConnection ω

def leftCayleyEdge {p : ℕ} (ω : ZMod p) (S : Set (G p))
    (x y : G p) : Prop :=
  ∃ s, s ∈ S ∧ y = gMul ω s x

def undirectedCayleyEdge {p : ℕ} (ω : ZMod p) (S : Set (G p))
    (x y : G p) : Prop :=
  x ≠ y ∧ (leftCayleyEdge ω S x y ∨ leftCayleyEdge ω S y x)

def identityFree {p : ℕ} (S : Set (G p)) : Prop :=
  gZero ∉ S

def inverseClosed {p : ℕ} (ω : ZMod p) (S : Set (G p)) : Prop :=
  ∀ x, x ∈ S ↔ gInv ω x ∈ S

def connectedCayley {p : ℕ} (ω : ZMod p) (S : Set (G p)) : Prop :=
  ∀ x y : G p,
    Relation.ReflTransGen (undirectedCayleyEdge ω S) x y

def groupAutomorphism {p : ℕ} (ω : ZMod p) (φ : G p → G p) : Prop :=
  Function.Bijective φ ∧
    ∀ x y, φ (gMul ω x y) = gMul ω (φ x) (φ y)

def undirectedGraphIsomorphism {p : ℕ} (ω : ZMod p)
    (S T : Set (G p)) : Prop :=
  ∃ f : G p → G p,
    Function.Bijective f ∧
      ∀ x y, undirectedCayleyEdge ω S x y ↔
        undirectedCayleyEdge ω T (f x) (f y)

def ordinaryUndirectedCI {p : ℕ} (ω : ZMod p) : Prop :=
  ∀ S T : Set (G p),
    identityFree S → inverseClosed ω S →
    identityFree T → inverseClosed ω T →
    undirectedGraphIsomorphism ω S T →
    ∃ φ : G p → G p, groupAutomorphism ω φ ∧ φ '' S = T

def affineMap {p : ℕ} (b c x : ZMod p) : ZMod p :=
  b + c * x

def baseSupport {p : ℕ} (ω : ZMod p) : Set (ZMod p) :=
  {x | ∃ t : Fin 5, x = (1 - ω) * slopeValue t}

def affineBaseSelfMap {p : ℕ} (ω b c : ZMod p) : Prop :=
  Function.Bijective (affineMap b c) ∧
    affineMap b c '' baseSupport ω = baseSupport ω

def mappedSlope {p : ℕ} (ω b c : ZMod p) (t : Fin 5) : ZMod p :=
  (1 - ω)⁻¹ * affineMap b c ((1 - ω) * slopeValue t)

def preservesPlaneDirections {p : ℕ} (ω b c : ZMod p) : Prop :=
  ∀ t : Fin 5,
    directionPlane ω (mappedSlope ω b c t) = plane ω t

def positiveLayerAction {p : ℕ} (φ : G p → G p)
    (A : (W p × ZMod p) → (W p × ZMod p)) : Prop :=
  ∀ w a, φ (w, (a, (1 : ZMod 3))) =
    ((A (w, a)).1, ((A (w, a)).2, (1 : ZMod 3)))

def affineTransporterForm {p : ℕ}
    (A : (W p × ZMod p) → (W p × ZMod p)) : Prop :=
  ∃ ε : ZMod p, ∃ u : W p, ∃ c : ZMod p,
    (ε = 1 ∨ ε = -1) ∧ c ≠ 0 ∧
      ∀ w a, A (w, a) = (ε • w + a • u, c * a)

/-- Claim 37783: the base-support symmetries, their direction obstruction,
and the resulting affine transporter normal form. -/
def claim_37783 : Prop :=
  ∀ p : ℕ, Nat.Prime p → p % 3 = 1 →
    ∀ ω : ZMod p, scalarCubeRoot ω →
      (∀ b c : ZMod p,
        affineBaseSelfMap ω b c →
          ((b = 0 ∧ c = 1) ∨ (b = 4 * (1 - ω) ∧ c = -1))) ∧
      ¬ preservesPlaneDirections ω (4 * (1 - ω)) (-1) ∧
      (∀ φ : G p → G p,
        groupAutomorphism ω φ →
          φ '' sourceConnection ω = targetConnection ω →
          ∃ A : (W p × ZMod p) → (W p × ZMod p),
            positiveLayerAction φ A ∧ affineTransporterForm A)

/-- Claim 37788: the uniform connected inverse-closed witness lies in a
nontrivial graph-isomorphism fibre but outside the full group-automorphism
orbit. -/
def claim_37788 : Prop :=
  ∀ p : ℕ, Nat.Prime p → p % 3 = 1 →
    ∃ ω : ZMod p,
      scalarCubeRoot ω ∧ scalarGroupLaw ω ∧
        let S := sourceConnection ω
        let T := targetConnection ω
        identityFree S ∧ identityFree T ∧
          inverseClosed ω S ∧ inverseClosed ω T ∧
          Set.ncard S = 10 * p ^ 2 + 10 ∧
          Set.ncard T = 10 * p ^ 2 + 10 ∧
          connectedCayley ω S ∧ connectedCayley ω T ∧
          Function.Bijective (normalizedBijection (p := p)) ∧
          (∀ x y : G p,
            leftCayleyEdge ω S x y ↔
              leftCayleyEdge ω T
                (normalizedBijection x) (normalizedBijection y)) ∧
          (¬ ∃ φ : G p → G p,
            groupAutomorphism ω φ ∧ φ '' S = T) ∧
          ¬ ordinaryUndirectedCI ω

end MathlibPlus.Open.ResearchBatch.R1542Claims
