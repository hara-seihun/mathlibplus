import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2062Claim35951

noncomputable section

abbrev Point := ℝ × ℝ

def dot (u v : Point) : ℝ :=
  u.1 * v.1 + u.2 * v.2

def squaredDistance (u v : Point) : ℝ :=
  dot (u - v) (u - v)

def distance (u v : Point) : ℝ :=
  Real.sqrt (squaredDistance u v)

def rotateVector (theta : ℝ) (u : Point) : Point :=
  (Real.cos theta * u.1 - Real.sin theta * u.2,
    Real.sin theta * u.1 + Real.cos theta * u.2)

def rotateAbout (a u : Point) (theta : ℝ) : Point :=
  a + rotateVector theta (u - a)

def planarDiameterMinimizer
    (n : ℕ) (X : Set Point) (D : ℝ) : Prop :=
  X.Finite ∧
    X.ncard = n ∧
    (∀ u ∈ X, ∀ v ∈ X, u ≠ v → 1 ≤ distance u v) ∧
    (∃ u ∈ X, ∃ v ∈ X, u ≠ v ∧ distance u v = 1) ∧
    (∀ u ∈ X, ∀ v ∈ X, distance u v ≤ D) ∧
    (∃ u ∈ X, ∃ v ∈ X, u ≠ v ∧ distance u v = D) ∧
    (∀ Y : Set Point, ∀ E : ℝ,
      Y.Finite →
      Y.ncard = n →
      (∀ u ∈ Y, ∀ v ∈ Y, u ≠ v → 1 ≤ distance u v) →
      (∀ u ∈ Y, ∀ v ∈ Y, distance u v ≤ E) →
      D ≤ E)

def unitTriangleFree (X : Set Point) : Prop :=
  ∀ u ∈ X, ∀ v ∈ X, ∀ w ∈ X,
    u ≠ v → u ≠ w → v ≠ w →
      ¬ (distance u v = 1 ∧ distance u w = 1 ∧ distance v w = 1)

def activeAdjacency (X : Set Point) (D : ℝ) (u v : Point) : Prop :=
  u ∈ X ∧ v ∈ X ∧ u ≠ v ∧
    (distance u v = 1 ∨ distance u v = D)

def activeReachable (X : Set Point) (D : ℝ) (u v : Point) : Prop :=
  Relation.ReflTransGen (activeAdjacency X D) u v

def activeConnected (X : Set Point) (D : ℝ) : Prop :=
  ∀ u ∈ X, ∀ v ∈ X, activeReachable X D u v

def deletedActiveAdjacency
    (X : Set Point) (D : ℝ) (a b u v : Point) : Prop :=
  activeAdjacency X D u v ∧
    ¬ ((u = a ∧ v = b) ∨ (u = b ∧ v = a))

def activeBridge (X : Set Point) (D : ℝ) (a b : Point) : Prop :=
  activeAdjacency X D a b ∧
    ¬ Relation.ReflTransGen (deletedActiveAdjacency X D a b) a b

def activeSideReachable
    (X : Set Point) (D : ℝ) (S : Set Point) (u v : Point) : Prop :=
  Relation.ReflTransGen
    (fun x y => x ∈ S ∧ y ∈ S ∧ activeAdjacency X D x y) u v

def activeSideConnected
    (X : Set Point) (D : ℝ) (S : Set Point) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, activeSideReachable X D S u v

def bridgeCut
    (X : Set Point) (D : ℝ) (a b : Point)
    (W Z : Set Point) : Prop :=
  activeBridge X D a b ∧
    W ⊆ X ∧ Z ⊆ X ∧ Disjoint W Z ∧ W ∪ Z = X ∧
    a ∈ W ∧ b ∈ Z ∧
    activeSideConnected X D W ∧ activeSideConnected X D Z ∧
    (∀ u ∈ W, ∀ z ∈ Z,
      activeAdjacency X D u z ↔ u = a ∧ z = b)

def movedConfiguration
    (X W Z : Set Point) (a : Point) (theta : ℝ) : Set Point :=
  Set.image (fun u : Point => rotateAbout a u theta) W ∪ (X \ W)

def movedSide (W : Set Point) (a : Point) (theta : ℝ) : Set Point :=
  Set.image (fun u : Point => rotateAbout a u theta) W

def crossActivationEventAt
    (X W Z : Set Point) (D : ℝ)
    (a b : Point) (theta : ℝ) : Prop :=
  ∃ u ∈ W, ∃ z ∈ Z,
    (u ≠ a ∨ z ≠ b) ∧
      activeAdjacency (movedConfiguration X W Z a theta) D
        (rotateAbout a u theta) z

def firstPositiveEvent
    (X W Z : Set Point) (D : ℝ)
    (a b : Point) (theta : ℝ) : Prop :=
  0 < theta ∧ theta < 2 * Real.pi ∧
    crossActivationEventAt X W Z D a b theta ∧
    ∀ phi : ℝ, 0 < phi → phi < theta →
      ¬ crossActivationEventAt X W Z D a b phi

def firstNegativeEvent
    (X W Z : Set Point) (D : ℝ)
    (a b : Point) (theta : ℝ) : Prop :=
  -2 * Real.pi < theta ∧ theta < 0 ∧
    crossActivationEventAt X W Z D a b theta ∧
    ∀ phi : ℝ, theta < phi → phi < 0 →
      ¬ crossActivationEventAt X W Z D a b phi

def newCrossCycle
    (X W Z : Set Point) (D : ℝ) (a b : Point) (theta : ℝ) : Prop :=
  ∃ u ∈ W, ∃ z ∈ Z,
    (u ≠ a ∨ z ≠ b) ∧
      activeAdjacency (movedConfiguration X W Z a theta) D
        (rotateAbout a u theta) z ∧
      activeSideReachable
        (movedConfiguration X W Z a theta) D
        (movedSide W a theta) a (rotateAbout a u theta) ∧
      activeSideReachable
        (movedConfiguration X W Z a theta) D Z z b

def endpointData
    (n : ℕ) (X W Z : Set Point) (D : ℝ)
    (a b : Point) (theta : ℝ) : Prop :=
  planarDiameterMinimizer n (movedConfiguration X W Z a theta) D ∧
    newCrossCycle X W Z D a b theta

def spanningUnitEquilateral
    (W Z : Set Point) (a : Point) (theta : ℝ) : Prop :=
  ∃ u v w : Point,
    u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      ((u ∈ W ∧ v ∈ W ∧ w ∈ Z ∧
          distance (rotateAbout a u theta) (rotateAbout a v theta) = 1 ∧
          distance (rotateAbout a u theta) w = 1 ∧
          distance (rotateAbout a v theta) w = 1) ∨
        (u ∈ W ∧ v ∈ Z ∧ w ∈ Z ∧
          distance (rotateAbout a u theta) v = 1 ∧
          distance (rotateAbout a u theta) w = 1 ∧
          distance v w = 1))

def safeEndpoint
    (n : ℕ) (X W Z : Set Point) (D : ℝ)
    (a b : Point) (theta : ℝ) : Prop :=
  endpointData n X W Z D a b theta ∧
    unitTriangleFree (movedConfiguration X W Z a theta) ∧
    ¬ activeBridge (movedConfiguration X W Z a theta) D a b

def theoremForEveryActiveBridge_claim35951 : Prop :=
  ∀ (n : ℕ) (X : Set Point) (D : ℝ),
    3 ≤ n →
      planarDiameterMinimizer n X D →
        unitTriangleFree X →
          activeConnected X D →
            ∀ a b : Point, activeBridge X D a b →
              ∃ a' b' : Point, ∃ W Z : Set Point,
                ((a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)) ∧
                  bridgeCut X D a' b' W Z ∧
                  2 ≤ W.ncard ∧
                  ∃ thetaPos thetaNeg : ℝ,
                    firstPositiveEvent X W Z D a' b' thetaPos ∧
                    firstNegativeEvent X W Z D a' b' thetaNeg ∧
                    endpointData n X W Z D a' b' thetaPos ∧
                    endpointData n X W Z D a' b' thetaNeg ∧
                    (safeEndpoint n X W Z D a' b' thetaPos ∨
                      safeEndpoint n X W Z D a' b' thetaNeg ∨
                      (spanningUnitEquilateral W Z a' thetaPos ∧
                        spanningUnitEquilateral W Z a' thetaNeg))

end

end MathlibPlus.Open.ResearchFormalization.R2062Claim35951
