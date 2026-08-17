import Mathlib

open scoped Classical BigOperators
noncomputable section

namespace MathlibPlus.Open.Research.R1943InternalDiameter36417

abbrev Vec2 := Fin 2 → ℝ

def vecXY (x y : ℝ) : Vec2 := ![x, y]

def normSq (x : Vec2) : ℝ := ∑ i : Fin 2, x i ^ 2

def distSq (x y : Vec2) : ℝ := normSq (x - y)

def patchPoint (b w v : Vec2) (i j : ℕ) : Vec2 :=
  b + (i : ℝ) • w + (j : ℝ) • v

def patchSet (N : ℕ) (b w v : Vec2) : Set Vec2 :=
  {x | ∃ i j : ℕ, i + j ≤ N ∧ x = patchPoint b w v i j}

def rotateAround (b : Vec2) (θ : ℝ) (x : Vec2) : Vec2 :=
  vecXY
    (b 0 + Real.cos θ * (x 0 - b 0) - Real.sin θ * (x 1 - b 1))
    (b 1 + Real.sin θ * (x 0 - b 0) + Real.cos θ * (x 1 - b 1))

def rotatedPatch (N : ℕ) (b w v : Vec2) (θ : ℝ) : Set Vec2 :=
  {x | ∃ y ∈ patchSet N b w v, x = rotateAround b θ y}

def diameterSquared (S : Set Vec2) : ℝ :=
  sSup {d : ℝ | ∃ x ∈ S, ∃ y ∈ S, d = distSq x y}

def bridgePatch (a b : Vec2) (N : ℕ) (w v : Vec2) : Set Vec2 :=
  insert a (insert b (patchSet N b w v))

def rotatedBridgePatch (a b : Vec2) (N : ℕ)
    (w v : Vec2) (θ : ℝ) : Set Vec2 :=
  insert a (insert b (rotatedPatch N b w v θ))

/-- Claim 36417: the internal diagonal dominates all singleton-to-patch
pairs, and a small bridge-preserving rotation leaves the diameter unchanged. -/
def claim36417 : Prop :=
  ∀ m : ℕ, 6 ≤ m →
    let t : ℝ := 1 / Real.sqrt 3 - 1 / (m : ℝ)
    let w : Vec2 :=
      vecXY ((1 - t ^ 2) / (1 + t ^ 2)) (2 * t / (1 + t ^ 2))
    let v : Vec2 := vecXY (-1 / 2) (Real.sqrt 3 / 2)
    let a : Vec2 := vecXY 0 0
    let b : Vec2 := vecXY 1 0
    let rho : ℝ := ∑ i : Fin 2, w i * v i
    let ell : ℝ := Real.sqrt (2 - 2 * rho)
    let N : ℕ := Nat.ceil (2 / (ell - 1))
    let Z : Set Vec2 := patchSet N b w v
    (normSq w = 1 ∧ normSq v = 1 ∧ 0 < rho ∧ rho < 1 / 2 ∧
      ell = Real.sqrt (2 - 2 * rho) ∧ 1 < ell) ∧
      (∀ z ∈ Z, distSq a z ≤ ((N : ℝ) + 1) ^ 2) ∧
        distSq (b + (N : ℝ) • w) (b + (N : ℝ) • v) =
          ((N : ℝ) * ell) ^ 2 ∧
          (N : ℝ) * ell ≥ (N : ℝ) + 2 ∧
            diameterSquared (bridgePatch a b N w v) =
              distSq (b + (N : ℝ) • w) (b + (N : ℝ) • v) ∧
              ∃ ε : ℝ, 0 < ε ∧
                ∀ θ : ℝ, -ε < θ → θ < 0 →
                  diameterSquared (rotatedBridgePatch a b N w v θ) =
                    diameterSquared (bridgePatch a b N w v)

end MathlibPlus.Open.Research.R1943InternalDiameter36417
