import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.StressSupport

noncomputable section

abbrev Point := Fin 2 → ℝ
abbrev Edge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

def edgeFirst {n : ℕ} (e : Edge n) : Fin n := e.1.1

def edgeSecond {n : ℕ} (e : Edge n) : Fin n := e.1.2

def planarDistance (x y : Point) : ℝ :=
  Real.sqrt (∑ k : Fin 2, (x k - y k) ^ 2)

def edgeVector {n : ℕ} (X : Fin n → Point) (e : Edge n) : Point :=
  X (edgeFirst e) - X (edgeSecond e)

def edgeWithin {n : ℕ} (K : Finset (Fin n)) (e : Edge n) : Prop :=
  edgeFirst e ∈ K ∧ edgeSecond e ∈ K

def edgesWithin {n : ℕ} (K : Finset (Fin n)) (A : Finset (Edge n)) : Finset (Edge n) := by
  classical
  exact A.filter (edgeWithin K)

def supportStep {n : ℕ} (ω : Edge n → ℝ) (u v : Fin n) : Prop :=
  ∃ e, ω e ≠ 0 ∧
    ((edgeFirst e = u ∧ edgeSecond e = v) ∨
      (edgeFirst e = v ∧ edgeSecond e = u))

def supportReachable {n : ℕ} (ω : Edge n → ℝ) (u v : Fin n) : Prop :=
  Relation.ReflTransGen (supportStep ω) u v

def supportStepWithout {n : ℕ} (ω : Edge n → ℝ) (removed : Edge n)
    (u v : Fin n) : Prop :=
  ∃ e, e ≠ removed ∧ ω e ≠ 0 ∧
    ((edgeFirst e = u ∧ edgeSecond e = v) ∨
      (edgeFirst e = v ∧ edgeSecond e = u))

def supportReachableWithout {n : ℕ} (ω : Edge n → ℝ) (removed : Edge n)
    (u v : Fin n) : Prop :=
  Relation.ReflTransGen (supportStepWithout ω removed) u v

def isSupportComponent {n : ℕ} (ω : Edge n → ℝ) (K : Finset (Fin n)) : Prop :=
  K.Nonempty ∧
    (∀ u ∈ K, ∀ v ∈ K, supportReachable ω u v) ∧
    (∀ u ∈ K, ∀ v, supportReachable ω u v → v ∈ K)

def isSupportBridge {n : ℕ} (ω : Edge n → ℝ) (K : Finset (Fin n))
    (e : Edge n) : Prop :=
  edgeFirst e ∈ K ∧ edgeSecond e ∈ K ∧ ω e ≠ 0 ∧
    ∃ u ∈ K, ∃ v ∈ K, ¬ supportReachableWithout ω e u v

def stressContribution {n : ℕ} (X : Fin n → Point) (ω : Edge n → ℝ)
    (i : Fin n) (e : Edge n) : Point :=
  if edgeFirst e = i then
    ω e • (X i - X (edgeSecond e))
  else if edgeSecond e = i then
    ω e • (X i - X (edgeFirst e))
  else 0

def vertexEquilibrium {n : ℕ} (X : Fin n → Point) (ω : Edge n → ℝ) : Prop :=
  ∀ i, ∑ e : Edge n, stressContribution X ω i e = 0

def edgeMomentMatrix {n : ℕ} (X : Fin n → Point) (K : Finset (Fin n))
    (A : Finset (Edge n)) (w : Edge n → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => ∑ e ∈ edgesWithin K A, w e * edgeVector X e i * edgeVector X e j

def scaledMomentMatrix {n : ℕ} (r : ℝ) (X : Fin n → Point)
    (K : Finset (Fin n)) (A : Finset (Edge n)) (w : Edge n → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => r * edgeMomentMatrix X K A w i j

def supportDegree {n : ℕ} (ω : Edge n → ℝ) (v : Fin n) : ℕ :=
  ((Finset.univ : Finset (Edge n)).filter (fun e =>
    ω e ≠ 0 ∧ (edgeFirst e = v ∨ edgeSecond e = v))).card

def supportEdgeOnCycle {n : ℕ} (ω : Edge n → ℝ) (K : Finset (Fin n))
    (e : Edge n) : Prop :=
  edgeFirst e ∈ K ∧ edgeSecond e ∈ K ∧ ω e ≠ 0 ∧
    supportReachableWithout ω e (edgeFirst e) (edgeSecond e)

def balancedPlanarStressContext {n : ℕ} (X : Fin n → Point)
    (C H : Finset (Edge n)) (α β : Edge n → ℝ) (D : ℝ)
    (ω : Edge n → ℝ) : Prop :=
  0 < D ∧
  (∀ e, 1 ≤ planarDistance (X (edgeFirst e)) (X (edgeSecond e))) ∧
  (∀ e, planarDistance (X (edgeFirst e)) (X (edgeSecond e)) ≤ D) ∧
  (∀ e, e ∈ C ↔ planarDistance (X (edgeFirst e)) (X (edgeSecond e)) = 1) ∧
  (∀ e, e ∈ H ↔ planarDistance (X (edgeFirst e)) (X (edgeSecond e)) = D) ∧
  (∀ e, 0 ≤ α e) ∧ (∀ e, e ∉ C → α e = 0) ∧
  (∑ e ∈ C, α e) = 1 ∧
  (∀ e, 0 ≤ β e) ∧ (∀ e, e ∉ H → β e = 0) ∧
  (∑ e ∈ H, β e) = 1 ∧
  (∀ e, ω e =
    (if e ∈ C then α e else 0) -
      (if e ∈ H then β e / D ^ 2 else 0)) ∧
  Function.Injective X ∧ vertexEquilibrium X ω

def noPositiveStressBridge : Prop :=
  ∀ (n : ℕ) (X : Fin n → Point) (C H : Finset (Edge n))
    (α β : Edge n → ℝ) (D : ℝ) (ω : Edge n → ℝ),
    balancedPlanarStressContext X C H α β D ω →
    ∀ K, isSupportComponent ω K → 2 ≤ K.card →
      ∀ e, ¬ isSupportBridge ω K e

def supportCycleAndMinimumDegree : Prop :=
  ∀ (n : ℕ) (X : Fin n → Point) (C H : Finset (Edge n))
    (α β : Edge n → ℝ) (D : ℝ) (ω : Edge n → ℝ),
    balancedPlanarStressContext X C H α β D ω →
    ∀ K, isSupportComponent ω K → 2 ≤ K.card →
      (∀ v ∈ K, 2 ≤ supportDegree ω v) ∧
      (∀ e, edgeFirst e ∈ K → edgeSecond e ∈ K → ω e ≠ 0 →
        supportEdgeOnCycle ω K e)

def componentSupportedAffineMomentIdentity : Prop :=
  ∀ (n : ℕ) (X : Fin n → Point) (C H : Finset (Edge n))
    (α β : Edge n → ℝ) (D : ℝ) (ω : Edge n → ℝ),
    balancedPlanarStressContext X C H α β D ω →
    ∀ K, isSupportComponent ω K →
      edgeMomentMatrix X K C α =
        scaledMomentMatrix (D ^ (-2 : ℤ)) X K H β

def equalContactFarthestMassOnSupportComponent : Prop :=
  ∀ (n : ℕ) (X : Fin n → Point) (C H : Finset (Edge n))
    (α β : Edge n → ℝ) (D : ℝ) (ω : Edge n → ℝ),
    balancedPlanarStressContext X C H α β D ω →
    ∀ K, isSupportComponent ω K → 2 ≤ K.card →
      (∑ e ∈ edgesWithin K C, α e) =
        (∑ e ∈ edgesWithin K H, β e) ∧
      0 < (∑ e ∈ edgesWithin K C, α e)

def squarePoint (i : Fin 4) : Point :=
  if i = 0 then ![0, 0]
  else if i = 1 then ![1, 0]
  else if i = 2 then ![1, 1]
  else ![0, 1]

def squareSideEdges : Finset (Edge 4) :=
  let e01 : Edge 4 := ⟨((0 : Fin 4), (1 : Fin 4)), by decide⟩
  let e12 : Edge 4 := ⟨((1 : Fin 4), (2 : Fin 4)), by decide⟩
  let e23 : Edge 4 := ⟨((2 : Fin 4), (3 : Fin 4)), by decide⟩
  let e03 : Edge 4 := ⟨((0 : Fin 4), (3 : Fin 4)), by decide⟩
  {e01, e12, e23, e03}

def squareDiagonalEdges : Finset (Edge 4) :=
  let e02 : Edge 4 := ⟨((0 : Fin 4), (2 : Fin 4)), by decide⟩
  let e13 : Edge 4 := ⟨((1 : Fin 4), (3 : Fin 4)), by decide⟩
  {e02, e13}

def squareContactWeight (e : Edge 4) : ℝ :=
  if e ∈ squareSideEdges then (1 : ℝ) / 4 else 0

def squareFarthestWeight (e : Edge 4) : ℝ :=
  if e ∈ squareDiagonalEdges then (1 : ℝ) / 2 else 0

def squareDiameter : ℝ := Real.sqrt 2

def squareStress (e : Edge 4) : ℝ :=
  squareContactWeight e - squareFarthestWeight e / squareDiameter ^ 2

def squareIdentity : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then (1 : ℝ) / 2 else 0

def unitSquareKKTWitness : Prop :=
  let K : Finset (Fin 4) := Finset.univ
  let C : Finset (Edge 4) := squareSideEdges
  let H : Finset (Edge 4) := squareDiagonalEdges
  (∀ e ∈ C, planarDistance (squarePoint (edgeFirst e))
      (squarePoint (edgeSecond e)) = 1) ∧
  (∀ e ∈ H, planarDistance (squarePoint (edgeFirst e))
      (squarePoint (edgeSecond e)) = squareDiameter) ∧
  (∀ e : Edge 4, squareContactWeight e =
      if e ∈ C then (1 : ℝ) / 4 else 0) ∧
  (∀ e : Edge 4, squareFarthestWeight e =
      if e ∈ H then (1 : ℝ) / 2 else 0) ∧
  vertexEquilibrium squarePoint squareStress ∧
  isSupportComponent squareStress K ∧
  (∀ e : Edge 4, ¬ isSupportBridge squareStress K e) ∧
  (∑ e ∈ edgesWithin K C, squareContactWeight e) =
    (∑ e ∈ edgesWithin K H, squareFarthestWeight e) ∧
  edgeMomentMatrix squarePoint K C squareContactWeight = squareIdentity ∧
  scaledMomentMatrix (squareDiameter ^ (-2 : ℤ)) squarePoint K H squareFarthestWeight =
    squareIdentity

end

end MathlibPlus.Open.StressSupport
