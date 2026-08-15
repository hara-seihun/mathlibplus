import Mathlib

namespace MathlibPlus.Open.FormalizationBatchPaths

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V]

def treeDegree (T : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w => T.Adj v w)).card

/-- The local leaf-event load is the stated sum over the other neighbors. -/
def localLeafEventLoadClaim25613 (T : SimpleGraph V) (ℓ v : V) : ℕ := by
  classical
  exact Finset.sum
    (Finset.univ.filter (fun u => T.Adj v u ∧ u ≠ ℓ))
    (fun u => treeDegree T u - 1)

def directedEdge {V : Type*} (E : Finset (V × V)) (u v : V) : Prop :=
  (u, v) ∈ E

def reachesByEdges {V : Type*} (E : Finset (V × V)) (u v : V) : Prop :=
  Relation.ReflTransGen (directedEdge E) u v

/-- The data and filtration defining a strict-host descent graph. -/
def strictHostDescentGraphClaim53710
    (V : Type*) [Fintype V]
    (E : Finset (V × V)) (entries exits : Finset V)
    (rank : V → ℕ) : Prop :=
  entries.Nonempty ∧
  (∀ x ∈ exits, rank x = 1) ∧
  (∀ u v : V, directedEdge E u v → rank v < rank u)

/-- Its rank-one reachability objective is existential path reachability. -/
def strictHostRankOneReachabilityGoalClaim53710
    {V : Type*} (E : Finset (V × V)) (entries exits : Finset V) : Prop :=
  ∃ e ∈ entries, ∃ x ∈ exits, reachesByEdges E e x

/-- A positive scalar circuit with one-dimensional kernel gives a simple closed
potential path for every ordering. -/
def everyOrderingPositiveCircuitPathClaim55571 : Prop := by
  classical
  exact ∀ (S : Type*) [Fintype S] [Nonempty S]
    (W : Type*) [AddCommGroup W] [Module ℚ W]
    (L : (S → ℚ) →ₗ[ℚ] W) (q : S → ℚ),
    (∀ e : S, 0 < q e) →
    LinearMap.ker L = Submodule.span ℚ ({q} : Set (S → ℚ)) →
    ∀ (e : Fin (Fintype.card S) → S), Function.Bijective e →
      ∃ v : Fin (Fintype.card S + 1) → W,
        v 0 = 0 ∧
        (∀ i : Fin (Fintype.card S),
          v i.succ = v i.castSucc -
            q (e i) • L (Pi.single (e i) 1)) ∧
        v (Fin.last (Fintype.card S)) = v 0 ∧
        Function.Injective (fun i : Fin (Fintype.card S) => v i.castSucc) ∧
        (∀ i : Fin (Fintype.card S),
          v i.castSucc - v i.succ = q (e i) • L (Pi.single (e i) 1))

def simplexColumn (k : ℕ) (i : Fin k) : Fin (k - 1) → ℚ := by
  classical
  by_cases h : i.val < k - 1
  · exact Pi.single ⟨i.val, h⟩ 1
  · exact fun _ => -1

def simplexCentering (k : ℕ) (w : Fin (k - 1) → ℚ) : ℚ :=
  ∑ i : Fin (k - 1), (2 : ℚ) ^ i.val * w i

def positiveRelationOnSimplex (k : ℕ) : Prop :=
  ∀ q : Fin k → ℚ,
    (∀ i, 0 < q i) →
    (∑ i : Fin k, q i • simplexColumn k i) = 0 →
    ∃ c : ℚ, 0 < c ∧ ∀ i, q i = c

def simpleClosedPotentialPath (k : ℕ) (e : Fin k → Fin k)
    (v : Fin (k + 1) → (Fin (k - 1) → ℚ)) : Prop :=
  v 0 = 0 ∧
  (∀ i : Fin k,
    v i.succ = v i.castSucc - simplexColumn k (e i)) ∧
  v (Fin.last k) = v 0 ∧
  Function.Injective (fun i : Fin k => v i.castSucc) ∧
  (∀ i : Fin k,
    v i.castSucc - v i.succ = simplexColumn k (e i))

/-- The canonical centered simplex has the unique positive relation, no vanishing
proper partial support, and nevertheless the simple path for every ordering. -/
def canonicalSimplexCenteringCounterexampleClaim55575 : Prop := by
  classical
  exact ∀ k : ℕ, 2 ≤ k →
    (∑ i : Fin k, simplexColumn k i) = 0 ∧
    (positiveRelationOnSimplex k) ∧
    (∀ i : Fin (k - 1),
      simplexCentering k (Pi.single i 1) = (2 : ℚ) ^ i.val) ∧
    (∀ T : Finset (Fin k),
      T.Nonempty → T ≠ (Finset.univ : Finset (Fin k)) →
      simplexCentering k
          (Finset.sum T (fun i => simplexColumn k i)) ≠ 0) ∧
    (∀ (e : Fin k → Fin k), Function.Bijective e →
      ∃ v : Fin (k + 1) → (Fin (k - 1) → ℚ), simpleClosedPotentialPath k e v)

abbrev TwoVector := Fin 2 → ℝ

def logarithmicMotionMatrix (a x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a⁻¹, -x / (2 * a); -x / (2 * a), a]

def quadraticFormTwo (K : Matrix (Fin 2) (Fin 2) ℝ) (v : TwoVector) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, v i * K i j * v j

def logarithmicQuadraticDerivative (a x : ℝ) (v : TwoVector) : ℝ :=
  deriv (fun t : ℝ =>
    Real.log (quadraticFormTwo (logarithmicMotionMatrix (Real.exp t) x) v))
    (Real.log a)

def logarithmicMotionBoundClaim8646 : Prop :=
  ∀ (ρ a x : ℝ),
    0 ≤ ρ → ρ < 1 → 0 < a → |x| ≤ 2 * ρ * a →
    ∀ v : TwoVector, v ≠ 0 →
      |logarithmicQuadraticDerivative a x v| ≤
        (1 + ρ ^ 2) / (1 - ρ ^ 2)

end

end MathlibPlus.Open.FormalizationBatchPaths
