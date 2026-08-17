import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0800DefectFour

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0800ContextualVisibility

noncomputable section
open Classical

abbrev Coeff := MvPolynomial ℕ ℤ
abbrev MarkerPolynomial := Polynomial Coeff

abbrev UnrootedTree (m : ℕ) := {G : SimpleGraph (Fin m) // G.IsTree}

/-- A finite selected edge set in the exact labelled tree carrier. -/
def treeEdges {m : ℕ} (T : UnrootedTree m) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ T.1.Adj e.1 e.2)

def selectedAdj {m : ℕ} (S : Finset (Fin m × Fin m))
    (u v : Fin m) : Prop :=
  (u < v ∧ (u, v) ∈ S) ∨ (v < u ∧ (v, u) ∈ S)

def selectedReachable {m : ℕ} (S : Finset (Fin m × Fin m))
    (u v : Fin m) : Prop :=
  Relation.ReflTransGen (selectedAdj S) u v

def selectedComponent {m : ℕ} (S : Finset (Fin m × Fin m))
    (v : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (selectedReachable S v)

def selectedComponentSize {m : ℕ} (S : Finset (Fin m × Fin m))
    (v : Fin m) : ℕ :=
  (selectedComponent S v).card

def selectedComponentMinima {m : ℕ} (S : Finset (Fin m × Fin m)) :
    Finset (Fin m) :=
  Finset.univ.filter (fun v =>
    ∀ u, selectedReachable S u v → v ≤ u)

def componentProduct {m : ℕ} (S : Finset (Fin m × Fin m)) : Coeff :=
  (selectedComponentMinima S).prod
    (fun v => MvPolynomial.X (selectedComponentSize S v))

def componentProductExcept {m : ℕ} (S : Finset (Fin m × Fin m))
    (r : Fin m) : Coeff :=
  (selectedComponentMinima S).filter (fun v => ¬ selectedReachable S r v) |>.prod
    (fun v => MvPolynomial.X (selectedComponentSize S v))

def openState {m : ℕ} (S : Finset (Fin m × Fin m))
    (r : Fin m) : MarkerPolynomial :=
  if 1 < selectedComponentSize S r then
    Polynomial.X ^ selectedComponentSize S r *
      Polynomial.C (componentProductExcept S r)
  else 0

def closedForestPolynomial {m : ℕ} (T : UnrootedTree m) : MarkerPolynomial :=
  (treeEdges T).powerset.sum
    (fun S => Polynomial.C (componentProduct S))

def rootedForestPolynomial {m : ℕ} (T : UnrootedTree m)
    (r : Fin m) : MarkerPolynomial :=
  (treeEdges T).powerset.sum
    (fun S => Polynomial.C (componentProduct S) + openState S r)

def rerootDifference {m : ℕ} (T : UnrootedTree m)
    (r s : Fin m) : MarkerPolynomial :=
  rootedForestPolynomial T r - rootedForestPolynomial T s

def defectWeight (d : ℕ) (e : ℕ →₀ ℕ) : ℕ :=
  d + e.support.sum (fun i => (i - 1) * e i)

def defectLayer (p : MarkerPolynomial) (j : ℕ) : MarkerPolynomial :=
  p.support.sum (fun d =>
    (p.coeff d).support.filter (fun e => defectWeight d e = j) |>.sum
      (fun e => Polynomial.monomial d
        (MvPolynomial.monomial e ((p.coeff d).coeff e))))

/-- A rooted tree occurring as one genuine factor of a rooted forest. -/
abbrev RootedTreeFactor := Σ n : ℕ, UnrootedTree n × Fin n
abbrev RootedForestContext := Multiset RootedTreeFactor

def rootedTreeFactorPolynomial (R : RootedTreeFactor) : MarkerPolynomial :=
  rootedForestPolynomial R.2.1 R.2.2

def contextProduct (C : RootedForestContext) : MarkerPolynomial :=
  (C.map rootedTreeFactorPolynomial).prod

def contextWeight (C : RootedForestContext) : ℕ :=
  (C.map (fun R => R.1)).sum

def genuineContext (a : ℕ) (C : RootedForestContext) : Prop :=
  contextWeight C = a

def firstDefectFour {m : ℕ} (T : UnrootedTree m)
    (r s : Fin m) : Prop :=
  (∀ d, d < 4 → defectLayer (rerootDifference T r s) d = 0) ∧
    defectLayer (rerootDifference T r s) 4 ≠ 0

/-- Claim 24851: a first nonzero defect-four reroot layer remains visible
under every genuine rooted-forest context and the reviewed derivative map. -/
def contextualVisibilityFirstDefectFour_claim24851 : Prop :=
  ∀ (m : ℕ) (T : UnrootedTree m) (r s : Fin m),
    firstDefectFour T r s →
      ∀ (a : ℕ) (C : RootedForestContext),
        genuineContext a C →
          MathlibPlus.Open.ResearchFormalization.R0800.defectFourOperator
            (defectLayer
              (contextProduct C * rerootDifference T r s) 4) ≠ 0

end

end MathlibPlus.Open.ResearchFormalization.R0800ContextualVisibility
