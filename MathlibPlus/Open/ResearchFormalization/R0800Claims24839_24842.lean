import MathlibPlus.Open.ResearchFormalization.R0800ContextualVisibilityClaim24851
import MathlibPlus.Open.ResearchFormalization.R0800DefectFour

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0800Claims24839_24842

noncomputable section
open Classical

open MathlibPlus.Open.ResearchFormalization.R0800ContextualVisibility
open MathlibPlus.Open.ResearchFormalization.R0800

abbrev ComponentCoefficient := MvPolynomial ℕ ℤ
abbrev MarkerPolynomial := Polynomial ComponentCoefficient

/-- The open-root monomial keeps the root component marked even when it is a
singleton. -/
def completeOpenState {m : ℕ} (S : Finset (Fin m × Fin m))
    (r : Fin m) : MarkerPolynomial :=
  Polynomial.X ^ selectedComponentSize S r *
    Polynomial.C (componentProductExcept S r)

/-- The rooted polynomial on the selected-edge carrier with every open-root
state retained. -/
def completeRootedForestPolynomial {m : ℕ} (T : UnrootedTree m)
    (r : Fin m) : MarkerPolynomial :=
  (treeEdges T).powerset.sum
    (fun S => Polynomial.C (componentProduct S) + completeOpenState S r)

def completeRerootDifference {m : ℕ} (T : UnrootedTree m)
    (r s : Fin m) : MarkerPolynomial :=
  completeRootedForestPolynomial T r - completeRootedForestPolynomial T s

def nonSingletonComponentSizes {m : ℕ}
    (S : Finset (Fin m × Fin m)) : Multiset ℕ :=
  ((selectedComponentMinima S).filter
      (fun v => 1 < selectedComponentSize S v)).val.map
    (fun v => selectedComponentSize S v)

def selectedTypeFour {m : ℕ} (S : Finset (Fin m × Fin m)) : Prop :=
  nonSingletonComponentSizes S = (4 ::ₘ 0)

def selectedTypeThreeTwo {m : ℕ} (S : Finset (Fin m × Fin m)) : Prop :=
  nonSingletonComponentSizes S = (3 ::ₘ 2 ::ₘ 0)

def selectedTypeTwoTwoTwo {m : ℕ} (S : Finset (Fin m × Fin m)) : Prop :=
  nonSingletonComponentSizes S = (2 ::ₘ 2 ::ₘ 2 ::ₘ 0)

def openRootDefectFourMonomial {m : ℕ}
    (T : UnrootedTree m) (S : Finset (Fin m × Fin m)) (r : Fin m)
    (d : ℕ) (e : ℕ →₀ ℕ) : Prop :=
  S ∈ (treeEdges T).powerset ∧
    d ∈ (completeOpenState S r).support ∧
    e ∈ ((completeOpenState S r).coeff d).support ∧
    defectWeight d e = 4

/-- Every complete open-root defect-four state has three selected edges, and
its non-singleton selected components have one of the three stated types. -/
def claim24839_selectedThreeEdgeComponentTypes : Prop :=
  ∀ (m : ℕ) (T : UnrootedTree m) (r : Fin m)
    (S : Finset (Fin m × Fin m)) (d : ℕ) (e : ℕ →₀ ℕ),
    openRootDefectFourMonomial T S r d e →
      S.card = 3 ∧
        (selectedTypeFour S ∨ selectedTypeThreeTwo S ∨
          selectedTypeTwoTwoTwo S)

def rootC {m : ℕ} (T : UnrootedTree m) (v : Fin m) : ℕ :=
  ((treeEdges T).powerset.filter (fun S =>
    selectedTypeFour S ∧ selectedComponentSize S v = 4)).card

def rootD {m : ℕ} (T : UnrootedTree m) (v : Fin m) : ℕ :=
  ((treeEdges T).powerset.filter (fun S =>
    selectedTypeThreeTwo S ∧ selectedComponentSize S v = 3)).card

def rootE {m : ℕ} (T : UnrootedTree m) (v : Fin m) : ℕ :=
  ((treeEdges T).powerset.filter (fun S =>
    selectedTypeThreeTwo S ∧ selectedComponentSize S v = 2)).card

def rootF {m : ℕ} (T : UnrootedTree m) (v : Fin m) : ℕ :=
  ((treeEdges T).powerset.filter (fun S =>
    selectedTypeTwoTwoTwo S ∧ selectedComponentSize S v = 2)).card

/-- The complete defect-four decomposition in the common marker-polynomial
carrier. -/
def claim24842_completeDefectFourDecomposition : Prop :=
  ∀ (m : ℕ) (T : UnrootedTree m) (r s : Fin m),
    defectLayer (completeRerootDifference T r s) 2 = 0 →
      defectLayer (completeRerootDifference T r s) 3 = 0 →
        defectLayer (completeRerootDifference T r s) 4 =
          singletonPad (m - 7)
            (((rootC T r : ℤ) - rootC T s) • axisC4 +
              ((rootD T r : ℤ) - rootD T s) • axisD4 +
              ((rootE T r : ℤ) - rootE T s) • axisE4 +
              ((rootF T r : ℤ) - rootF T s) • axisF4)

end

end MathlibPlus.Open.ResearchFormalization.R0800Claims24839_24842
