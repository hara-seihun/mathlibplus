import MathlibPlus.Open.Research.R2209
import MathlibPlus.Open.ResearchFormalization.R2209SharpBoundaryClaim43425

namespace MathlibPlus.Open.ResearchFormalization.R2209Claim43423

open scoped BigOperators
open MathlibPlus.Open.Research.R2209
open MathlibPlus.Open.ResearchFormalization.R2209SharpBoundaryRepair

noncomputable section

abbrev F3 := MathlibPlus.Open.Research.R2209.F3
abbrev FiberPoint :=
  MathlibPlus.Open.ResearchFormalization.R2209SharpBoundaryRepair.FiberPoint
abbrev QuotientPoint :=
  MathlibPlus.Open.ResearchFormalization.R2209SharpBoundaryRepair.QuotientPoint
abbrev ChartPoint :=
  MathlibPlus.Open.ResearchFormalization.R2209SharpBoundaryRepair.ChartPoint
abbrev DualPoint :=
  MathlibPlus.Open.ResearchFormalization.R2209SharpBoundaryRepair.DualPoint
abbrev LowerTopCoefficients := Fin 5 → F3
abbrev ChartFunction := QuotientPoint → FiberPoint

/-- The five-dimensional lower-top part in the normalized quartic-leading
chart. -/
def lowerTop (c : LowerTopCoefficients) (y : QuotientPoint) : F3 :=
  MathlibPlus.Open.Research.R2209.lowerPolynomial c y

/-- Every normalized quartic-leading top function in the fixed chart. -/
def quarticLeadingTop (c : LowerTopCoefficients)
    (y : QuotientPoint) : F3 :=
  y.1 ^ 2 * y.2 ^ 2 + lowerTop c y

/-- The exact `(t,q)` chart function; the lower quotient shear is absent from
its relative derivative by the retained shear identity. -/
def chartFunction (c : LowerTopCoefficients)
    (q : QuotientPoint → F3) : ChartFunction :=
  fun y => (quarticLeadingTop c y, q y)

/-- The normalized source relative derivative after the exact shear
cancellation. -/
def chartRelativeDerivative (F : ChartFunction)
    (label z : ChartPoint) : ChartPoint :=
  (z.1 +
      (F (z.2 + label.2) - F z.2 - F label.2), z.2)

/-- Point masses in the exact dual chart. -/
def chartPointMass (x : ChartPoint) : DualPoint :=
  fun y => if y = x then 1 else 0

/-- The exact component-relation transition row. -/
def chartTransitionRow (F : ChartFunction)
    (x label : ChartPoint) : DualPoint :=
  chartPointMass (x + label) - chartPointMass label -
    chartPointMass (chartRelativeDerivative F label x)

def chartTransitionEdge (F : ChartFunction)
    (x y : ChartPoint) : Prop :=
  ∃ label : ChartPoint, y = chartRelativeDerivative F label x

def chartDerivativeComponent (F : ChartFunction)
    (root : ChartPoint) : Set ChartPoint :=
  {x | Relation.EqvGen (chartTransitionEdge F) root x}

def chartPathEndpoint (F : ChartFunction) :
    ChartPoint → List ChartPoint → ChartPoint
  | x, [] => x
  | x, label :: labels =>
      chartPathEndpoint F (chartRelativeDerivative F label x) labels

def chartPathRow (F : ChartFunction) :
    ChartPoint → List ChartPoint → DualPoint
  | x, [] => 0
  | x, label :: labels =>
      chartTransitionRow F x label +
        chartPathRow F (chartRelativeDerivative F label x) labels

def chartCycleRows (F : ChartFunction) (root : ChartPoint) : Set DualPoint :=
  {r | ∃ x : ChartPoint, x ∈ chartDerivativeComponent F root ∧
    ∃ path : List ChartPoint,
      chartPathEndpoint F x path = x ∧ r = chartPathRow F x path}

def chartComponentRelation (F : ChartFunction) (root : ChartPoint) :
    Submodule F3 DualPoint :=
  Submodule.span F3 (chartCycleRows F root)

def chartCyclePairing (r f : DualPoint) : F3 :=
  ∑ x : ChartPoint, r x * f x

def chartComponentAnnihilator (F : ChartFunction)
    (root : ChartPoint) (f : DualPoint) : Prop :=
  ∀ r : DualPoint, r ∈ chartComponentRelation F root →
    chartCyclePairing r f = 0

def chartComponentwiseAnnihilatorIncidence (F : ChartFunction)
    (U : Submodule F3 DualPoint) : Prop :=
  ∀ root : ChartPoint,
    ∃ f : DualPoint, f ∈ U ∧ f ≠ 0 ∧
      chartComponentAnnihilator F root f

/-- A decomposable switching plane in the exact component-relation atlas. -/
def chartDecomposablePlane (F : ChartFunction)
    (U : Submodule F3 DualPoint) : Prop :=
  Module.finrank F3 U = 2 ∧
    (∀ f : DualPoint, f ∈ U → f 0 = 0) ∧
      chartComponentwiseAnnihilatorIncidence F U

/-- The projective line represented by a nonzero dual point. -/
def chartProjectiveLine (t : DualPoint) : Submodule F3 DualPoint :=
  Submodule.span F3 {t}

def chartLineVertex (L : Submodule F3 DualPoint) : Prop :=
  ∃ t : DualPoint, t ≠ 0 ∧ L = chartProjectiveLine t

def chartPlaneLineIncidence (F : ChartFunction)
    (U L : Submodule F3 DualPoint) : Prop :=
  chartDecomposablePlane F U ∧ chartLineVertex L ∧ L ≤ U

/-- The shared-line relation on the exact plane/line vertices. -/
def chartSharedTopLine (F : ChartFunction) : Prop :=
  ∃ U V L : Submodule F3 DualPoint,
    chartDecomposablePlane F U ∧ chartDecomposablePlane F V ∧
      chartLineVertex L ∧ U ≠ V ∧ L ≤ U ∧ L ≤ V

/-- Every projective top line has degree at most one on the plane side. -/
def chartIncidenceLineDegreeAtMostOne (F : ChartFunction) : Prop :=
  ∀ L U V : Submodule F3 DualPoint,
    chartLineVertex L → chartDecomposablePlane F U →
      chartDecomposablePlane F V → L ≤ U → L ≤ V → U = V

/-- Exact incidence-graph form: line vertices have degree at most one and
 every decomposable plane is the centre of its four projective lines. -/
def chartIncidenceIsDisjointK14Stars (F : ChartFunction) : Prop :=
  (∀ L : Submodule F3 DualPoint, chartLineVertex L →
    Set.ncard {U : Submodule F3 DualPoint |
      chartDecomposablePlane F U ∧ L ≤ U} ≤ 1) ∧
    (∀ U : Submodule F3 DualPoint, chartDecomposablePlane F U →
      Set.ncard {L : Submodule F3 DualPoint |
        chartLineVertex L ∧ L ≤ U} = 4)

/-- Claim 43423: the global shared-line gate is empty throughout the
normalized quartic-leading chart, and its exact plane/line incidence is a
union of `K_(1,4)` stars; decomposable planes with no shared line remain
allowed. -/
def claim43423 : Prop :=
  ∀ (c : LowerTopCoefficients) (q : QuotientPoint → F3),
    q 0 = 0 →
      let F := chartFunction c q
      ¬ chartSharedTopLine F ∧
        chartIncidenceLineDegreeAtMostOne F ∧
          chartIncidenceIsDisjointK14Stars F

end

end MathlibPlus.Open.ResearchFormalization.R2209Claim43423
