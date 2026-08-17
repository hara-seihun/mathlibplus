import MathlibPlus.Open.Research.R2209

namespace MathlibPlus.Open.ResearchFormalization.R2209SharpBoundaryRepair

open scoped BigOperators

noncomputable section

abbrev F3 := MathlibPlus.Open.Research.R2209.F3
abbrev FiberPoint := F3 × F3
abbrev QuotientPoint := F3 × F3
abbrev ChartPoint := FiberPoint × QuotientPoint
abbrev DualPoint := ChartPoint → F3

/-- The carry and quartic-leading top in the sharp boundary family. -/
def sharpCarry (y : QuotientPoint) : F3 := y.1 * y.2

def sharpTop (lambda : F3) (y : QuotientPoint) : F3 :=
  y.1 ^ 2 * y.2 ^ 2 + lambda * y.1 * y.2

def sharpFunction (lambda : F3) (y : QuotientPoint) : FiberPoint :=
  (sharpTop lambda y, sharpCarry y)

def sharpMap (lambda : F3) (z : ChartPoint) : ChartPoint :=
  (z.1 + sharpFunction lambda z.2, z.2)

def pureEndpoint (z : ChartPoint) : ChartPoint := sharpMap 0 z

/-- The displayed coordinate change
`L_lambda(x,u,v,w)=(x+lambda*u,u,v,w)`. -/
def fibreCoordinateChange (lambda : F3) (z : ChartPoint) : ChartPoint :=
  ((z.1.1 + lambda * z.1.2, z.1.2), z.2)

def sharpMapInverse (lambda : F3) (z : ChartPoint) : ChartPoint :=
  (z.1 - sharpFunction lambda z.2, z.2)

/-- The normalized source derivative of the sharp chart. -/
def relativeDerivative (lambda : F3) (label z : ChartPoint) : ChartPoint :=
  sharpMapInverse lambda
    (sharpMap lambda (z + label) - sharpMap lambda label)

/-- Exact relation rows for the derivative components. -/
def pointMass (x : ChartPoint) : DualPoint :=
  fun y => if y = x then 1 else 0

def transitionRow (lambda : F3) (x label : ChartPoint) : DualPoint :=
  pointMass (x + label) - pointMass label -
    pointMass (relativeDerivative lambda label x)

def transitionEdge (lambda : F3) (x y : ChartPoint) : Prop :=
  ∃ label : ChartPoint, y = relativeDerivative lambda label x

def derivativeComponent (lambda : F3) (root : ChartPoint) : Set ChartPoint :=
  {x | Relation.EqvGen (transitionEdge lambda) root x}

def pathEndpoint (lambda : F3) : ChartPoint → List ChartPoint → ChartPoint
  | x, [] => x
  | x, label :: labels =>
      pathEndpoint lambda (relativeDerivative lambda label x) labels

def pathRow (lambda : F3) : ChartPoint → List ChartPoint → DualPoint
  | x, [] => 0
  | x, label :: labels =>
      transitionRow lambda x label +
        pathRow lambda (relativeDerivative lambda label x) labels

def cycleRows (lambda : F3) (root : ChartPoint) : Set DualPoint :=
  {r | ∃ x : ChartPoint, x ∈ derivativeComponent lambda root ∧
    ∃ path : List ChartPoint,
      pathEndpoint lambda x path = x ∧ r = pathRow lambda x path}

def componentRelation (lambda : F3) (root : ChartPoint) :
    Submodule F3 DualPoint :=
  Submodule.span F3 (cycleRows lambda root)

def cyclePairing (r f : DualPoint) : F3 :=
  ∑ x : ChartPoint, r x * f x

def componentAnnihilator (lambda : F3) (root : ChartPoint)
    (f : DualPoint) : Prop :=
  ∀ r : DualPoint, r ∈ componentRelation lambda root →
    cyclePairing r f = 0

/-- A projective line in the normalized dual space. -/
def projectiveLine (t : DualPoint) : Submodule F3 DualPoint :=
  Submodule.span F3 {t}

/-- The componentwise nontrivial-annihilator incidence used by the exact
component-relation atlas. -/
def componentwiseAnnihilatorIncidence (lambda : F3)
    (U : Submodule F3 DualPoint) : Prop :=
  ∀ root : ChartPoint,
    ∃ f : DualPoint, f ∈ U ∧ f ≠ 0 ∧
      componentAnnihilator lambda root f

/-- A decomposable switching plane is normalized, two-dimensional, and meets
 each component annihilator nontrivially. -/
def decomposablePlane (lambda : F3) (U : Submodule F3 DualPoint) : Prop :=
  Module.finrank F3 U = 2 ∧
    (∀ f : DualPoint, f ∈ U → f 0 = 0) ∧
    componentwiseAnnihilatorIncidence lambda U

/-- An isolated decomposable plane has no distinct decomposable plane on
any of its projective lines. -/
def isolatedDecomposablePlane (lambda : F3)
    (U : Submodule F3 DualPoint) : Prop :=
  decomposablePlane lambda U ∧
    ∀ t : DualPoint, t ≠ 0 → projectiveLine t ≤ U →
      ∀ V : Submodule F3 DualPoint,
        decomposablePlane lambda V → projectiveLine t ≤ V → V = U

/-- The geometric common-line relation for two distinct decomposable planes. -/
def sharedTopLineWitness (lambda : F3)
    (U V : Submodule F3 DualPoint) (t : DualPoint) : Prop :=
  decomposablePlane lambda U ∧ decomposablePlane lambda V ∧ U ≠ V ∧
    t ≠ 0 ∧ projectiveLine t ≤ U ∧ projectiveLine t ≤ V

def sharedTopLine (lambda : F3) : Prop :=
  ∃ U V t, sharedTopLineWitness lambda U V t

/-- The edge voltage of a scalar function for the exact source derivative. -/
def edgeVoltage (lambda : F3) (f : DualPoint)
    (label z : ChartPoint) : F3 :=
  f (z + label) - f label - f (relativeDerivative lambda label z)

/-- The genuine fixed-top condition: a top voltage which vanishes on a
component's cycle relations forces the whole switching plane to vanish there. -/
def genuineFixedTop (lambda : F3) (U : Submodule F3 DualPoint)
    (t : DualPoint) : Prop :=
  ∀ root : ChartPoint,
    componentAnnihilator lambda root t →
      ∀ f : DualPoint, f ∈ U → componentAnnihilator lambda root f

/-- A rank-five fixed-top multi-section source has two distinct decomposable
planes over one common top line, with the genuine fixed-top condition on both
planes. -/
def fixedTopSource (lambda : F3)
    (U V : Submodule F3 DualPoint) (t : DualPoint) : Prop :=
  decomposablePlane lambda U ∧ decomposablePlane lambda V ∧ U ≠ V ∧
    t ≠ 0 ∧ projectiveLine t ≤ U ∧ projectiveLine t ≤ V ∧
    genuineFixedTop lambda U t ∧ genuineFixedTop lambda V t

/-- The componentwise gradient form of a genuine section. -/
def gradientCorrectedSection (lambda : F3)
    (U : Submodule F3 DualPoint) (t s : DualPoint) : Prop :=
  s ∈ U ∧
    ∃ mu : F3, ∃ P : DualPoint,
      ∀ root : ChartPoint, ∀ x : ChartPoint,
        x ∈ derivativeComponent lambda root →
          ∀ label : ChartPoint,
            edgeVoltage lambda s label x - mu * edgeVoltage lambda t label x =
              P (relativeDerivative lambda label x) - P x

/-- A Babai-stage witness retains the genuine source pair and the
componentwise gradient data for both independent sections. -/
def babaiWitness (lambda : F3)
    (U V : Submodule F3 DualPoint) : Prop :=
  ∃ t sU sV : DualPoint,
    fixedTopSource lambda U V t ∧
    U = Submodule.span F3 ({t, sU} : Set DualPoint) ∧
    V = Submodule.span F3 ({t, sV} : Set DualPoint) ∧
    sU ∉ projectiveLine t ∧ sV ∉ projectiveLine t ∧
    gradientCorrectedSection lambda U t sU ∧
    gradientCorrectedSection lambda V t sV

/-- Claim 43425: the sharp nonzero-lambda family is conjugate to the pure
endpoint, has an isolated decomposable plane, and supplies neither a genuine
fixed-top source nor a Babai-stage witness. -/
def claim43425 : Prop :=
  ∀ lambda : F3, (lambda = 1 ∨ lambda = 2) →
    (Function.Bijective (fibreCoordinateChange lambda)) ∧
    (∀ z : ChartPoint,
      fibreCoordinateChange lambda (pureEndpoint z) =
        sharpMap lambda (fibreCoordinateChange lambda z)) ∧
    (∃ U : Submodule F3 DualPoint,
      isolatedDecomposablePlane lambda U) ∧
    ¬ sharedTopLine lambda ∧
    ¬ (∃ U V t, fixedTopSource lambda U V t) ∧
    ¬ (∃ U V, babaiWitness lambda U V)

end
end MathlibPlus.Open.ResearchFormalization.R2209SharpBoundaryRepair
