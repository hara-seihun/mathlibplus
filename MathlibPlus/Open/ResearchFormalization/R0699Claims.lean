import Mathlib
import MathlibPlus.Open.ResearchFormalization.Batch019ffede1003704cbb69a8fa6946cea1.TraceShapes

namespace MathlibPlus.Open.ResearchFormalization.Batch019ffede1003704cbb69a8fa6946cea1

/-- The cylinder of an upset on a larger retained coordinate set. -/
def traceCylinderOn {q : ℕ} (x : TraceShape q) (U : Finset (Fin q)) :
    Finset (Finset (Fin q)) :=
  (Finset.univ : Finset (Finset (Fin q))).filter
    (fun R => R ⊆ U ∧ R ∩ x.1.support ∈ x.1.traces)

/-- A cover obtained by adding one coordinate and replacing the upset by its
cylinder. -/
def freeCoordinateStepAt {q : ℕ}
    (x y : TraceShape q) (i : Fin q) : Prop :=
  i ∉ x.1.support ∧
    y.1.support = insert i x.1.support ∧
      y.1.traces = traceCylinderOn x (insert i x.1.support)

/-- The free-coordinate cover predicate. -/
def freeCoordinateStep {q : ℕ} (x y : TraceShape q) : Prop :=
  ∃ i : Fin q, freeCoordinateStepAt x y i

/-- A cover obtained by deleting one inclusion-minimal current trace, with a
nonempty upset left over. -/
def deleteMinimalTraceStepAt {q : ℕ}
    (x y : TraceShape q) (S : Finset (Fin q)) : Prop :=
  y.1.support = x.1.support ∧
    S ∈ x.1.traces ∧
    (∀ R : Finset (Fin q), R ∈ x.1.traces → R ⊆ S → R = S) ∧
    y.1.traces = x.1.traces.erase S ∧
    y.1.traces.Nonempty

/-- The trace-deletion cover predicate. -/
def deleteMinimalTraceStep {q : ℕ} (x y : TraceShape q) : Prop :=
  ∃ S : Finset (Fin q), deleteMinimalTraceStepAt x y S

/-- Strict order and cover relations for retained trace shapes. -/
def traceShapeLT {q : ℕ} (x y : TraceShape q) : Prop :=
  traceLE x y ∧ ¬ traceLE y x

def traceShapeCover {q : ℕ} (x y : TraceShape q) : Prop :=
  traceShapeLT x y ∧
    ¬ ∃ z : TraceShape q, traceShapeLT x z ∧ traceShapeLT z y

/-- Claim 24037: all covers are exactly the free-coordinate or legal
minimal-trace-deletion covers. -/
def claim_24037 : Prop :=
  ∀ (q : ℕ) (x y : TraceShape q),
    traceShapeCover x y ↔
      ((freeCoordinateStep x y ∨ deleteMinimalTraceStep x y) ∧
        ¬ (freeCoordinateStep x y ∧ deleteMinimalTraceStep x y))

/-- Labels for the two kinds of covers. -/
abbrev TraceLabel (q : ℕ) := Fin q ⊕ Finset (Fin q)

/-- The label relation induced by the two legal cover operations. -/
def traceStepLabel {q : ℕ}
    (x y : TraceShape q) (label : TraceLabel q) : Prop :=
  match label with
  | Sum.inl i => freeCoordinateStepAt x y i
  | Sum.inr S => deleteMinimalTraceStepAt x y S

structure TraceStep (q : ℕ) where
  source : TraceShape q
  label : TraceLabel q
  target : TraceShape q

/-- The label order: every free-coordinate label precedes every deletion
label, while each part uses its fixed order. -/
def traceLabelLT {q : ℕ}
    (coordinateOrder : LinearOrder (Fin q))
    (traceOrder : LinearOrder (Finset (Fin q))) :
    TraceLabel q → TraceLabel q → Prop
  | Sum.inl i, Sum.inl j => coordinateOrder.lt i j
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr S, Sum.inr R => traceOrder.lt S R

/-- A list is an ordered enumeration of a finite set. -/
def orderedEnumeration {α : Type*} [DecidableEq α]
    (r : α → α → Prop) (s : Finset α) (l : List α) : Prop :=
  l.Nodup ∧
    (∀ a : α, a ∈ l ↔ a ∈ s) ∧
    List.Pairwise r l

/-- A labeled saturated chain, represented by its successive labeled cover
steps. -/
def traceChainFrom {q : ℕ}
    (x y : TraceShape q) : List (TraceStep q) → Prop
  | [] => x = y
  | step :: rest =>
      step.source = x ∧
        traceShapeCover step.source step.target ∧
        traceStepLabel step.source step.target step.label ∧
        traceChainFrom step.target y rest

def traceChainLabels {q : ℕ} :
    List (TraceStep q) → List (TraceLabel q) :=
  List.map (fun step => step.label)

/-- The exact rising-label and prescribed-order condition for a chain. -/
def risingPrescribedTraceChain {q : ℕ}
    (coordinateOrder : LinearOrder (Fin q))
    (traceOrder : LinearOrder (Finset (Fin q)))
    (x y : TraceShape q) (chain : List (TraceStep q)) : Prop :=
  ∃ coordinates : List (Fin q), ∃ deletions : List (Finset (Fin q)),
    orderedEnumeration coordinateOrder.lt
      (y.1.support \ x.1.support) coordinates ∧
    orderedEnumeration traceOrder.lt
      (traceCylinderOn x y.1.support \ y.1.traces) deletions ∧
    traceChainLabels chain =
      coordinates.map (fun i => Sum.inl i) ++
        deletions.map (fun S => Sum.inr S) ∧
    List.Pairwise
      (traceLabelLT coordinateOrder traceOrder)
      (traceChainLabels chain)

/-- Claim 24038: for every fixed coordinate order and inclusion-extending
trace order, every interval has the unique rising lexicographically first
saturated chain, with the displayed free-then-deletion label sequence. -/
def claim_24038 : Prop :=
  ∀ (q : ℕ)
    (coordinateOrder : LinearOrder (Fin q))
    (traceOrder : LinearOrder (Finset (Fin q))),
    (∀ S R : Finset (Fin q), S ⊆ R → S ≠ R → traceOrder.lt S R) →
      ∀ (x y : TraceShape q), traceLE x y →
        ∃! chain : List (TraceStep q),
          traceChainFrom x y chain ∧
            risingPrescribedTraceChain coordinateOrder traceOrder x y chain ∧
            (∀ other : List (TraceStep q),
              traceChainFrom x y other →
                ¬ List.Lex (traceLabelLT coordinateOrder traceOrder)
                    (traceChainLabels other) (traceChainLabels chain))

end MathlibPlus.Open.ResearchFormalization.Batch019ffede1003704cbb69a8fa6946cea1
