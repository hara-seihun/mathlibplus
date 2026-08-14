import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch019ffede1003704cbb69a8fa6946cea1

/-- A retained trace-shape datum on the Boolean cube `[q]`. -/
structure TraceShapeData (q : ℕ) where
  support : Finset (Fin q)
  traces : Finset (Finset (Fin q))

/-- Nonempty upsets in the Boolean lattice of subsets of `T`. -/
def IsNonemptyUpset (T : Finset (Fin q)) (H : Finset (Finset (Fin q))) : Prop :=
  H.Nonempty ∧
    (∀ ⦃S : Finset (Fin q)⦄, S ∈ H → S ⊆ T) ∧
    (∀ ⦃S R : Finset (Fin q)⦄, S ∈ H → R ⊆ T → S ⊆ R → R ∈ H)

/-- The actual trace-shape objects, retaining their coordinate support. -/
def TraceShape (q : ℕ) :=
  {d : TraceShapeData q // IsNonemptyUpset d.support d.traces}

abbrev shapeSupport {q : ℕ} (x : TraceShape q) : Finset (Fin q) := x.1.support
abbrev shapeTraces {q : ℕ} (x : TraceShape q) : Finset (Finset (Fin q)) := x.1.traces

/-- Existential projection of a family of Boolean traces to retained coordinates `V`. -/
def traceProjection {q : ℕ} (H : Finset (Finset (Fin q))) (V : Finset (Fin q)) :
    Finset (Finset (Fin q)) :=
  H.image (fun S => S ∩ V)

/-- The projection formula for a trace shape. -/
def projectedTraces {q : ℕ} (x : TraceShape q) (V : Finset (Fin q)) :
    Finset (Finset (Fin q)) :=
  traceProjection x.1.traces V

/-- The Boolean function represented by a retained trace object, evaluated on an ambient trace. -/
def representedTrace {q : ℕ} (d : TraceShapeData q) (A : Finset (Fin q)) : Prop :=
  A ∩ d.support ∈ d.traces

/-- Equality of the represented monotone Boolean functions while retaining supports. -/
def sameRepresentedFunction {q : ℕ} (x y : TraceShape q) : Prop :=
  ∀ A : Finset (Fin q), representedTrace x.1 A ↔ representedTrace y.1 A

/-- The order determined by retained coordinates and existential projection. -/
def traceLE {q : ℕ} (x y : TraceShape q) : Prop :=
  x.1.support ⊆ y.1.support ∧
    traceProjection y.1.traces x.1.support ⊆ x.1.traces

def traceLEData {q : ℕ} (x y : TraceShapeData q) : Prop :=
  x.support ⊆ y.support ∧ traceProjection y.traces x.support ⊆ x.traces

def traceLTData {q : ℕ} (x y : TraceShapeData q) : Prop :=
  traceLEData x y ∧ ¬ traceLEData y x

def isAtomAboveData {q : ℕ} (b x : TraceShapeData q) : Prop :=
  traceLTData b x ∧
    ∀ z : TraceShape q, traceLEData b z.1 → traceLEData z.1 x → z.1 = b ∨ z.1 = x

/-- The raw meet candidate in the exact support/projection form. -/
def traceMeetData {q : ℕ} (x y : TraceShape q) : TraceShapeData q :=
  { support := x.1.support ∩ y.1.support
    traces :=
      traceProjection x.1.traces (x.1.support ∩ y.1.support) ∪
        traceProjection y.1.traces (x.1.support ∩ y.1.support) }

/-- The full-free raw shape. -/
def fullFreeData (q : ℕ) : TraceShapeData q :=
  { support := (Finset.univ : Finset (Fin q))
    traces := (Finset.univ : Finset (Finset (Fin q))).filter
      (fun S => S ⊆ (Finset.univ : Finset (Fin q))) }

/-- The closure that retains all ambient coordinates and existentially extends
an upset from the old support. -/
def fullTopClosureData {q : ℕ} (d : TraceShapeData q) : TraceShapeData q :=
  { support := (Finset.univ : Finset (Fin q))
    traces := (Finset.univ : Finset (Finset (Fin q))).filter
      (fun R => R ∩ d.support ∈ d.traces) }

/-- Cylinder intersection on the union of two retained coordinate sets. -/
def cylinderIntersection {q : ℕ}
    (T U : Finset (Fin q)) (H K : Finset (Finset (Fin q))) :
    Finset (Finset (Fin q)) :=
  (Finset.univ : Finset (Finset (Fin q))).filter fun R =>
    R ⊆ T ∪ U ∧ R ∩ T ∈ H ∧ R ∩ U ∈ K

/-- Claim 24032: trace-shape objects, projection, and retained dummy coordinates. -/
def claim_24032 : Prop :=
  ∀ (q : ℕ) (x : TraceShape q) (V : Finset (Fin q)),
    V ⊆ x.1.support →
      IsNonemptyUpset V (projectedTraces x V) ∧
        (∀ U : Finset (Fin q), x.1.support ⊆ U →
          ∃ y : TraceShape q,
            y.1.support = U ∧ sameRepresentedFunction x y)

/-- Claim 24035: the displayed meet is the greatest lower bound, and its trace
union is the least upset containing both projected traces. -/
def claim_24035 : Prop :=
  ∀ (q : ℕ) (x y : TraceShape q),
    IsNonemptyUpset (traceMeetData x y).support (traceMeetData x y).traces ∧
      traceLEData (traceMeetData x y) (x.1) ∧
      traceLEData (traceMeetData x y) (y.1) ∧
      (∀ z : TraceShape q,
        traceLEData z.1 x.1 → traceLEData z.1 y.1 →
          traceLEData z.1 (traceMeetData x y)) ∧
      (∀ L : Finset (Finset (Fin q)),
        IsNonemptyUpset (traceMeetData x y).support L →
          traceProjection x.1.traces (traceMeetData x y).support ⊆ L →
          traceProjection y.1.traces (traceMeetData x y).support ⊆ L →
          (traceMeetData x y).traces ⊆ L)

/-- Claim 24047: the full-top map is an ascending closure operator whose image
is the fixed-full-top slice with minimum the full-free shape. -/
def claim_24047 : Prop :=
  ∀ (q : ℕ),
    (∀ x : TraceShape q,
      ∃ c : TraceShape q,
        c.1 = fullTopClosureData x.1 ∧
          traceLEData x.1 c.1 ∧
          fullTopClosureData c.1 = c.1) ∧
    (∀ x y : TraceShape q,
      traceLEData x.1 y.1 →
        traceLEData (fullTopClosureData x.1) (fullTopClosureData y.1)) ∧
    (∀ x : TraceShape q,
      fullTopClosureData (fullTopClosureData x.1) = fullTopClosureData x.1) ∧
    (∀ y : TraceShape q,
      (∃ x : TraceShape q, y.1 = fullTopClosureData x.1) ↔
        (fullTopClosureData y.1 = y.1 ∧
          y.1.support = (Finset.univ : Finset (Fin q)))) ∧
    (∀ y : TraceShape q,
      fullTopClosureData y.1 = y.1 → traceLEData (fullFreeData q) y.1)

/-- Claim 24040: existential projection commutes with cylinder intersection for
monotone upsets. -/
def claim_24040 : Prop :=
  ∀ (q : ℕ) (T U V : Finset (Fin q))
    (H K : Finset (Finset (Fin q))),
    V ⊆ T ∩ U →
      IsNonemptyUpset T H → IsNonemptyUpset U K →
        traceProjection (cylinderIntersection T U H K) V =
          traceProjection H V ∩ traceProjection K V

/-- Claim 24045: the atoms over the bottom are the free singleton-coordinate
shapes and their least upper bound is the full free shape. -/
def claim_24045 : Prop :=
  ∀ (q : ℕ),
    (∀ x : TraceShape q,
      isAtomAboveData ({ support := ∅, traces := {∅} }) x.1 ↔
        ∃ i : Fin q,
          x.1 = { support := {i}, traces := ({i} : Finset (Fin q)).powerset }) ∧
      (∃ z : TraceShape q,
        z.1 =
          { support := (Finset.univ : Finset (Fin q))
            traces := (Finset.univ : Finset (Finset (Fin q))).filter
              (fun S => S ⊆ (Finset.univ : Finset (Fin q))) } ∧
          (∀ i : Fin q,
            traceLEData
              { support := {i}, traces := ({i} : Finset (Fin q)).powerset }
              z.1) ∧
          (∀ y : TraceShape q,
            (∀ i : Fin q,
              traceLEData
                { support := {i}, traces := ({i} : Finset (Fin q)).powerset }
                y.1) →
              traceLEData z.1 y.1))

end MathlibPlus.Open.ResearchFormalization.Batch019ffede1003704cbb69a8fa6946cea1
