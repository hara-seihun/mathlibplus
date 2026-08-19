import MathlibPlus.Open.ResearchFormalization.Batch019ffede1003704cbb69a8fa6946cea1.TraceShapes

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0699Claim24046

noncomputable section

open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

open MathlibPlus.Open.ResearchFormalization.Batch019ffede1003704cbb69a8fa6946cea1

/-- The bottom of the retained trace-shape lattice. -/
def traceBottomData (q : ℕ) : TraceShapeData q :=
  { support := ∅, traces := {∅} }

/-- The absorbing top of the retained trace-shape lattice. -/
def traceAbsorbingTopData (q : ℕ) : TraceShapeData q :=
  { support := (Finset.univ : Finset (Fin q)),
    traces := {(Finset.univ : Finset (Fin q))} }

/-- The strict proper-part carrier, with the two endpoint data removed. -/
def traceIsProper {q : ℕ} (x : TraceShape q) : Prop :=
  x.1 ≠ traceBottomData q ∧ x.1 ≠ traceAbsorbingTopData q

/-- A finite-poset contraction of the proper part.  The two order homotopies
are represented by the pointwise inequalities from the identity and from the
constant map at the full-free shape. -/
def traceProperPartContractible (q : ℕ) : Prop :=
  (∃ f : TraceShape q,
      f.1 = fullFreeData q ∧ traceIsProper f) ∧
    ∃ c : TraceShape q → TraceShape q,
      (∀ x : TraceShape q,
        (c x).1 = fullTopClosureData x.1 ∧
          fullTopClosureData (c x).1 = (c x).1) ∧
      (∀ x : TraceShape q, traceIsProper x → traceIsProper (c x)) ∧
      (∀ x y : TraceShape q,
        traceLEData x.1 y.1 → traceLEData (c x).1 (c y).1) ∧
      (∀ x : TraceShape q,
        traceIsProper x → traceLEData x.1 (c x).1) ∧
      (∀ x : TraceShape q,
        traceIsProper x → traceLEData (fullFreeData q) (c x).1)

/-- Sum a function over all valid retained trace-shape data.  The two finite
Finset coordinates are the verified finite carrier of `TraceShape`. -/
def traceShapeSum {q : ℕ} (f : TraceShape q → ℤ) : ℤ :=
  ∑ T : Finset (Fin q),
    ∑ H : Finset (Finset (Fin q)),
      if h : IsNonemptyUpset T H then
        f ⟨{ support := T, traces := H }, h⟩
      else 0

/-- The recursive incidence-algebra specification of the poset Möbius
function on the verified retained trace-shape carrier. -/
def traceMobiusSpec (q : ℕ)
    (μ : TraceShape q → TraceShape q → ℤ) : Prop :=
  ∀ x y : TraceShape q, traceLEData x.1 y.1 →
    ((x.1 = y.1 → μ x y = 1) ∧
      (x.1 ≠ y.1 →
        μ x y =
          -traceShapeSum (fun z =>
            if traceLEData x.1 z.1 ∧ traceLEData z.1 y.1 ∧ z.1 ≠ y.1 then
              μ x z
            else 0)))

/-- Claim 24046: for every positive `q`, the proper part contracts through the
full-top closure, and the endpoint Möbius value is zero. -/
def claim_24046 : Prop :=
  ∀ q : ℕ, 1 ≤ q →
    traceProperPartContractible q ∧
      ∃ b t : TraceShape q,
        b.1 = traceBottomData q ∧
          t.1 = traceAbsorbingTopData q ∧
          traceLEData b.1 t.1 ∧
          ∀ μ : TraceShape q → TraceShape q → ℤ,
            traceMobiusSpec q μ → μ b t = 0

end

end MathlibPlus.Open.ResearchFormalization.R0699Claim24046
