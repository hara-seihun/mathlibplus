import MathlibPlus.Open.Algebra.MarkerSupportClaims31768_31769
import MathlibPlus.Open.ResearchFormalization.R1166.Claim31763

open scoped BigOperators

noncomputable section

open Classical

namespace MathlibPlus.Open.ResearchFormalization.R1166.Claim31754

open MathlibPlus.Open.ResearchFormalization.R0849
open MathlibPlus.Open.Algebra.MarkerSupportClaims
open MathlibPlus.Open.ResearchFormalization.R1166.Claim31763

/-- A monomial witness in the exact connected-deletion and packing sums of a
terminal complement transform. -/
def terminalPackingWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (X : SimpleGraph V) (m r : ℕ) (A : Finset V) (k : ℕ)
    (C : Finset (Finset {v : V // v ∉ (A : Set V)})) : Prop :=
  A ∈
      (Finset.univ : Finset (Finset V)).filter
        (fun A => A.card = m - r ∧ connectedDeletedBlock X A) ∧
    k ∈ Finset.range
      (Fintype.card {v : V // v ∉ (A : Set V)} + 1) ∧
    C ∈ connectedPackings (deletedForest X A) k

/-- The packing covers the whole deleted forest, so no scalar leftover factor
is used and all component markers are explicitly represented. -/
def explicitTerminalPackingWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (X : SimpleGraph V) (m r : ℕ) (A : Finset V) (k : ℕ)
    (C : Finset (Finset {v : V // v ∉ (A : Set V)})) : Prop :=
  terminalPackingWitness X m r A k C ∧
    (∑ B ∈ C, B.card) =
      Fintype.card {v : V // v ∉ (A : Set V)}

/-- Every supported terminal monomial is tied to one of the actual packing
summands, while this predicate records the explicit-marker subcase. -/
def terminalMonomialWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (X : SimpleGraph V) (m r : ℕ) (d : ℕ →₀ ℕ) : Prop :=
  ∃ (A : Finset V) (k : ℕ)
    (C : Finset (Finset {v : V // v ∉ (A : Set V)})),
    terminalPackingWitness X m r A k C ∧
      d ∈ (connectedPackingMonomial C).support

/-- A supported monomial with an actual explicit component-marker
representation.  The `d 0 = 0` clause records the absence of the scalar
leftover marker in the monomial itself. -/
def explicitTerminalMonomial
    {V : Type*} [Fintype V] [DecidableEq V]
    (X : SimpleGraph V) (m r : ℕ) (d : ℕ →₀ ℕ) : Prop :=
  ∃ (A : Finset V) (k : ℕ)
    (C : Finset (Finset {v : V // v ∉ (A : Set V)})),
    explicitTerminalPackingWitness X m r A k C ∧
      d ∈ (connectedPackingMonomial C).support ∧
        d 0 = 0

/-- Claim 31754: the terminal complement transform is the exact connected-
deleted packing sum, every supported monomial has the retained weighted-order
bound and a genuine packing witness, and equality is asserted only for an
explicit component-marker representation. -/
def claim31754 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (X : SimpleGraph V) (m r : ℕ),
    Fintype.card V = m →
      let Θ := terminalComplementTransform X m r
      hasTotalMarkerOrderAtMost r Θ ∧
        (∀ d : ℕ →₀ ℕ,
          d ∈ Θ.support →
            terminalMonomialWitness X m r d ∧
              (explicitTerminalMonomial X m r d →
                markerMonomialOrder d = r))

end MathlibPlus.Open.ResearchFormalization.R1166.Claim31754
