import Mathlib
import MathlibPlus.Open.Combinatorics.DTreeUPolynomial

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR0772

open MathlibPlus.Open.Combinatorics.DTreeUPolynomial

/-- The cavity graph obtained by deleting a distinguished root. -/
def cavityGraph {V : Type*} (T : SimpleGraph V) (r : V) :
    SimpleGraph {u : V // u ≠ r} :=
  T.induce {u : V | u ≠ r}

/-- Evaluate the standard component-partition U-polynomial with every
component variable set to the same real value. -/
noncomputable def equalVariableUValue
    {V : Type*} [Fintype V] [LinearOrder V]
    (F : SimpleGraph V) (q : ℝ) : ℝ :=
  MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun _ => q) (uPolynomial F)

/-- Claim 24597: deleting the root of a finite rooted tree records the root
component degree and gives the stated equal-variable U-value. -/
def claim24597_equalVariableCavityValue : Prop :=
  ∀ {V : Type*} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (r : V) (m : ℕ) (q : ℝ),
    T.IsTree →
    Fintype.card V = m →
    letI : Fintype (T.neighborSet r) := Fintype.ofFinite _
    let C := cavityGraph T r
    letI : Fintype (C.ConnectedComponent) := Fintype.ofFinite _
    Fintype.card {u : V // u ≠ r} = m - 1 ∧
      Fintype.card (C.ConnectedComponent) = T.degree r ∧
      equalVariableUValue C q =
        q ^ T.degree r * (1 + q) ^ (m - 1 - T.degree r)

end MathlibPlus.Open.ResearchFormalization.BatchR0772
