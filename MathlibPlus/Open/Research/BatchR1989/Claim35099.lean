import Mathlib

namespace MathlibPlus.Open.Research.BatchR1989

noncomputable section
open scoped BigOperators
open Set
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

abbrev F2_35099 := ZMod 2

def quotientMap_35099 {W : Type*} [AddCommGroup W]
    [Module F2_35099 W] (K : Submodule F2_35099 W) :
    W → (W ⧸ K) :=
  fun x => Submodule.Quotient.mk (p := K) x

/-- Complete autocorrelation events used by the weighted quotient argument. -/
def completeAutocorrelation_35099 {W : Type*} [Add W]
    (S : Set W) (v : W) : Set W :=
  S ∩ {x | ∃ y, y ∈ S ∧ y + v = x}

/-- The quotient support of one complete autocorrelation event. -/
def quotientSupport_35099 {W : Type*} [AddCommGroup W]
    [Module F2_35099 W] (K : Submodule F2_35099 W)
    (E : Set W) : Set (W ⧸ K) :=
  {q | ∃ x, x ∈ E ∧ quotientMap_35099 K x = q}

/-- The homogeneous relation in the weighted lemma. -/
def homogeneousRelation_35099 {W : Type*} [AddCommGroup W]
    [Module F2_35099 W] (K : Submodule F2_35099 W) : Set (W × W) :=
  {p | p.1 + p.2 ∈ K}

/-- Claim 35099: the exact `a+b ∈ K` quotient relation, ordered
cross-avoidance, pairwise-disjoint overlap supports, matching inequalities,
and the summed density bound are all retained. -/
def claim_35099 {W : Type*}
    [Fintype W] [AddCommGroup W] [Module F2_35099 W]
    [FiniteDimensional F2_35099 W]
    (m : ℕ) (K : Submodule F2_35099 W)
    (S : Fin m → Set W) (a b : W) : Prop :=
  a + b ∈ K →
    let π := quotientMap_35099 K
    let δ := π a
    let L := homogeneousRelation_35099 K
    let A : Fin m → Set (W ⧸ K) :=
      fun i => quotientSupport_35099 K
        (completeAutocorrelation_35099 (S i) a)
    let B : Fin m → Set (W ⧸ K) :=
      fun i => quotientSupport_35099 K
        (completeAutocorrelation_35099 (S i) b)
    let O : Fin m → Set (W ⧸ K) := fun i => A i ∩ B i
    π b = δ ∧
      L = {p | π p.1 = π p.2} ∧
      ((∀ i j : Fin m, i < j → A i ∩ B j = ∅) →
        Pairwise (fun i j => Disjoint (O i) (O j)) ∧
          (∀ i : Fin m,
            (Set.ncard (S i) : ℝ) / (Fintype.card W : ℝ) - (1 : ℝ) / 2 ≤
              (Set.ncard (O i) : ℝ) /
                (2 * (Fintype.card (W ⧸ K) : ℝ))) ∧
          (∑ i : Fin m,
              (Set.ncard (S i) : ℝ) / (Fintype.card W : ℝ)) ≤
            (m : ℝ) / 2 + (1 : ℝ) / 2)

end
end MathlibPlus.Open.Research.BatchR1989
