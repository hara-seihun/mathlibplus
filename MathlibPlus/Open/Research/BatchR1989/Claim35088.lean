import Mathlib

namespace MathlibPlus.Open.Research.BatchR1989

noncomputable section
open scoped BigOperators
open Set
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

abbrev F2_35088 := ZMod 2

def quotientMap_35088 {W : Type*} [AddCommGroup W]
    [Module F2_35088 W] (K : Submodule F2_35088 W) :
    W → (W ⧸ K) :=
  fun x => Submodule.Quotient.mk (p := K) x

/-- Complete autocorrelation in the selected quotient subset. -/
def completeAutocorrelation_35088 {W : Type*} [Add W]
    (S : Set W) (v : W) : Set W :=
  S ∩ {x | ∃ y, y ∈ S ∧ y + v = x}

/-- Quotient cosets meeting an autocorrelation event. -/
def quotientSupport_35088 {W : Type*} [AddCommGroup W]
    [Module F2_35088 W] (K : Submodule F2_35088 W)
    (E : Set W) : Set (W ⧸ K) :=
  {q | ∃ x, x ∈ E ∧ quotientMap_35088 K x = q}

/-- The homogeneous binary relation determined by a subspace. -/
def homogeneousRelation_35088 {W : Type*} [AddCommGroup W]
    [Module F2_35088 W] (K : Submodule F2_35088 W) : Set (W × W) :=
  {p | p.1 + p.2 ∈ K}

/-- Claim 35088: after the homogeneous relation supplies the exact
`a+b ∈ K` condition, a selected set of density strictly above one half has
one quotient coset meeting both complete autocorrelation events. -/
def claim_35088 {W : Type*}
    [Fintype W] [AddCommGroup W] [Module F2_35088 W]
    [FiniteDimensional F2_35088 W]
    (K : Submodule F2_35088 W) (S : Set W) (a b : W) : Prop :=
  a + b ∈ K →
    (Set.ncard S : ℝ) > (Fintype.card W : ℝ) / 2 →
    let A := quotientSupport_35088 K
      (completeAutocorrelation_35088 S a)
    let B := quotientSupport_35088 K
      (completeAutocorrelation_35088 S b)
    A ∩ B ≠ ∅

end
end MathlibPlus.Open.Research.BatchR1989
