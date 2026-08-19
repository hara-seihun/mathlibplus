import Mathlib
import MathlibPlus.Open.CayleyCIE7
import MathlibPlus.Open.ResearchFormalization.R1441Claim37224
import MathlibPlus.Open.ResearchFormalization.R1444LocalDerivativeTupleClaim37260

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR1432R1441R1444

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1441Claim37224
open MathlibPlus.Open.ResearchFormalization.R1444

attribute [local instance] Classical.decEq Classical.propDecidable

private abbrev Multiplier35 := (ZMod 35)ˣ

private def standardMultiplierSubgroup37184 : Subgroup Multiplier35 :=
  Subgroup.closure {u : Multiplier35 |
    (u : ZMod 35) = 11 ∨ (u : ZMod 35) = 16}

private def standardMultiplierValues37184 : Set (ZMod 35) :=
  {x | ∃ u : standardMultiplierSubgroup37184,
    (u.1 : ZMod 35) = x}

/-- Claim 37184, standard-multiplier receipt.  The units model and its
explicit order-three subgroup are retained; the separate identification of
this model with the full automorphism group is left visible in the receipt. -/
def claim37184_uniqueMultiplierSubgroup : Prop :=
  Nat.card Multiplier35 = 24 ∧
    Nat.card standardMultiplierSubgroup37184 = 3 ∧
      (∀ H : Subgroup Multiplier35,
        Nat.card H = 3 → H = standardMultiplierSubgroup37184) ∧
        standardMultiplierValues37184 = ({1, 11, 16} : Set (ZMod 35))

/-- Claim 37222: the exact E(C₇,3) matching-scalar derivative subspace and
pure-translation profile are specified on the located source carriers. -/
def claim37222_derivativeSubspacePureTranslation : Prop :=
  ∀ τ : H → W, normalizedProfile τ →
    (∃ D : H → Submodule (ZMod 7) W,
      (∀ h : H,
        D h =
          Submodule.span (ZMod 7)
            (Set.range (fun k : H =>
              τ (MathlibPlus.Open.CayleyCIE7.eC73Mul h k) -
                τ h - hAction h (τ k)))) ∧
      ∃ f : W × H → W × H,
        ∀ w : W, ∀ h : H, f (w, h) = (w + τ h, h))

private def nonaffineChartSet37266 : Set quinaryPermutation :=
  {σ | ¬ affineChart5 σ}

private def simultaneousTupleClass37266
    (σ : quinaryPermutation) : Set quinaryPermutation :=
  {τ | τ ∈ nonaffineChartSet37266 ∧
    simultaneouslyConjugateDerivativeTuples σ τ}

private def simultaneousTupleClassFamily37266 : Set (Set quinaryPermutation) :=
  {C | ∃ σ : quinaryPermutation,
    σ ∈ nonaffineChartSet37266 ∧ C = simultaneousTupleClass37266 σ}

private def orderedDistinctChartPairs37266 : Set (quinaryPermutation × quinaryPermutation) :=
  {p | p.1 ∈ nonaffineChartSet37266 ∧
    p.2 ∈ nonaffineChartSet37266 ∧ p.1 ≠ p.2}

private def automorphismGraphPairs37266 : Set (quinaryPermutation × quinaryPermutation) :=
  {p | p ∈ orderedDistinctChartPairs37266 ∧
    simultaneouslyConjugateDerivativeTuples p.1 p.2}

private def fullProductPairs37266 : Set (quinaryPermutation × quinaryPermutation) :=
  orderedDistinctChartPairs37266 \ automorphismGraphPairs37266

/-- Claim 37266: the exact nonaffine chart, simultaneous-tuple-class, pair,
and generated-subgroup census on the located quinary permutation carrier. -/
def claim37266_derivativeTupleCensus : Prop :=
  Set.ncard nonaffineChartSet37266 = 100 ∧
    Set.ncard simultaneousTupleClassFamily37266 = 4 ∧
      (∀ C : Set quinaryPermutation,
        C ∈ simultaneousTupleClassFamily37266 → Set.ncard C = 25) ∧
        Set.ncard orderedDistinctChartPairs37266 = 9900 ∧
          Set.ncard automorphismGraphPairs37266 = 2400 ∧
            Set.ncard fullProductPairs37266 = 7500 ∧
              (∀ p, p ∈ automorphismGraphPairs37266 →
                Nat.card (synchronousClosure5 p.1 p.2) = 60) ∧
                (∀ p, p ∈ fullProductPairs37266 →
                  Nat.card (synchronousClosure5 p.1 p.2) = 3600) ∧
                  2400 = 4 * 25 * 24 ∧
                    7500 = 9900 - 2400 ∧
                      3600 = 60 * 60

end
end MathlibPlus.Open.ResearchFormalization.BatchR1432R1441R1444
