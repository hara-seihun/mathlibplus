import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.ResearchFormalization.R4377Claim54358

abbrev scalarCellDomain (E : Type*) := E → ℚ

abbrev scalarCellMap (E V : Type*) [AddCommGroup V] [Module ℚ V] :=
  scalarCellDomain E →ₗ[ℚ] V

def cellColumn {E V : Type*} [DecidableEq E] [AddCommGroup V]
    [Module ℚ V] (L : scalarCellMap E V) (e : E) : V :=
  L (Pi.single e 1)

def supportCircuit {E : Type*} [DecidableEq E]
    (S : Finset E) (q : E → ℚ) : Prop :=
  2 ≤ S.card ∧ S.Nonempty ∧
    (∀ e, e ∈ S → 0 < q e) ∧
    (∀ e, e ∉ S → q e = 0)

def totalWeight {E : Type*} (S : Finset E) (q : E → ℚ) : ℚ :=
  ∑ e ∈ S, q e

def normalizedWeight {E : Type*} (S : Finset E) (q : E → ℚ) (e : E) : ℚ :=
  q e / totalWeight S q

def circuitSpan {E V : Type*} [DecidableEq E] [AddCommGroup V]
    [Module ℚ V] (S : Finset E) (L : scalarCellMap E V) : Submodule ℚ V :=
  Submodule.span ℚ (Set.range (fun e : {e // e ∈ S} => cellColumn L e))

def circuitFacts {E V : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (S : Finset E) (L : scalarCellMap E V) (q : E → ℚ) : Prop :=
  supportCircuit S q ∧
    Module.finrank ℚ (circuitSpan S L) = S.card - 1 ∧
    (∑ e : {e // e ∈ S},
      normalizedWeight S q e • cellColumn L e) = 0 ∧
    (∀ T : Finset E, T ⊂ S →
      LinearIndependent ℚ
        (fun e : {e // e ∈ T} => cellColumn L e))

def columnInSpan {E V : Type*} [DecidableEq E] [AddCommGroup V]
    [Module ℚ V] (S : Finset E) (L : scalarCellMap E V)
    (e : {e // e ∈ S}) : circuitSpan S L :=
  ⟨cellColumn L e, Submodule.subset_span ⟨e, rfl⟩⟩

def evaluationMap {E V : Type*} [DecidableEq E] [AddCommGroup V]
    [Module ℚ V] (S : Finset E) (L : scalarCellMap E V) :
    (circuitSpan S L →ₗ[ℚ] ℚ) →ₗ[ℚ]
      ({e // e ∈ S} → ℚ) :=
  { toFun := fun phi e => phi (columnInSpan S L e)
    map_add' := by
      intro phi psi
      funext e
      simp
    map_smul' := by
      intro a phi
      funext e
      simp }

def weightedMeanMap {E : Type*} [DecidableEq E]
    (S : Finset E) (q : E → ℚ) :
    ({e // e ∈ S} → ℚ) →ₗ[ℚ] ℚ :=
  { toFun := fun a => ∑ e : {e // e ∈ S}, normalizedWeight S q e * a e
    map_add' := by
      intro a b
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c a
      simp only [Pi.smul_apply, smul_eq_mul]
      calc
        _ = ∑ e : {e // e ∈ S},
            c * (normalizedWeight S q e * a e) := by
          apply Fintype.sum_congr
          intro e
          ring
        _ = c * ∑ e : {e // e ∈ S},
            normalizedWeight S q e * a e := by
          rw [Finset.mul_sum] }

def weightedZeroMeanSpace {E : Type*} [DecidableEq E]
    (S : Finset E) (q : E → ℚ) :
    Submodule ℚ ({e // e ∈ S} → ℚ) :=
  (weightedMeanMap S q).ker

end MathlibPlus.ResearchFormalization.R4377Claim54358

namespace MathlibPlus.Open.ResearchFormalization.R4377

open MathlibPlus.ResearchFormalization.R4377Claim54358

/-- R-4377.1: weighted-zero-mean evaluation on the exact finite rational circuit. -/
def claim54358 : Prop :=
  ∀ (E V : Type*) [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (S : Finset E) (L : scalarCellMap E V) (q : E → ℚ),
    circuitFacts S L q →
      ∃ ev : (circuitSpan S L →ₗ[ℚ] ℚ) ≃ₗ[ℚ]
          weightedZeroMeanSpace S q,
        ∀ phi : circuitSpan S L →ₗ[ℚ] ℚ,
          (ev phi : {e // e ∈ S} → ℚ) = evaluationMap S L phi

end MathlibPlus.Open.ResearchFormalization.R4377
