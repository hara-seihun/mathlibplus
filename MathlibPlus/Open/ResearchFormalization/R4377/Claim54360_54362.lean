import MathlibPlus.Open.ResearchFormalization.R4377.Claim54358

open scoped BigOperators
noncomputable section

namespace MathlibPlus.ResearchFormalization.R4377Claim54360_54362

open MathlibPlus.ResearchFormalization.R4377Claim54358

abbrev dualSpace {E V : Type*} [DecidableEq E] [AddCommGroup V]
    [Module ℚ V] [FiniteDimensional ℚ V]
    (S : Finset E) (L : scalarCellMap E V) :=
  circuitSpan S L →ₗ[ℚ] ℚ

def oneVersusRestValue {E : Type*} [DecidableEq E]
    (S : Finset E) (q : E → ℚ) (e : {e // e ∈ S}) : ℚ :=
  -((1 - normalizedWeight S q e) / normalizedWeight S q e)

def otherColumnsBasis {E V : Type*} [DecidableEq E] [AddCommGroup V]
    [Module ℚ V] [FiniteDimensional ℚ V]
    (S : Finset E) (L : scalarCellMap E V)
    (e : {e // e ∈ S}) : Prop :=
  ∃ b : Module.Basis {f : {f // f ∈ S} // f ≠ e} ℚ (circuitSpan S L),
    ∀ f, b f = columnInSpan S L f.1

def canonicalDualFrame {E V : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (S : Finset E) (L : scalarCellMap E V) (q : E → ℚ)
    (theta : {e // e ∈ S} →
      dualSpace (E := E) (V := V) S L) : Prop :=
  (∀ e : {e // e ∈ S}, otherColumnsBasis S L e) ∧
    (∀ e : {e // e ∈ S},
      (∃! phi : dualSpace (E := E) (V := V) S L,
        ∀ f : {f // f ∈ S}, f ≠ e →
          phi (columnInSpan (E := E) (V := V) S L f) = 1) ∧
      (∀ f : {f // f ∈ S}, f ≠ e →
        theta e (columnInSpan (E := E) (V := V) S L f) = 1) ∧
      theta e (columnInSpan (E := E) (V := V) S L e) =
        oneVersusRestValue S q e) ∧
    (∑ e : {e // e ∈ S}, normalizedWeight S q e • theta e) = 0 ∧
    (∀ c : {e // e ∈ S} → ℚ,
      (∑ e : {e // e ∈ S}, c e • theta e) = 0 →
        ∃ r : ℚ, ∀ e, c e = r * normalizedWeight S q e) ∧
    Submodule.span ℚ (Set.range theta) = ⊤ ∧
    (∀ T : Finset {e // e ∈ S}, T ⊂ Finset.univ →
      LinearIndependent ℚ (fun e : {e // e ∈ T} => theta e.1))

def subsetWeight {E : Type*} [DecidableEq E]
    (S : Finset E) (q : E → ℚ) (T : Finset {e // e ∈ S}) : ℚ :=
  ∑ e ∈ T, normalizedWeight S q e

def supportCut {E V : Type*} [DecidableEq E] [AddCommGroup V]
    [Module ℚ V] [FiniteDimensional ℚ V]
    (S : Finset E) (L : scalarCellMap E V) (q : E → ℚ)
    (theta : {e // e ∈ S} → dualSpace S L)
    (T : Finset {e // e ∈ S}) : dualSpace S L :=
  ∑ e ∈ T, normalizedWeight S q e • theta e

end MathlibPlus.ResearchFormalization.R4377Claim54360_54362

namespace MathlibPlus.Open.ResearchFormalization.R4377

open MathlibPlus.ResearchFormalization.R4377Claim54358
open MathlibPlus.ResearchFormalization.R4377Claim54360_54362

/-- R-4377.2: the canonical one-versus-rest dual frame on the exact circuit. -/
def claim54360 : Prop :=
  ∀ (E V : Type*) [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (S : Finset E) (L : scalarCellMap E V) (q : E → ℚ),
    circuitFacts S L q →
      ∃ theta : {e // e ∈ S} →
          dualSpace (E := E) (V := V) S L,
        canonicalDualFrame S L q theta

/-- R-4377.3: canonical two-level support cuts on the exact circuit. -/
def claim54362 : Prop :=
  ∀ (E V : Type*) [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (S : Finset E) (L : scalarCellMap E V) (q : E → ℚ),
    circuitFacts S L q →
      ∃ theta : {e // e ∈ S} → dualSpace S L,
        canonicalDualFrame S L q theta ∧
        ∀ T : Finset {e // e ∈ S}, T.Nonempty → T ⊂ Finset.univ →
          let lambdaT := subsetWeight S q T
          let chi := supportCut S L q theta T
          (∀ f : {e // e ∈ S},
            chi (columnInSpan S L f) =
              if f ∈ T then -(1 - lambdaT) else lambdaT) ∧
          supportCut S L q theta (Finset.univ \ T) = -chi ∧
          (∀ phi : dualSpace S L,
            (∀ f : {e // e ∈ S},
              phi (columnInSpan S L f) =
                chi (columnInSpan S L f)) →
              phi = chi)

end MathlibPlus.Open.ResearchFormalization.R4377
