import Mathlib

open Classical
open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.GraphTheory.Claim31564

abbrev F7 := ZMod 7
abbrev State31564 := (F7 → F7) × (F7 → F7)

private def baseLine31564 : Finset F7 :=
  {0, 1, 3}

private def translateLine31564 (t : F7) : Finset F7 :=
  baseLine31564.image (fun x => x + t)

private def normalizedOutput31564 (f : F7 → F7) : F7 → F7 :=
  fun x => f x - f 0

private def shiftedDerivative31564
    (g : F7 → F7) (t : F7) : F7 → F7 :=
  fun s => g (t + s) - g t

private def scalarState31564 (g : F7 → F7) : Prop :=
  ∃ a : F7, a ≠ 0 ∧ ∀ x : F7, g x = a * x

private def pointStates31564 : Finset (F7 → F7) :=
  (Finset.univ : Finset (Equiv.Perm F7)).image
    (fun σ => normalizedOutput31564 σ)

private def pointFixedPairs31564 :
    Finset ((F7 → F7) × F7) :=
  (pointStates31564.product
      ((Finset.univ : Finset F7).filter (fun t => t ≠ 0))).filter
    (fun pair => shiftedDerivative31564 pair.1 pair.2 = pair.1)

private def fanoIncidenceStates31564 : Finset State31564 :=
  ((Finset.univ : Finset State31564)).filter
    (fun state =>
      state.1 0 = 0 ∧ state.2 0 = 0 ∧
        ∃ σ : Equiv.Perm F7,
          state.1 = normalizedOutput31564 σ ∧
            ∀ t : F7,
              (translateLine31564 t).image σ =
                translateLine31564 (state.2 t + σ 0))

private def lineFixedPairs31564 :
    Finset (State31564 × F7) :=
  (fanoIncidenceStates31564.product
      ((Finset.univ : Finset F7).filter (fun t => t ≠ 0))).filter
    (fun pair =>
      shiftedDerivative31564 pair.1.2 pair.2 = pair.1.2)

private def mixedAction31564
    (state : State31564) (kind : Fin 2) : F7 → F7 :=
  normalizedOutput31564
    (if kind = (0 : Fin 2) then state.1 else state.2)

private def mixedRowValid31564
    (left right : Fin 2) (step : F7)
    (row : F7 → State31564) : Prop :=
  (∀ y : F7, row y ∈ fanoIncidenceStates31564) ∧
    ∀ y : F7,
      mixedAction31564 (row (y + step)) right =
        mixedAction31564 (row y) left

private def mixedRows31564
    (left right : Fin 2) (step : F7) :
    Finset (F7 → State31564) :=
  (Finset.univ : Finset (F7 → State31564)).filter
    (mixedRowValid31564 left right step)

private def mixedNonlinearRows31564
    (left right : Fin 2) (step : F7) :
    Finset (F7 → State31564) :=
  (mixedRows31564 left right step).filter
    (fun row => ∃ y : F7, ¬scalarState31564 (row y).1)

def incidenceStateRigidity_claim31564 : Prop :=
  pointStates31564.card = 720 ∧
    (pointStates31564.filter scalarState31564).card = 6 ∧
    (∀ g ∈ pointStates31564,
      ((∃ t : F7, t ≠ 0 ∧
          shiftedDerivative31564 g t = g) ↔ scalarState31564 g)) ∧
    pointFixedPairs31564.card = 36 ∧
    (pointFixedPairs31564.filter
      (fun pair => ¬scalarState31564 pair.1)).card = 0 ∧
    fanoIncidenceStates31564.card = 24 ∧
    (fanoIncidenceStates31564.filter
      (fun state => scalarState31564 state.1)).card = 3 ∧
    (∀ state ∈ fanoIncidenceStates31564,
      (∃ t : F7, t ≠ 0 ∧
        shiftedDerivative31564 state.2 t = state.2) →
          scalarState31564 state.1) ∧
    lineFixedPairs31564.card = 18 ∧
    (lineFixedPairs31564.filter
      (fun pair => ¬scalarState31564 pair.1.1)).card = 0 ∧
    (∀ (left right : Fin 2), left ≠ right →
      ∀ step : F7, step ≠ 0 →
        (mixedRows31564 left right step).card = 3 ∧
          (mixedNonlinearRows31564 left right step).card = 0) ∧
    2 * 6 * fanoIncidenceStates31564.card = 288 ∧
    2 * 6 * 3 = 36

end MathlibPlus.Open.GraphTheory.Claim31564

end
