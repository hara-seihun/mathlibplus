import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.R1527Counterexample

abbrev F₃ := ZMod 3
abbrev W := Fin 2 → F₃
abbrev U := W × F₃

def coordinateNormal : W →ₗ[F₃] F₃ :=
  LinearMap.proj 0

def twoRows : Finset F₃ := {0, 1}
def singletonLabels : F₃ → Finset F₃ := fun _ => {0}
def shiftedLabels : F₃ → Finset F₃ := fun a => if a = 1 then {1} else {0}
def twoRowUnion (L : F₃ → Finset F₃) : Set U :=
  {x | ∃ a ∈ twoRows, ∃ ell ∈ L a,
    coordinateNormal x.1 = ell ∧ x.2 = a}
def twoRowDifference (L : F₃ → Finset F₃) (v : W) (c : F₃) : ℕ := by
  classical
  exact (Finset.univ.filter (fun xy : U × U =>
    xy.1 ∈ twoRowUnion L ∧ xy.2 ∈ twoRowUnion L ∧ xy.1 - xy.2 = (v, c))).card

def repeatedNormalCounterexample_claim38136 : Prop :=
  (Finset.univ.filter (fun u : U =>
    twoRowDifference singletonLabels u.1 u.2 ≠
      twoRowDifference shiftedLabels u.1 u.2)).card = 12

end MathlibPlus.Open.ResearchBatch.R1527Counterexample
