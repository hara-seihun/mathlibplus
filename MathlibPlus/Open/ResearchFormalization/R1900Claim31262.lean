import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1900

noncomputable section

open Classical

abbrev TraceVertex31262 := Fin 5

def exactTrace31262
    (A B : Finset TraceVertex31262) : Finset TraceVertex31262 :=
  A ∩ B

def residual31262
    (A B : Finset TraceVertex31262) : Finset TraceVertex31262 :=
  B \ A

/-- The exact-intersection trace witness: equal trace sizes do not identify
trace classes, and the corresponding residuals have different behavior. -/
def claim31262 : Prop :=
  let A : Finset TraceVertex31262 := {1, 2}
  let B : Finset TraceVertex31262 := {1, 3}
  let C : Finset TraceVertex31262 := {2, 4}
  exactTrace31262 A B = {1} ∧
    exactTrace31262 A C = {2} ∧
    (exactTrace31262 A B).card = (exactTrace31262 A C).card ∧
    exactTrace31262 A B ≠ exactTrace31262 A C ∧
    residual31262 A B = {3} ∧
    residual31262 A C = {4} ∧
    Disjoint (residual31262 A B) (residual31262 A C) ∧
    residual31262 A B ≠ residual31262 A C

end
end MathlibPlus.Open.ResearchFormalization.R1900
