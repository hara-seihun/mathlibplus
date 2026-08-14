import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R5784

noncomputable section

/-- The two table rows of the pointed switch in the vector order
`00,01,02,10,11,12,20,21,22`. -/
def q₀ : Fin 9 → Fin 9 :=
  ![0, 2, 8, 6, 3, 7, 1, 5, 4]

def q₁ : Fin 9 → Fin 9 :=
  ![1, 4, 5, 2, 0, 8, 7, 3, 6]

def switchQ : Fin 9 × Fin 2 → Fin 9 × Fin 2 :=
  fun v => if v.2 = 0 then (q₀ v.1, 0) else (q₁ v.1, 1)

def reflectionHat (A : Finset (Fin 9)) : Finset (Fin 9 × Fin 2) :=
  A.product ({1} : Finset (Fin 2))

def B : Finset (Fin 9) := {0, 1, 4}
def C : Finset (Fin 9) := {2, 7, 8}
def D : Finset (Fin 9) := {3, 5, 6}

/-- R-5784.1: the displayed pointed bijection on the two layers of the
concrete encoding of `Dih(𝔽₃²)`, together with the asserted action on the
three reflection triangles. -/
def claim58507 : Prop :=
  Function.Bijective switchQ ∧
    switchQ (0, 0) = (0, 0) ∧
    (reflectionHat B).image switchQ = reflectionHat B ∧
    (reflectionHat C).image switchQ = reflectionHat D ∧
    (reflectionHat D).image switchQ = reflectionHat C

end

end MathlibPlus.Open.ResearchFormalization.R5784
