import Mathlib

open Classical
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1552HomogeneousQuadraticFamily39166

noncomputable section

abbrev F3 := ZMod 3
abbrev State := Fin 4 → F3
abbrev Ternary := Fin 3 → F3
abbrev Binary := Fin 2 → F3

/-- The two nondegenerate binary quadratic representatives over `F₃`. -/
def binaryQuadratic (q : Fin 2) (v w : F3) : F3 :=
  if q = 0 then v * (v + w) else v ^ 2 + w ^ 2

/-- Homogeneous quadratic forms in three coordinates, with their six actual
monomial coefficients. -/
def homogeneousQuadratic (coeff : Fin 6 → F3) (x : Ternary) : F3 :=
  coeff 0 * x 0 ^ 2 +
    coeff 1 * x 1 ^ 2 +
      coeff 2 * x 2 ^ 2 +
        coeff 3 * x 0 * x 1 +
          coeff 4 * x 0 * x 2 +
            coeff 5 * x 1 * x 2

def familyTransporter (q : Fin 2) (lambda : F3)
    (coeff : Fin 6 → F3) (x : State) : State :=
  ![
    x 0 + homogeneousQuadratic coeff ![x 1, x 2, x 3],
    x 1 + binaryQuadratic q (x 2) (x 3),
    x 2 + lambda * x 3,
    x 3
  ]

abbrev Row := Fin 2 × F3 × (Fin 6 → F3)

def rowTransporter (r : Row) : State → State :=
  familyTransporter r.1 r.2.1 r.2.2

/-- Claim 39166: the Record-6 family is the exact two-type, three-parameter,
three-variable homogeneous-quadratic triangular family. -/
def claim39166 : Prop :=
  Nat.card Row = 2 * 3 * 3 ^ 6 ∧
    (∀ (q : Fin 2) (lambda : F3) (coeff : Fin 6 → F3)
      (x : State),
      rowTransporter (q, lambda, coeff) x =
        ![
          x 0 + homogeneousQuadratic coeff ![x 1, x 2, x 3],
          x 1 + binaryQuadratic q (x 2) (x 3),
          x 2 + lambda * x 3,
          x 3
        ])

end

end MathlibPlus.Open.ResearchFormalization.R1552HomogeneousQuadraticFamily39166
