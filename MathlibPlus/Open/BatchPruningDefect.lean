import Mathlib

namespace MathlibPlus.Open.PruningDefect

open MvPolynomial

abbrev PruningPolynomial := MvPolynomial (Fin 3) ℚ

noncomputable def pruningFactor : PruningPolynomial :=
  1 + X 0 * X 1 + (X 0)^2 * (X 2 + (X 1)^2)

noncomputable def activeFaceA : PruningPolynomial := pruningFactor

noncomputable def activeFaceB : PruningPolynomial := pruningFactor ^ 2

noncomputable def activeFaceC : PruningPolynomial := pruningFactor ^ 3

def activeFaceDefect : Prop :=
  activeFaceA - 2 * activeFaceB + activeFaceC =
      pruningFactor * (pruningFactor - 1)^2 ∧
    pruningFactor ≠ 0 ∧ pruningFactor - 1 ≠ 0 ∧
    activeFaceA - 2 * activeFaceB + activeFaceC ≠ 0

end MathlibPlus.Open.PruningDefect
