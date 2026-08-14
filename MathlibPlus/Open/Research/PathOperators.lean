import Mathlib

namespace MathlibPlus.Open.Research.PathOperators

abbrev MatchingPolynomial := Polynomial ℚ

noncomputable def t : MatchingPolynomial := Polynomial.X

noncomputable def sideForestOperator (A L : MatchingPolynomial) :
    Matrix (Fin 2) (Fin 2) MatchingPolynomial :=
  fun i j =>
    if i = 0 then
      if j = 0 then t * A + L else A
    else if j = 0 then A else 0

noncomputable def transferMatrix
    (word : List (MatchingPolynomial × MatchingPolynomial)) :
    Matrix (Fin 2) (Fin 2) MatchingPolynomial :=
  (word.map (fun state => sideForestOperator state.1 state.2)).foldl
    (fun acc next => acc * next) 1

def claim_26294 : Prop :=
  (∀ (A L : MatchingPolynomial),
    Matrix.transpose (sideForestOperator A L) = sideForestOperator A L) ∧
  (∀ (word : List (MatchingPolynomial × MatchingPolynomial)),
    transferMatrix word.reverse = Matrix.transpose (transferMatrix word))

end MathlibPlus.Open.Research.PathOperators
