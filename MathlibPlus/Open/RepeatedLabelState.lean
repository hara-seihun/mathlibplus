import Mathlib

namespace MathlibPlus.Open.RepeatedLabelState

open scoped BigOperators

/-- The elementary symmetric sum of degree `k` in the occurrence labels selected by `s`.

The variables of `MvPolynomial α ℚ` are the distinct cavity labels `α`; the map
`labels` records which variable occurs at each of the six labeled occurrences.
-/
private noncomputable def elementarySymmetricSum
    {α : Type*} (k : ℕ) (s : Finset (Fin 6))
    (labels : Fin 6 → α) : MvPolynomial α ℚ :=
  ∑ t ∈ Finset.powersetCard k s, ∏ i ∈ t, MvPolynomial.X (labels i)

/-- The symmetric two-coordinate state of an unordered three-versus-three
bipartition of six labeled occurrences.  The state is symmetric in the chosen
representative and its complement. -/
noncomputable def universalRepeatedLabelTernaryState
    {α : Type*} (labels : Fin 6 → α)
    (_hlabels : Function.Surjective labels)
    (E : {E : Finset (Fin 6) // E.card = 3}) :
    MvPolynomial α ℚ × MvPolynomial α ℚ :=
  ( elementarySymmetricSum 2 E.1 labels +
      elementarySymmetricSum 2 (Finset.univ \ E.1) labels,
    elementarySymmetricSum 3 E.1 labels +
      elementarySymmetricSum 3 (Finset.univ \ E.1) labels )

end MathlibPlus.Open.RepeatedLabelState
