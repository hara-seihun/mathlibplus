import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0950

noncomputable section

/-- The eight-point fiber `C₂³`, represented as the additive cube over `ZMod 2`. -/
abbrev cube : Type := Fin 3 → ZMod 2

/-- The displacement map of a permutation of the fiber. -/
def displacement (σ : Equiv.Perm cube) : cube → cube :=
  fun x => σ x - x

/-- Rank of the span of all permutation displacements over `F₂`. -/
noncomputable def displacementRank (σ : Equiv.Perm cube) : ℕ :=
  Module.finrank (ZMod 2)
    (Submodule.span (ZMod 2) (Set.range (displacement σ)))

/-- A permutation of the cube is affine when it is an additive automorphism
followed by a translation. -/
def IsAffine (σ : Equiv.Perm cube) : Prop :=
  ∃ A : cube ≃+ cube, ∃ b : cube, ∀ x, σ x = A x + b

noncomputable def allRankCard (r : Fin 4) : ℕ :=
  let α := {σ : Equiv.Perm cube // displacementRank σ = r.1}
  letI : Fintype α := Fintype.ofFinite α
  Fintype.card α

noncomputable def affineRankCard (r : Fin 4) : ℕ :=
  let α := {σ : Equiv.Perm cube // displacementRank σ = r.1 ∧ IsAffine σ}
  letI : Fintype α := Fintype.ofFinite α
  Fintype.card α

noncomputable def nonlinearRankCard (r : Fin 4) : ℕ :=
  let α := {σ : Equiv.Perm cube // displacementRank σ = r.1 ∧ ¬ IsAffine σ}
  letI : Fintype α := Fintype.ofFinite α
  Fintype.card α

noncomputable def nonlinearTotalCard : ℕ :=
  let α := {σ : Equiv.Perm cube // ¬ IsAffine σ}
  letI : Fintype α := Fintype.ofFinite α
  Fintype.card α

/-- The exact displacement-rank census on the eight-point fiber, with each
triple ordered `(all, affine, nonlinear)`. -/
def claim27502_exactDisplacementRankCensus : Prop :=
  (∀ r : Fin 4,
    (allRankCard r, affineRankCard r, nonlinearRankCard r) =
      (![ (8, 8, 0),
          (392, 168, 224),
          (6832, 784, 6048),
          (33088, 384, 32704) ] : Fin 4 → ℕ × ℕ × ℕ) r) ∧
    nonlinearTotalCard = 38976 ∧
    nonlinearRankCard 3 = 32704

end

end MathlibPlus.Open.NewResearch2.R0950
