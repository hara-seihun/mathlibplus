import MathlibPlus.Open.NumberTheory.ResearchEulerFactor

namespace MathlibPlus.Open.NumberTheory.OddCharacterClaim8274

open Classical
open MathlibPlus.Open.NumberTheory
open scoped BigOperators

noncomputable def oddDirichletCharacters8274 (N : ℕ) :
    Finset (DirichletCharacter ℂ N) :=
  Finset.univ.filter (fun χ => DirichletCharacter.Odd χ)

noncomputable def analyticDirichletL8274 (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  @DirichletCharacter.LFunction N ⟨Nat.ne_of_gt hN⟩ χ s

noncomputable def completedUnitStratum8274 (N : ℕ) (hN : 0 < N)
    (w : ℂ) : ℂ :=
  (2 : ℂ) / (Nat.totient N : ℂ) *
    ∑ χ ∈ oddDirichletCharacters8274 N,
      analyticDirichletL8274 N hN (star χ) 0 *
        (analyticDirichletL8274 N hN χ 1 * researchEulerSum N χ w 0)

/-- The odd-character inversion value and the completed v=0 unit stratum,
using the analytically continued Dirichlet L-function. -/
def oddCharacterInversionValue_claim8274 : Prop :=
  (∀ N : ℕ, ∀ hN' : 1 < N,
    (2 : ℂ) / (Nat.totient N : ℂ) *
        ∑ χ ∈ oddDirichletCharacters8274 N,
          analyticDirichletL8274 N (Nat.zero_lt_of_lt hN') (star χ) 0 =
      1 - (2 : ℂ) / (N : ℂ)) ∧
  (∀ N : ℕ, ∀ hN' : 1 < N, ∀ w : ℂ, 0 < w.re →
    completedUnitStratum8274 N (Nat.zero_lt_of_lt hN') w =
      1 - (2 : ℂ) / (N : ℂ)) ∧
  (∀ w : ℂ, 0 < w.re →
    completedUnitStratum8274 2 (Nat.zero_lt_succ 1) w = 0 ∧
      1 - (2 : ℂ) / (2 : ℂ) = 0)

end MathlibPlus.Open.NumberTheory.OddCharacterClaim8274
