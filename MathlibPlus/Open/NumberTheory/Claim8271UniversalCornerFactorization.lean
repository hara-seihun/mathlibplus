import MathlibPlus.NumberTheory.Claim8276

open scoped BigOperators

namespace MathlibPlus.Open.NumberTheory

open MathlibPlus.NumberTheory.Claim8276

/-- The exact prime product called `H_(chi,N)(w,v)` in Claim 8271. -/
noncomputable def cornerRemainder (N : ℕ) (χ : DirichletCharacter ℂ N)
    (w v : ℂ) : ℂ :=
  ∏' p : {p : ℕ // p.Prime ∧ ¬ p ∣ N},
    (1 - Complex.cpow (p : ℂ) (-1 - w) +
        Complex.cpow (p : ℂ) (-1 - w - v) -
        χ p * Complex.cpow (p : ℂ) (-1 - v)) *
      ((1 - Complex.cpow (p : ℂ) (-1 - w - v)) /
        ((1 - Complex.cpow (p : ℂ) (-1 - w)) *
          (1 - χ p * Complex.cpow (p : ℂ) (-1 - v))))

/-- Claim 8271: the universal corner factorization on the positive
real-part domain for an odd Dirichlet character. -/
def claim8271_universalCornerFactorization : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (w v : ℂ),
    N > 1 →
    χ (-1 : ZMod N) = (-1 : ℂ) →
    0 < w.re →
    0 < v.re →
    dirichletL N χ (1 : ℂ) * arithmeticSum N χ w v =
      (incompleteZeta N (1 + w + v) /
          incompleteZeta N (1 + w)) *
        (dirichletL N χ (1 : ℂ) /
          dirichletL N χ (1 + v)) *
      cornerRemainder N χ w v

end MathlibPlus.Open.NumberTheory
