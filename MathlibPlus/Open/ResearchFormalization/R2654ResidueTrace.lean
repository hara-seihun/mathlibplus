import MathlibPlus.Open.ResearchFormalization.R2654RawResultantRepair

namespace MathlibPlus.Open.ResearchFormalization.R2654ResidueTrace

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.R2654RawResultantRepair

/-- Claim 42190: in the reviewed genuine Type-IV carrier, the complete pole
configuration of `q/r` has positive residue ratios at the ordered interior
poles and a negative ratio at the unique exterior pole. -/
def claim42190 : Prop :=
  ∀ (n : ℕ) (ell A Astar R P1 P2 q r c : Polynomial ℤ),
    genuineTypeIVWitness n ell A Astar R P1 P2 q r c →
      let qR := q.map (algebraMap ℤ ℝ)
      let rR := r.map (algebraMap ℤ ℝ)
      ∃ u : Fin n → ℝ, ∃ b : ℝ,
        StrictMono u ∧
          (∀ i : Fin n,
            -2 < u i ∧ u i < 2 ∧
              Polynomial.eval (u i) rR = 0 ∧
                0 < Polynomial.eval (u i) qR /
                  Polynomial.eval (u i) rR.derivative) ∧
            2 < b ∧ Polynomial.eval b rR = 0 ∧
              Polynomial.eval b qR /
                  Polynomial.eval b rR.derivative < 0 ∧
                (∀ z : ℂ, evalRealComplex rR z = 0 →
                  (∃ i : Fin n, z = (u i : ℂ)) ∨ z = (b : ℂ))

/-- Claim 42191: in the reviewed genuine Type-IV carrier, the unique target
trace zero in the interval `(2,b)` occurs before the exterior pole `b` of
`q/r`. -/
def claim42191 : Prop :=
  ∀ (n : ℕ) (ell A Astar R P1 P2 q r c : Polynomial ℤ),
    genuineTypeIVWitness n ell A Astar R P1 P2 q r c →
      let ellR := ell.map (algebraMap ℤ ℝ)
      let qR := q.map (algebraMap ℤ ℝ)
      let rR := r.map (algebraMap ℤ ℝ)
      ∃ u : Fin n → ℝ, ∃ b : ℝ, ∃ T : ℝ,
        StrictMono u ∧
          (∀ i : Fin n,
            -2 < u i ∧ u i < 2 ∧
              Polynomial.eval (u i) rR = 0 ∧
                0 < Polynomial.eval (u i) qR /
                  Polynomial.eval (u i) rR.derivative) ∧
            2 < b ∧ Polynomial.eval b rR = 0 ∧
              Polynomial.eval b qR /
                  Polynomial.eval b rR.derivative < 0 ∧
                (∀ z : ℂ, evalRealComplex rR z = 0 →
                  (∃ i : Fin n, z = (u i : ℂ)) ∨ z = (b : ℂ)) ∧
                  2 < T ∧ T < b ∧ Polynomial.eval T ellR = 0 ∧
                    ∀ s : ℝ, 2 < s → s < b →
                      Polynomial.eval s ellR = 0 → s = T

end

end MathlibPlus.Open.ResearchFormalization.R2654ResidueTrace
