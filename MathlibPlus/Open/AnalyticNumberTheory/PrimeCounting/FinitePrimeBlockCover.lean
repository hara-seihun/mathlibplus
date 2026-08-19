import MathlibPlus.AxlerMajorant

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

noncomputable section

/-- Claim 635: the exact 24,276-block finite certificate for the canonical
`6097.2` majorant.  Prime indices are one-based, so `p_i` is
`Nat.nth Nat.Prime (i - 1)`. -/
def finitePrimeBlockCover : Prop :=
  let primeAtIndex : ℕ → ℕ := fun i => Nat.nth Nat.Prime (i - 1)
  let primeCountingReal : ℝ → ℕ := fun x => Nat.primeCounting (Nat.floor x)
  ∃ firstIndex lastIndex : Fin 24276 → ℕ,
    primeAtIndex 15 = 47 ∧
      firstIndex 0 = 15 ∧
      (∀ k : Fin 24276,
        1 ≤ firstIndex k ∧ firstIndex k ≤ lastIndex k) ∧
      (∀ k : Fin 24275,
        firstIndex k.succ = lastIndex k.castSucc + 1) ∧
      (∀ k : Fin 24276,
        MathlibPlus.AxlerMajorant.predecessorBound
              (primeAtIndex (firstIndex k)) > (lastIndex k : ℝ) ∧
          MathlibPlus.AxlerMajorant.predecessorBound
              (primeAtIndex (firstIndex k)) - (lastIndex k : ℝ) >
            (250017899 : ℝ) / 1000000000 ∧
          ∀ x : ℝ,
            (primeAtIndex (firstIndex k) : ℝ) ≤ x →
            x < (primeAtIndex (lastIndex k + 1) : ℝ) →
            (primeCountingReal x : ℝ) <
              MathlibPlus.AxlerMajorant.predecessorBound x) ∧
      (primeAtIndex (firstIndex (Fin.last 24275)) : ℝ) ≤ 205000000 ∧
      (205000000 : ℝ) <
        (primeAtIndex (lastIndex (Fin.last 24275) + 1) : ℝ) ∧
      ∀ x : ℝ, 47 ≤ x → x ≤ 205000000 →
        (primeCountingReal x : ℝ) <
          MathlibPlus.AxlerMajorant.predecessorBound x

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
