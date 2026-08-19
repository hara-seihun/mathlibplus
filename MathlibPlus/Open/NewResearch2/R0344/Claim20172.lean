import Mathlib
import MathlibPlus.Open.NewResearch2.R0344Claim20167

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0344.Claim20172

noncomputable section

open MathlibPlus.Open.NewResearch2.R0344

abbrev SelectedPrimes := Fin 160 → ℕ

def selectedMode (R : ℕ) (primes : SelectedPrimes) (S : Finset ℕ) : Prop :=
  S.card = 8 ∧
    ∀ p ∈ S, ∃ i : Fin 160, p = primes i ∧ selectedPrime R (primes i)

def beta20172 (U : ℝ) : ℝ :=
  (1 + 7 / 50) / 2 + (901 / 10000 / 4) * Real.log U

noncomputable def residualQ20172 (q : ℕ → ℝ) (U : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 (32768 * 175000000),
    (q n : ℂ) * Real.rpow (n : ℝ) (-beta20172 U) *
      Complex.exp (2 * Real.pi * Complex.I *
        ((U : ℂ) * Real.log (n : ℝ)))

noncomputable def firstOpenDyadicBlock20172 : Set ℝ :=
  Set.Icc
    ((690989 : ℝ) ^ 2 - (901 / 10000 : ℝ) / 16)
    ((1381978 : ℝ) ^ 2 - (901 / 10000 : ℝ) / 16)

def exactLongBeatObstruction_claim20172
    (q : ℕ → ℝ) (primes : SelectedPrimes) : Prop :=
  Function.Injective primes ∧
    (∀ i : Fin 160, selectedPrime 175000000 (primes i)) ∧
    q 1 = 0 ∧
    (∀ i : Fin 160,
      q (primes i) =
          Real.exp ((901 / 10000 : ℝ) / 4 *
            Real.log (primes i : ℝ) ^ 2) ∧
        q (primes i) ≠ 0) ∧
    (firstOpenDyadicBlock20172).OrdConnected ∧
    (∃ S T : Finset ℕ,
      selectedMode 175000000 primes S ∧
        selectedMode 175000000 primes T ∧
        S ≠ T ∧
        let Q : MvPolynomial ℕ ℝ :=
          residualPolynomial 32768 175000000 q
        let K_S : ℕ := S.prod id
        let K_T : ℕ := T.prod id
        let f_S : ℝ := Real.log (K_S : ℝ)
        let f_T : ℝ := Real.log (K_T : ℝ)
        MvPolynomial.coeff (Nat.factorization K_S) (Q ^ 8) =
            (Nat.factorial 8 : ℝ) * Finset.prod S (fun p => q p) ∧
          MvPolynomial.coeff (Nat.factorization K_T) (Q ^ 8) =
            (Nat.factorial 8 : ℝ) * Finset.prod T (fun p => q p) ∧
          MvPolynomial.coeff (Nat.factorization K_S) (Q ^ 8) ≠ 0 ∧
          MvPolynomial.coeff (Nat.factorization K_T) (Q ^ 8) ≠ 0 ∧
          f_S ≠ 0 ∧ f_T ≠ 0 ∧
          f_S ≠ f_T ∧
          |f_S - f_T| < 1 / (3 * (690989 : ℝ) ^ 2) ∧
          (1 / |f_S - f_T|) > 3 * (690989 : ℝ) ^ 2 ∧
          ((2 * (690989 : ℝ)) ^ 2 - (690989 : ℝ) ^ 2 =
            3 * (690989 : ℝ) ^ 2) ∧
          ((2 * (690989 : ℝ)) ^ 2 - (690989 : ℝ) ^ 2 >
            0))

end

end MathlibPlus.Open.NewResearch2.R0344.Claim20172
