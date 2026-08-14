import Mathlib

namespace MathlibPlus.Open.Analysis.GammaJetBatch

noncomputable def hurwitzZetaFiveQuarters (m : ℕ) : ℝ :=
  ∑' r : ℕ, 1 / (((r : ℝ) + (5 : ℝ) / 4) ^ m)

noncomputable def gammaLogJetCoeff (m : ℕ) : ℝ :=
  if m = 1 then
    (Real.log Real.pi - (Complex.digamma ((5 : ℂ) / 4)).re) / 2
  else if 2 ≤ m then
    hurwitzZetaFiveQuarters m / ((m : ℝ) * (2 : ℝ) ^ m)
  else 0

noncomputable def gammaTaylorCoeff (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (n + 1)) (fun k =>
    (1 / (Nat.factorial k : ℝ)) *
      Finset.sum
        (Finset.filter (fun v : Fin k → Fin (n + 1) =>
          (∑ i : Fin k, (v i).val) = n)
          (Finset.univ : Finset (Fin k → Fin (n + 1))))
        (fun v => ∏ i : Fin k, gammaLogJetCoeff ((v i).val)))

noncomputable def gammaToeplitz (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i.val ≤ j.val then gammaTaylorCoeff (j.val - i.val) else 0

noncomputable def gammaSolidMinor : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    if i.val ≤ j.val + 1 then gammaTaylorCoeff (j.val + 1 - i.val) else 0

def totallyNonnegative {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ k : ℕ, ∀ I J : Fin k → Fin n,
    Function.Injective I → Function.Injective J →
      0 ≤ Matrix.det (fun i j => A (I i) (J j))

/-- Claim 19333: the alternating gamma log jet and all resulting Taylor
coefficients have the displayed positive coefficients. -/
def alternatingGaugeGammaJet_claim19333 : Prop :=
  gammaLogJetCoeff 1 =
      (Real.log Real.pi - (Complex.digamma ((5 : ℂ) / 4)).re) / 2 ∧
    (∀ m : ℕ, 2 ≤ m →
      gammaLogJetCoeff m =
        hurwitzZetaFiveQuarters m / ((m : ℝ) * (2 : ℝ) ^ m)) ∧
    (0 < gammaLogJetCoeff 1) ∧
    (∀ m : ℕ, 2 ≤ m → 0 < gammaLogJetCoeff m) ∧
    (∀ m : ℕ, 0 < gammaTaylorCoeff m)

/-- Claim 19334: the exact solid three-by-three gamma Toeplitz minor. -/
def exactSolidCompoundGamma_claim19334 : Prop :=
  Matrix.det gammaSolidMinor =
    (gammaTaylorCoeff 0) ^ 3 *
      ((gammaLogJetCoeff 1) ^ 3 / 6
        - gammaLogJetCoeff 1 * gammaLogJetCoeff 2
        + gammaLogJetCoeff 3)

/-- Claim 19335: the explicit solid minor is negative although the Toeplitz
matrix has nonnegative entries and positive entries on its upper triangle. -/
def gammaToeplitzNotTotallyNonnegative_claim19335 : Prop :=
  let L := gammaLogJetCoeff 1
  let ell2 := gammaLogJetCoeff 2
  let ell3 := gammaLogJetCoeff 3
  let normalized := L ^ 3 / 6 - L * ell2 + ell3
  normalized < 0 ∧
    (-21198 / 1000000 : ℝ) < normalized ∧
    normalized < (-21196 / 1000000 : ℝ) ∧
    (∀ (n : ℕ) (i : Fin n) (j : Fin n),
      0 ≤ gammaToeplitz n i j) ∧
    (∀ (n : ℕ) (i : Fin n) (j : Fin n),
      i.val ≤ j.val → 0 < gammaToeplitz n i j) ∧
    ¬ totallyNonnegative (gammaToeplitz 4)

/-- Claim 19336: sign conjugation preserving entrywise nonnegativity cannot
remove the negative solid minor. -/
def signConjugationCannotRepairGamma_claim19336 : Prop :=
  ¬ ∃ (ε : Fin 4 → ℝ),
    (∀ i, ε i = 1 ∨ ε i = -1) ∧
    (∀ i j, 0 ≤ ε i * gammaToeplitz 4 i j * ε j) ∧
    0 ≤ Matrix.det (fun i j : Fin 3 =>
      ε (Fin.castSucc i) * gammaToeplitz 4 (Fin.castSucc i) (Fin.succ j) *
        ε (Fin.succ j))

end MathlibPlus.Open.Analysis.GammaJetBatch
