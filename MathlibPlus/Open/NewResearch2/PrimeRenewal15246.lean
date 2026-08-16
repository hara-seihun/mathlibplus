import MathlibPlus.Analysis.LogarithmicTranslation

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.NewResearch2.PrimeRenewal15246

noncomputable section

abbrev L2 := Lp ℂ 2 (volume : Measure ℝ)

/-- The actual unitary translation on the canonical complex Lebesgue L² carrier. -/
noncomputable def translationOperator (a : ℝ) : L2 →L[ℂ] L2 :=
  (MathlibPlus.Analysis.LogarithmicTranslation.logarithmicTranslation a).toContinuousLinearEquiv.toContinuousLinearMap

/-- The literal prime Euler face on that carrier. -/
def primeEulerFace (p : ℕ) : L2 →L[ℂ] L2 :=
  ContinuousLinearMap.id ℂ L2 -
    ((Real.rpow (p : ℝ) (- (1 : ℝ) / 2) : ℝ) : ℂ) •
      translationOperator (Real.log (p : ℝ))

/-- The actual Neumann inverse of a literal prime Euler face. -/
noncomputable def primeEulerFaceInverse (p : ℕ) : L2 →L[ℂ] L2 :=
  ∑' r : ℕ,
    ((Real.rpow (p : ℝ) (- (r : ℝ) / 2) : ℝ) : ℂ) •
      translationOperator ((r : ℝ) * Real.log (p : ℝ))

/-- The primes in the natural cutoff `P_x={p | p≤x}`. -/
def primeCutoff (x : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor x + 1)).filter
    (fun p => Nat.Prime p ∧ (p : ℝ) ≤ x)

/-- The finite ordered composition product of the actual prime-face inverses. -/
def operatorProduct (s : Finset ℕ) (F : ℕ → L2 →L[ℂ] L2) : L2 →L[ℂ] L2 :=
  (s.sort (· ≤ ·)).foldl (fun acc p => (F p).comp acc)
    (ContinuousLinearMap.id ℂ L2)

/-- The finite product of the actual prime-face inverses. -/
noncomputable def inverseProduct (x : ℝ) : L2 →L[ℂ] L2 :=
  operatorProduct (primeCutoff x) primeEulerFaceInverse

/-- A finite-subset basis carrier for the exterior factor of the finite
Koszul cube.  Its coefficients are the canonical L² source space. -/
abbrev PrimeIndex (P : Finset ℕ) := {p // p ∈ P}
abbrev KoszulCarrier (P : Finset ℕ) := Finset (PrimeIndex P) → L2

def koszulSign {P : Finset ℕ} (s : Finset (PrimeIndex P)) (p : PrimeIndex P) : ℂ :=
  (-1 : ℂ) ^ (s.filter (fun q => q.1 < p.1)).card

/-- The exterior-wedge Koszul differential with the actual prime faces. -/
def koszulDifferential (P : Finset ℕ) (x : KoszulCarrier P) : KoszulCarrier P :=
  fun s =>
    ∑ p ∈ s,
      koszulSign s p • primeEulerFace p.1 (x (s.erase p))

/-- Contraction by a selected exterior generator, tensored with its actual
Neumann inverse face. -/
noncomputable def koszulHomotopy (P : Finset ℕ) (q : PrimeIndex P)
    (x : KoszulCarrier P) : KoszulCarrier P :=
  fun s =>
    if q ∉ s then
      koszulSign (insert q s) q • primeEulerFaceInverse q.1 (x (insert q s))
    else 0

/-- Explicit contractibility of every finite prime-renewal cube on the exact
source carrier; this is the higher-degree homology alternative in Claim 15246. -/
def finitePrimeKoszulContractible (P : Finset ℕ) : Prop :=
  ∀ (q : PrimeIndex P) (x : KoszulCarrier P),
    ∀ s : Finset (PrimeIndex P),
      koszulDifferential P (koszulHomotopy P q x) s +
          koszulHomotopy P q (koszulDifferential P x) s = x s

/-- Full inverse norm, prime-number-theorem cutoff asymptotic, and the fact
that the divergence is a degree-zero source reconstruction singularity rather
than surviving higher Koszul homology. -/
def claim_15246 : Prop :=
  let N : ℝ → ℝ := fun x => ‖inverseProduct x‖
  (∀ x : ℝ,
      N x = ∏ p ∈ primeCutoff x,
        (1 - Real.rpow (p : ℝ) (- (1 : ℝ) / 2))⁻¹) ∧
    (∃ C X₀ : ℝ,
      0 < C ∧ 1 < X₀ ∧
        ∀ x : ℝ, X₀ ≤ x →
          |Real.log (N x) -
              2 * Real.sqrt x / Real.log x| ≤
            C * Real.sqrt x / Real.log x ^ 2) ∧
    (∀ P : Finset ℕ,
      (∀ p ∈ P, Nat.Prime p) → P.Nonempty →
        finitePrimeKoszulContractible P)

end
end MathlibPlus.Open.NewResearch2.PrimeRenewal15246
