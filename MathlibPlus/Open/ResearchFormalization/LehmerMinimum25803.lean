import MathlibPlus.Open.ResearchFormalization.BoydAffineBatch

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.LehmerMinimum25803

/-- The coefficient vector of a real polynomial in the five correction
coordinates. -/
def coefficientVector (p : Polynomial ℝ) : Fin 5 → ℝ :=
  fun i => p.coeff i.1

def correctionPolynomial (v : Fin 5 → ℝ) : Polynomial ℝ :=
  ∑ i : Fin 5, Polynomial.C (v i) * Polynomial.X ^ i.1

def correctionPolynomialInt (v : Fin 5 → ℤ) : Polynomial ℝ :=
  correctionPolynomial (fun i => (v i : ℝ))

def exteriorRoot (p : Polynomial ℝ) (θ : ℝ) : Prop :=
  1 < θ ∧
    Polynomial.eval θ p = 0 ∧
      ∀ z : ℂ,
        evalRealComplex p z = 0 → 1 < ‖z‖ → z = (θ : ℂ)

/-- The Pisot condition includes the monic irreducible integral carrier and
places every root other than the positive exterior root strictly inside the
unit disk. -/
def pisotPolynomial (p : Polynomial ℤ) : Prop :=
  p.Monic ∧
    Irreducible p ∧
      ∃ θ : ℝ,
        exteriorRoot (p.map (algebraMap ℤ ℝ)) θ ∧
          ∀ z : ℂ,
            evalIntComplex p z = 0 →
              z = (θ : ℂ) ∨ ‖z‖ < 1

def wallPredicate (ell : Polynomial ℝ) (v : Fin 5 → ℝ) : Prop :=
  (∃ u : ℝ,
    -2 < u ∧ u < 2 ∧ u ≠ 0 ∧
      Polynomial.eval u ell = 0 ∧
        Polynomial.eval u (correctionPolynomial v) = 0) ∨
    Polynomial.eval 0
      (ell - (2 : Polynomial ℝ) * correctionPolynomial v) = 0

def connectedComponent (ell : Polynomial ℝ)
    (S : Set (Fin 5 → ℝ)) : Prop :=
  S ⊆ {v | ¬ wallPredicate ell v} ∧
    IsConnected S ∧
      ∀ T : Set (Fin 5 → ℝ),
        S ⊆ T → T ⊆ {v | ¬ wallPredicate ell v} → IsConnected T → T ⊆ S

/-- The chamber predicate does not assume that every member already has the
one-exterior-root conclusion. -/
def pisotBoydChamber
    (ell : Polynomial ℝ) (S : Set (Fin 5 → ℝ)) : Prop :=
  connectedComponent ell S ∧
    ∃ v ∈ S, ∃ q A : Polynomial ℝ, ∃ θ : ℝ,
      affineBoydFormula 5 ell (correctionPolynomial v) q A ∧
        exteriorRoot A θ

def closedSameChamberSublevel
    (ell : Polynomial ℝ) (S : Set (Fin 5 → ℝ))
    (θstar : ℝ) : Set (Fin 5 → ℝ) :=
  {v | v ∈ closure S ∧
    ∃ q A : Polynomial ℝ, ∃ θ : ℝ,
      affineBoydFormula 5 ell (correctionPolynomial v) q A ∧
        exteriorRoot A θ ∧ θ ≤ θstar}

def integerSublevel
    (ell : Polynomial ℝ) (S : Set (Fin 5 → ℝ))
    (θstar : ℝ) : Set (Fin 5 → ℤ) :=
  {v | coefficientVector (correctionPolynomialInt v) ∈
    closedSameChamberSublevel ell S θstar}

def coefficientBox
    (lo hi : Fin 5 → ℤ) : Set (Fin 5 → ℤ) :=
  {v | ∀ i : Fin 5, lo i ≤ v i ∧ v i ≤ hi i}

def rootOrderFunctional
    (v vstar : Fin 5 → ℝ) (x : ℝ) : ℝ :=
  Polynomial.eval x
    (correctionPolynomial v - correctionPolynomial vstar)

def lehmerTrace : Polynomial ℝ :=
  Polynomial.X ^ 5 + Polynomial.X ^ 4 - Polynomial.C 5 * Polynomial.X ^ 3 -
    Polynomial.C 5 * Polynomial.X ^ 2 + Polynomial.C 4 * Polynomial.X +
    Polynomial.C 3

def lehmerCorrection : Polynomial ℝ :=
  Polynomial.X ^ 4 + Polynomial.C 2 * Polynomial.X ^ 3 - Polynomial.X

def lehmerPisot : Polynomial ℤ :=
  Polynomial.X ^ 11 - Polynomial.C 2 * Polynomial.X ^ 9 -
    Polynomial.C 4 * Polynomial.X ^ 8 - Polynomial.C 4 * Polynomial.X ^ 7 -
    Polynomial.C 3 * Polynomial.X ^ 6 - Polynomial.X ^ 5 + Polynomial.X ^ 4 +
    Polynomial.C 3 * Polynomial.X ^ 3 + Polynomial.C 4 * Polynomial.X ^ 2 +
    Polynomial.C 3 * Polynomial.X + Polynomial.C 1

def lehmerLower : Fin 5 → ℤ := ![-1, -2, -4, -3, -1]
def lehmerUpper : Fin 5 → ℤ := ![1, 4, 4, 2, 2]
def lehmerMinimizer : Fin 5 → ℤ := ![0, -1, 0, 2, 1]

/-- Claim 25803: the exact Lehmer chamber box, its 4536 integer candidates,
the root-ordering certificate at the exterior trace, and the unique Pisot
minimum. -/
def claim25803 : Prop :=
  let ell := lehmerTrace
  let cL := lehmerCorrection
  let p := lehmerPisot
  let box := coefficientBox lehmerLower lehmerUpper
  let vstar := lehmerMinimizer
  ∃ S : Set (Fin 5 → ℝ), ∃ qL A_L : Polynomial ℝ, ∃ θL : ℝ,
    (coefficientVector cL ∈ S ∧ pisotBoydChamber ell S) ∧
      affineBoydFormula 5 ell cL qL A_L ∧
          exteriorRoot A_L θL ∧
            p.map (algebraMap ℤ ℝ) = A_L ∧
              coefficientVector cL = (fun i => (vstar i : ℝ)) ∧
                p.Monic ∧ p.natDegree = 11 ∧ pisotPolynomial p ∧
                Set.Finite box ∧ box.ncard = 4536 ∧ vstar ∈ box ∧
                  (∀ v : Fin 5 → ℤ,
                    v ∈ integerSublevel ell S (θL : ℝ) → v ∈ box) ∧
                    (∀ v : Fin 5 → ℤ,
                      v ∈ box →
                        0 ≤ rootOrderFunctional
                          (fun i => (v i : ℝ))
                          (fun i => (vstar i : ℝ))
                          (θL + θL⁻¹) ∧
                          (rootOrderFunctional
                              (fun i => (v i : ℝ))
                              (fun i => (vstar i : ℝ))
                              (θL + θL⁻¹) = 0 ↔ v = vstar)) ∧
                      (∀ v : Fin 5 → ℤ, ∀ θ : ℝ,
                        coefficientVector (correctionPolynomialInt v) ∈ S →
                          (∃ q A : Polynomial ℝ,
                            affineBoydFormula 5 ell
                              (correctionPolynomialInt v) q A ∧
                            exteriorRoot A θ) →
                            θL ≤ θ ∧
                              (θ = θL ↔ v = vstar))

end MathlibPlus.Open.ResearchFormalization.LehmerMinimum25803
