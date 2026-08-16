import MathlibPlus.Open.Analysis.Claim15188

open scoped BigOperators Matrix

namespace MathlibPlus.Open.Analysis.Claim15192

noncomputable section

open MathlibPlus.Open.Analysis.Claim15188

/-- The coefficient sequence of `Q=-zP'/P`, with the index shifted so that
`mu j` is the coefficient of `z^(j+1)` in `Q`. -/
def activeMoments (P : Polynomial ℝ) : ℕ → ℝ :=
  let Pseries : PowerSeries ℝ := Polynomial.toPowerSeries P
  let invP : PowerSeries ℝ := PowerSeries.inv Pseries
  let Qseries : PowerSeries ℝ :=
    -(PowerSeries.X * PowerSeries.derivative ℝ Pseries * invP)
  fun j => PowerSeries.coeff (j + 1) Qseries

/-- The coefficient sequence of `V=C/P`. -/
def activeUpdateVector (P C : Polynomial ℝ) : ℕ → ℝ :=
  let Pseries : PowerSeries ℝ := Polynomial.toPowerSeries P
  let invP : PowerSeries ℝ := PowerSeries.inv Pseries
  let Vseries : PowerSeries ℝ := Polynomial.toPowerSeries C * invP
  fun j => PowerSeries.coeff j Vseries

/-- The scalar Hankel section and its rank-one update on the active carrier. -/
def activeHankel (P : Polynomial ℝ) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  hankelSection (activeMoments P) m

def activeUpdatedHankel (P C : Polynomial ℝ) (α : ℝ) (m : ℕ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => activeHankel P m i j +
    α * activeUpdateVector P C i.1 * activeUpdateVector P C j.1

/-- The lower-triangular Toeplitz congruence for the two active sections. -/
def activeNumeratorSection (P : Polynomial ℝ) (m : ℕ) :
    Matrix (Fin m) (Fin m) ℝ :=
  toeplitzSection P m * activeHankel P m * (toeplitzSection P m).transpose

def activeKernelSection (P C : Polynomial ℝ) (α : ℝ) (m : ℕ) :
    Matrix (Fin m) (Fin m) ℝ :=
  toeplitzSection P m * activeUpdatedHankel P C α m *
    (toeplitzSection P m).transpose

/--
The completed-defect determinant bridge on the actual `P,C,alpha` carrier.
In particular, `r` is defined from the Uvarov `eta` ratio and the conclusion
also records the exact bridge `r_n=e_n/e_(n+1)`; the latter is not hidden in a
mere beta-conditional consequence.
-/
def completedDefectDeterminantBridge_claim15192 : Prop :=
  ∀ (α : ℝ) (P C : Polynomial ℝ) (h : ℕ → ℝ)
    (π : ℕ → Polynomial ℝ) (β : ℕ → ℝ),
    P.coeff 0 ≠ 0 →
    (∀ k : ℕ,
      (π k).Monic ∧
        (π k).natDegree = k ∧
        Matrix.det (activeHankel P (k + 1)) ≠ 0 ∧
        h k ≠ 0 ∧
        activeHankel P (k + 1) *ᵥ
            coefficientVector (k + 1) (π k) = terminalVector k (h k)) →
    (∀ k : ℕ,
      Matrix.det (activeUpdatedHankel P C α k) ≠ 0 ∧
        Matrix.det (activeNumeratorSection P k) ≠ 0 ∧
        Matrix.det (activeKernelSection P C α k) ≠ 0) →
    let v : ℕ → ℝ := activeUpdateVector P C
    let η : ℕ → ℝ := uvarovEta α v h π
    let e : ℕ → ℝ := fun k =>
      Matrix.det (activeNumeratorSection P k) /
        Matrix.det (activeKernelSection P C α k)
    let r : ℕ → ℝ := fun k => η (k + 1) / η k
    (∀ k : ℕ, η k ≠ 0) →
    (∀ k : ℕ,
      η k = Matrix.det (activeUpdatedHankel P C α k) /
          Matrix.det (activeHankel P k) ∧
        η k = Matrix.det (activeKernelSection P C α k) /
          Matrix.det (activeNumeratorSection P k) ∧
        η k = 1 / e k ∧
        r k = e k / e (k + 1)) ∧
      ((∀ k : ℕ, e (k + 1) / e k = 1 - β k ^ 2) →
        (∀ k : ℕ, r k = 1 / (1 - β k ^ 2)) ∧
        (∀ k : ℕ, 1 ≤ k →
          r k / r (k - 1) =
            (1 - β (k - 1) ^ 2) / (1 - β k ^ 2)))

end

end MathlibPlus.Open.Analysis.Claim15192
