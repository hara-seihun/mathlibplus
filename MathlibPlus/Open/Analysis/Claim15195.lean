import MathlibPlus.Open.Analysis.Claim15188

open scoped BigOperators Matrix

namespace MathlibPlus.Open.Analysis.Claim15195

noncomputable section

open MathlibPlus.Open.Analysis.Claim15188

/-- The active logarithmic-derivative moments of `P`. -/
def activeMoments (P : Polynomial ℝ) : ℕ → ℝ :=
  let Pseries : PowerSeries ℝ := Polynomial.toPowerSeries P
  let invP : PowerSeries ℝ := PowerSeries.inv Pseries
  let Qseries : PowerSeries ℝ :=
    -(PowerSeries.X * PowerSeries.derivative ℝ Pseries * invP)
  fun j => PowerSeries.coeff (j + 1) Qseries

/-- The active update-vector coefficients of `C/P`. -/
def activeUpdateVector (P C : Polynomial ℝ) : ℕ → ℝ :=
  let Pseries : PowerSeries ℝ := Polynomial.toPowerSeries P
  let invP : PowerSeries ℝ := PowerSeries.inv Pseries
  let Vseries : PowerSeries ℝ := Polynomial.toPowerSeries C * invP
  fun j => PowerSeries.coeff j Vseries

def activeHankel (P : Polynomial ℝ) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  hankelSection (activeMoments P) m

def activeUpdatedHankel (P C : Polynomial ℝ) (α : ℝ) (m : ℕ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => activeHankel P m i j +
    α * activeUpdateVector P C i.1 * activeUpdateVector P C j.1

/-- The finite active kernel section `G_m`, not an unconstrained matrix. -/
def activeKernelSection (P C : Polynomial ℝ) (α : ℝ) (m : ℕ) :
    Matrix (Fin m) (Fin m) ℝ :=
  toeplitzSection P m * activeUpdatedHankel P C α m *
    (toeplitzSection P m).transpose

/-- Reverse a degree-`n` polynomial using the source's explicit
`z^n q(z⁻¹)` convention.  No exact natural-degree assertion is built into
this operation. -/
def reverseAt (n : ℕ) (q : Polynomial ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    Polynomial.C (q.coeff i) * Polynomial.X ^ (n - i)

/-- Truncation through coefficient `n`. -/
def truncateAt (n : ℕ) (f : Polynomial ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    Polynomial.C (f.coeff i) * Polynomial.X ^ i

/-- The Euler operator `E=z d/dz` on the polynomial carrier. -/
def eulerOperator (f : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.X * f.derivative

/--
The forced vector Hermite--Padé defect on the active kernel.  The matrix is
instantiated from the admitted `P,C,alpha` kernel, and the coefficient vector
is the positive-leading-block Schur candidate, so neither `K` nor `q_n` is an
unconstrained callback.
-/
def forcedVectorHermitePadeDefectIdentity_claim15195 : Prop :=
  ∀ (n : ℕ) (α : ℝ) (P C : Polynomial ℝ),
    P.coeff 0 ≠ 0 →
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      activeKernelSection P C α (n + 1)
    let K₀ : Matrix (Fin n) (Fin n) ℝ :=
      fun i j => K i.castSucc j.castSucc
    let b : Fin n → ℝ := fun i => K i.castSucc (Fin.last n)
    let c : ℝ := K (Fin.last n) (Fin.last n)
    ∀ hK : K₀.PosDef,
      letI := hK.isUnit.invertible
      let qv : Fin (n + 1) → ℝ :=
        Fin.lastCases (1 : ℝ)
          (fun i : Fin n => -(K₀⁻¹ *ᵥ b) i)
      let p : ℝ := c - b ⬝ᵥ (K₀⁻¹ *ᵥ b)
      let q : Polynomial ℝ :=
        ∑ i : Fin (n + 1),
          Polynomial.C (qv i) * Polynomial.X ^ i.1
      let Hn : Polynomial ℝ := reverseAt n q
      let A_P : Polynomial ℝ := truncateAt n (Hn * P)
      let A_EP : Polynomial ℝ :=
        truncateAt n (Hn * eulerOperator P)
      let A_C : Polynomial ℝ := truncateAt n (Hn * C)
      let σC : ℝ := A_C.coeff n
      let S : Polynomial ℝ :=
        P * A_EP - eulerOperator P * A_P +
          (α * σC) • (Polynomial.X ^ (n + 1) * C)
      q.Monic ∧
        q.natDegree = n ∧
        (∀ i : Fin (n + 1),
          S.coeff (n + 1 + i.1) = (K *ᵥ qv) i) ∧
        (∀ i : Fin n, (K *ᵥ qv) i.castSucc = 0) ∧
        (K *ᵥ qv) (Fin.last n) = p ∧
        (∃ R : Polynomial ℝ,
          S = Polynomial.C p * Polynomial.X ^ (2 * n + 1) +
            Polynomial.X ^ (2 * n + 2) * R) ∧
        S.coeff (2 * n + 1) = p

end

end MathlibPlus.Open.Analysis.Claim15195
