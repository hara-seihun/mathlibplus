import MathlibPlus.NumberTheory.CompletedZetaRadial

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.CompletedTheta11882

noncomputable section

open MathlibPlus.NumberTheory.CompletedZetaRadial

/-- The completed-xi even jet used by the completed-theta moments. -/
def completedXiEvenJet (h : ℕ → ℝ) : Prop :=
  ∀ x : ℂ,
    riemannXi ((1 / 2 : ℂ) + x) =
      ∑' j : ℕ, (h j : ℂ) * x ^ (2 * j)

/-- The moment recurrence with an explicit initial value. -/
def thetaMomentSequence (h : ℕ → ℝ) (t0 : ℝ) : ℕ → ℝ
  | 0 => t0
  | j + 1 => 4 * (thetaMomentSequence h t0 j - h (j + 1))

/-- The signed moment sequence in the checkerboard bulk. -/
def checkerboardMoments (h : ℕ → ℝ) (t0 : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * thetaMomentSequence h t0 j

/-- The completed-theta Bezout core, with the literal negative-index rule and
all inequalities in the source summation. -/
def completedThetaBezoutEntry (c : ℕ → ℝ) (i j : ℤ) : ℝ :=
  if i < 0 ∨ j < 0 then
    0
  else
    -∑ ell ∈ Finset.range (i.toNat + j.toNat + 2),
      ∑ r ∈ Finset.range (i.toNat + j.toNat + 2),
        if 0 ≤ ell ∧ ell < r ∧
            ell + r = i.toNat + j.toNat + 1 ∧
            ell ≤ i.toNat ∧ ell ≤ j.toNat ∧
            i.toNat < r ∧ j.toNat < r then
          (r - ell : ℝ) * c ell * c r
        else 0

/-- The checkerboard completed-theta bulk entry. -/
def checkerboardBulkEntry (h : ℕ → ℝ) (t0 : ℝ) (i j : ℕ) : ℝ :=
  (-1 : ℝ) ^ (i + j) *
    ((((i + j + 1 : ℕ) : ℝ) / 2) *
        (checkerboardMoments h t0 (i + j) +
          (1 / 4 : ℝ) * checkerboardMoments h t0 (i + j + 1)) +
      (1 / 16 : ℝ) *
        completedThetaBezoutEntry (checkerboardMoments h t0) (i : ℤ) (j : ℤ) +
      (1 / 4 : ℝ) *
        completedThetaBezoutEntry (checkerboardMoments h t0)
          ((i : ℤ) - 1) (j : ℤ) +
      (1 / 4 : ℝ) *
        completedThetaBezoutEntry (checkerboardMoments h t0)
          (i : ℤ) ((j : ℤ) - 1) +
      completedThetaBezoutEntry (checkerboardMoments h t0)
        ((i : ℤ) - 1) ((j : ℤ) - 1))

/-- The order-`N` checkerboard bulk as a family in the initial moment `t0`. -/
def checkerboardBulk (h : ℕ → ℝ) (t0 : ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => checkerboardBulkEntry h t0 i.1 j.1

/-- The exact central-difference realization of the primitive `t0` derivative. -/
def primitiveT0Derivative (h : ℕ → ℝ) (t0 : ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    (checkerboardBulk h (t0 + 1) N i j - checkerboardBulk h (t0 - 1) N i j) / 2

/-- The leading principal block of an order `n+1` bulk. -/
def leadingCheckerboardBlock {n : ℕ}
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => K i.castSucc j.castSucc

/-- The monic first `n` normal equations. -/
def monicNormalEquations {n : ℕ}
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : Fin (n + 1) → ℝ) : Prop :=
  q (Fin.last n) = 1 ∧
    ∀ i : Fin n, (Matrix.mulVec K q) i.castSucc = 0

/-- The quadratic primitive response attached to a monic vector. -/
def primitiveResponse (h : ℕ → ℝ) (t0 : ℝ) {n : ℕ}
    (q : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1),
    q i * (Matrix.mulVec (primitiveT0Derivative h t0 (n + 1)) q) i

/-- Monic extremal uniqueness and the exact primitive-response definition. -/
def monicExtremalAndPrimitiveResponse : Prop :=
  ∀ (h : ℕ → ℝ), completedXiEvenJet h →
    let t0 := 2 - 4 * h 0
    ∀ n : ℕ,
      Matrix.det
          (leadingCheckerboardBlock (checkerboardBulk h t0 (n + 1))) ≠ 0 →
        ∃ q : Fin (n + 1) → ℝ, ∃ dN : ℝ,
          monicNormalEquations (checkerboardBulk h t0 (n + 1)) q ∧
          (∀ q' : Fin (n + 1) → ℝ,
            monicNormalEquations (checkerboardBulk h t0 (n + 1)) q' →
              q' = q) ∧
          dN = primitiveResponse h t0 q

end

end MathlibPlus.Open.ResearchFormalization.CompletedTheta11882
