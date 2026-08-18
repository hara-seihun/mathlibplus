import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0083Sawtooth

noncomputable section

/-- The positive-cell Mellin amplitude used by the sawtooth claims. -/
def cellAmplitude (n : ℕ) (p : ℝ) : ℝ :=
  ∫ x : ℝ in (0 : ℝ)..1,
    x * ((n : ℝ) + x) ^ (-p - 1 : ℝ)

/-- The matrix of amplitudes at selected cells and parameters. -/
def cellMatrix (r : ℕ) (ns : Fin r → ℕ) (ps : Fin r → ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun i j => cellAmplitude (ns i) (ps j)

/-- Positive strictly ordered cell and parameter sequences. -/
def orderedPositiveCells (r : ℕ) (ns : Fin r → ℕ) : Prop :=
  (∀ i : Fin r, 0 < ns i) ∧ StrictMono ns

def orderedPositiveParameters (r : ℕ) (ps : Fin r → ℝ) : Prop :=
  (∀ i : Fin r, 0 < ps i) ∧ StrictMono ps

/-- Claim 17785: all ordered positive-cell minors have the prescribed sign. -/
def claim17785_allOrderStrictSignRegularity : Prop :=
  ∀ (r : ℕ), 1 ≤ r →
    ∀ (ns : Fin r → ℕ) (ps : Fin r → ℝ),
      orderedPositiveCells r ns →
      orderedPositiveParameters r ps →
      (-1 : ℝ) ^ (r * (r - 1) / 2) *
          Matrix.det (cellMatrix r ns ps) > 0

/-- Claim 17786: the same sign applies to arbitrary, not only consecutive,
positive strictly ordered selected cells. -/
def claim17786_nonconsecutiveMinorsIncluded : Prop :=
  ∀ (r : ℕ), 1 ≤ r →
    ∀ (ns : Fin r → ℕ) (ps : Fin r → ℝ),
      orderedPositiveCells r ns →
      orderedPositiveParameters r ps →
      (-1 : ℝ) ^ (r * (r - 1) / 2) *
          Matrix.det (cellMatrix r ns ps) > 0

/-- The reciprocal two-coordinate cell vector. -/
def reciprocalVector (p : ℝ) (n : ℕ) : ℝ × ℝ :=
  (cellAmplitude n (1 - p), cellAmplitude n p)

/-- The oriented wedge of two reciprocal cell vectors. -/
def wedge (u v : ℝ × ℝ) : ℝ :=
  u.1 * v.2 - u.2 * v.1

/-- Claim 17788: the reciprocal vectors have positive orientation. -/
def claim17788_reciprocalTwoVectorOrientation : Prop :=
  ∀ (p : ℝ), 0 < p → p < 1 / 2 →
    ∀ (n m : ℕ), 0 < n → n < m →
      wedge (reciprocalVector p n) (reciprocalVector p m) > 0

/-- Partial sums beginning with the empty sum at index zero. -/
def partialSum (p : ℝ) (N : ℕ) : ℝ × ℝ :=
  ∑ n ∈ Finset.Icc 1 N, reciprocalVector p n

/-- A strict turning path has every successive cell vector as an edge and
has positive wedges for every pair of edges in path order. -/
def strictTurningPath (p : ℝ) : Prop :=
  (∀ N : ℕ,
    partialSum p (N + 1) - partialSum p N = reciprocalVector p (N + 1)) ∧
  (∀ n m : ℕ, n < m →
    wedge (partialSum p (n + 1) - partialSum p n)
      (partialSum p (m + 1) - partialSum p m) > 0)

/-- Claim 17790: positive pairwise wedges of all reciprocal cell vectors
imply the strictly turning polygonal path of their partial sums. -/
def claim17790_partialSumsStrictTurning : Prop :=
  ∀ (p : ℝ), 0 < p → p < 1 / 2 →
    (∀ (n m : ℕ), 0 < n → n < m →
      wedge (reciprocalVector p n) (reciprocalVector p m) > 0) →
    strictTurningPath p

end

end MathlibPlus.Open.ResearchFormalization.R0083Sawtooth
