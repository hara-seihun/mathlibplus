import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- The rising-factorial coefficient appearing in the reflected Laguerre rows. -/
def risingFactorial (x : ℝ) (m : ℕ) : ℝ :=
  Finset.prod (Finset.range m) (fun t => x + (t : ℝ))

/-- The reflected row polynomial from the admitted Laguerre expansion. -/
noncomputable def reflectedRow (i : ℕ) : Polynomial ℝ :=
  Finset.sum (Finset.range (i + 2)) (fun k =>
    Polynomial.C
      ((Nat.choose (i + 1) k : ℝ) *
        risingFactorial (((i + k : ℕ) : ℝ) + (3 / 2 : ℝ)) (i + 1 - k)) *
      Polynomial.X ^ (i + k))

/-- The reflected coefficient matrix on an increasing list of degree columns. -/
noncomputable def reflectedCoefficientMatrix (r : ℕ) (n : Fin r → ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => (reflectedRow i.1).coeff (n j)

/-- A finite set of increasing columns supporting a nonzero maximal minor. -/
def nonzeroMaximalMinorSupport (r : ℕ) (s : Finset ℕ) : Prop :=
  ∃ n : Fin r → ℕ,
    StrictMono n ∧
      Finset.univ.image n = s ∧
        Matrix.det (reflectedCoefficientMatrix r n) ≠ 0

/-- Partitions contained in the staircase δᵣ = (r,r-1,…,1), with zero parts allowed. -/
def isStaircasePartition (r : ℕ) (part : Fin r → Fin (r + 1)) : Prop :=
  Antitone (fun i => (part i).1) ∧ ∀ i, (part i).1 ≤ r - i.1

/-- The degree nⱼ = j + λ_{r-j}, using zero-based `Fin` indices. -/
def staircaseDegree (r : ℕ) (part : Fin r → Fin (r + 1)) (j : Fin r) : ℕ :=
  j.1 + (part (Fin.rev j)).1

/-- The Catalan number Cₙ. -/
def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- The finite collection of all staircase partitions of length `r`. -/
noncomputable def staircasePartitions (r : ℕ) : Finset (Fin r → Fin (r + 1)) := by
  classical
  exact Finset.univ.filter (fun part => isStaircasePartition r part)

/-- Staircase indexing, exact nonzero-minor support, and Catalan enumeration. -/
def staircaseIndexingAndCatalanSupport : Prop :=
  ∀ r : ℕ,
    ({s : Finset ℕ | nonzeroMaximalMinorSupport r s} =
        {s : Finset ℕ |
          ∃ part : Fin r → Fin (r + 1),
            isStaircasePartition r part ∧
              s = Finset.univ.image (staircaseDegree r part)}) ∧
      Finset.card (staircasePartitions r) = catalanNumber (r + 1)

end MathlibPlus.Open.Combinatorics
