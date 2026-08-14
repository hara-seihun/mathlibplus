import Mathlib

open BigOperators

namespace MathlibPlus.Open

noncomputable section

/-- The path variable used for connected-subtree collar generating polynomials. -/
def pathCollarVariable : Polynomial ℚ := Polynomial.X

/-- The finite q-integer `[n]_q = 1 + q + ⋯ + q^(n-1)`. -/
def pathQInteger (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range n, pathCollarVariable ^ k

/-- Representatives of the root orbits of a path on `m` vertices, indexed from
an endpoint and chosen on one side of path reversal. -/
def PathRootOrbit (m : ℕ) := {r : ℕ // 1 ≤ r ∧ 2 * r ≤ m + 1}

/-- The connected-subtree collar of the root at position `r` on the path with
vertices numbered `1,...,m`; the constant term represents the empty subtree. -/
def connectedSubtreePathCollar (m r : ℕ) : Polynomial ℚ :=
  1 + ∑ l ∈ Finset.Icc 1 r, ∑ u ∈ Finset.Icc r m,
    pathCollarVariable ^ (u - l + 1)

def pathRootOrbitCollar (m : ℕ) (r : PathRootOrbit m) : Polynomial ℚ :=
  connectedSubtreePathCollar m r.1

def pathCrossLeft (m : ℕ) (a b c d : PathRootOrbit m) : Polynomial ℚ :=
  (pathRootOrbitCollar m a - pathRootOrbitCollar m d) *
    (pathRootOrbitCollar m b - pathRootOrbitCollar m c)

def pathCrossRight (m : ℕ) (a b c d : PathRootOrbit m) : Polynomial ℚ :=
  (pathRootOrbitCollar m a - pathRootOrbitCollar m c) *
    (pathRootOrbitCollar m b - pathRootOrbitCollar m d)

def pathCrossDefect (m : ℕ) (a b c d : PathRootOrbit m) : Polynomial ℚ :=
  pathCrossLeft m a b c d - pathCrossRight m a b c d

def pathMatchingAB_CD (m : ℕ) (a b c d : PathRootOrbit m) : Polynomial ℚ :=
  (pathRootOrbitCollar m a - pathRootOrbitCollar m b) *
    (pathRootOrbitCollar m c - pathRootOrbitCollar m d)

def pathMatchingAC_BD (m : ℕ) (a b c d : PathRootOrbit m) : Polynomial ℚ :=
  (pathRootOrbitCollar m a - pathRootOrbitCollar m c) *
    (pathRootOrbitCollar m b - pathRootOrbitCollar m d)

def pathMatchingAD_BC (m : ℕ) (a b c d : PathRootOrbit m) : Polynomial ℚ :=
  (pathRootOrbitCollar m a - pathRootOrbitCollar m d) *
    (pathRootOrbitCollar m b - pathRootOrbitCollar m c)

/-- Claim 24694. -/
def path_root_orbit_connected_subtree_collar : Prop :=
  ∀ (m : ℕ) (r : PathRootOrbit m),
    pathRootOrbitCollar m r =
      1 + pathCollarVariable * pathQInteger r.1 *
        pathQInteger (m - r.1 + 1)

/-- Claim 24695. -/
def nested_prefix_first_difference_formula : Prop :=
  ∀ (m : ℕ) (r s : PathRootOrbit m),
    r.1 < s.1 →
      (∀ k : ℕ, k < r.1 + 1 →
        (pathRootOrbitCollar m r - pathRootOrbitCollar m s).coeff k = 0) ∧
      (pathRootOrbitCollar m r - pathRootOrbitCollar m s).coeff (r.1 + 1) = -1

/-- Claim 24696. -/
def equal_leading_data_for_two_cross_ratio_products : Prop :=
  ∀ (m : ℕ) (a b c d : PathRootOrbit m),
    a.1 < b.1 ∧ b.1 < c.1 ∧ c.1 < d.1 →
      let k := (a.1 + 1) + (b.1 + 1)
      (∀ n : ℕ, n < k →
        (pathCrossLeft m a b c d).coeff n = 0 ∧
        (pathCrossRight m a b c d).coeff n = 0) ∧
      (pathCrossLeft m a b c d).coeff k = 1 ∧
      (pathCrossRight m a b c d).coeff k = 1

/-- Claim 24699. -/
def nonvanishing_of_cross_ratio_defect : Prop :=
  ∀ (m : ℕ) (a b c d : PathRootOrbit m),
    a.1 < b.1 ∧ b.1 < c.1 ∧ c.1 < d.1 →
      pathRootOrbitCollar m a - pathRootOrbitCollar m b ≠ 0 ∧
      pathRootOrbitCollar m d - pathRootOrbitCollar m c ≠ 0 ∧
      (pathRootOrbitCollar m a - pathRootOrbitCollar m b) *
          (pathRootOrbitCollar m d - pathRootOrbitCollar m c) ≠ 0 ∧
      pathCrossDefect m a b c d ≠ 0

/-- Claim 24700. -/
def no_rational_constant_cross_ratio_among_four_path_root_collars : Prop :=
  ∀ (m : ℕ) (a b c d : PathRootOrbit m),
    a.1 < b.1 ∧ b.1 < c.1 ∧ c.1 < d.1 →
      ¬ ∃ lam : ℚ,
        pathCrossLeft m a b c d =
          Polynomial.C lam * pathCrossRight m a b c d

/-- Claim 24701. -/
def affine_independence_of_three_perfect_matching_quadratics : Prop :=
  ∀ (m : ℕ) (a b c d : PathRootOrbit m),
    a.1 < b.1 ∧ b.1 < c.1 ∧ c.1 < d.1 →
      ∀ α β γ : ℚ,
        α + β + γ = 0 →
        Polynomial.C α * pathMatchingAB_CD m a b c d +
            Polynomial.C β * pathMatchingAC_BD m a b c d +
            Polynomial.C γ * pathMatchingAD_BC m a b c d = 0 →
          α = 0 ∧ β = 0 ∧ γ = 0

end

end MathlibPlus.Open
