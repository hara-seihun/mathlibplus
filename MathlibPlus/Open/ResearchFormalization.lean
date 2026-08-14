import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

private def factorialKernel (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (Nat.factorial ((i : ℕ) + (j : ℕ)) : ℝ)⁻¹

private def diagonalScaling (x : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i = j then x ^ (i : ℕ) else 0

private def jumpAtom (x : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => x ^ ((i : ℕ) + (j : ℕ) + 1) /
    (Nat.factorial ((i : ℕ) + (j : ℕ)) : ℝ)

/-- Claim 17564: the positive jump-atom matrix is the stated diagonal
congruence of the finite factorial kernel. -/
def factorial_jump_atom_congruence_17564 : Prop :=
  ∀ (x : ℝ), 0 < x → ∀ N : ℕ,
    jumpAtom x N = x • (diagonalScaling x N * factorialKernel N * diagonalScaling x N)

private def matrixForm (n : ℕ) (D : Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  ∑ i, x i * ∑ j, D i j * y j

private def doubledForm (n : ℕ) (D : Matrix (Fin n) (Fin n) ℝ)
    (p q : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  matrixForm n D p.1 q.1 - matrixForm n D p.2 q.2

private def graph (n : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | ∀ i, p.2 i = ∑ j, U i j * p.1 j}

private def isotropic (n : ℕ) (D : Matrix (Fin n) (Fin n) ℝ)
    (L : Set ((Fin n → ℝ) × (Fin n → ℝ))) : Prop :=
  ∀ ⦃p q⦄, p ∈ L → q ∈ L → doubledForm n D p q = 0

private def lagrangian (n : ℕ) (D : Matrix (Fin n) (Fin n) ℝ)
    (L : Set ((Fin n → ℝ) × (Fin n → ℝ))) : Prop :=
  isotropic n D L ∧
    ∀ M : Set ((Fin n → ℝ) × (Fin n → ℝ)),
      isotropic n D M → L ⊆ M → M ⊆ L

/-- Claim 17568: the graph of a D-isometry is maximal isotropic for
D ⊕ (-D). -/
def krein_isometry_graph_is_lagrangian_17568 : Prop :=
  ∀ (n : ℕ) (D U : Matrix (Fin n) (Fin n) ℝ),
    (∀ i j, D i j = D j i) →
    D.det ≠ 0 →
    U.transpose * D * U = D →
    lagrangian n D (graph n U)

private def contiguousMinor {R : Type} [CommRing R]
    (A : Matrix ℕ ℕ R) (N a b : ℕ) : R :=
  Matrix.det (fun i j : Fin N => A (a + (i : ℕ)) (b + (j : ℕ)))

private def maslovMatrix (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ 2 * a * b ^ 2 / (a ^ 2 * b ^ 2 + 4),
      -a * b * (a * b + 2) / (a ^ 2 * b ^ 2 + 4);
      -a * b * (a * b + 2) / (a ^ 2 * b ^ 2 + 4),
      2 * a ^ 2 * b / (a ^ 2 * b ^ 2 + 4) ]

/-- Claim 17595: the displayed Maslov form has Lorentz--Maslov norm
exactly equal to the squared transmission parameter. -/
def lorentz_maslov_norm_17595 : Prop :=
  ∀ (a b : ℝ) (ρ : ℝ) (τ : ℝ),
    0 < ρ → |τ| < 1 →
    (a * b) ^ 2 = ρ + ρ⁻¹ - 2 ∧
      ρ + ρ⁻¹ - 2 = 4 * τ ^ 2 / (1 - τ ^ 2) →
    -Matrix.det (maslovMatrix a b) = τ ^ 2

/-- Claim 17614: Desnanot--Jacobi for contiguous minors. -/
def desnanot_jacobi_contiguous_minors_17614 : Prop :=
  ∀ {R : Type} [CommRing R] (A : Matrix ℕ ℕ R) (N a b : ℕ),
    2 ≤ N →
      contiguousMinor A N a b * contiguousMinor A (N - 2) (a + 1) (b + 1) =
        contiguousMinor A (N - 1) a b * contiguousMinor A (N - 1) (a + 1) (b + 1) -
          contiguousMinor A (N - 1) (a + 1) b * contiguousMinor A (N - 1) a (b + 1)

end

end MathlibPlus.Open.ResearchFormalization
