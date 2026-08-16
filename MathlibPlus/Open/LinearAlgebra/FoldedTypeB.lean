import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.LinearAlgebra.FoldedTypeB

private def foldSign (e : Fin 2) : ℝ :=
  if e = 0 then 1 else -1

/-- Claim 4933: a chamber sign is one of the two signs, and signed kernel
entries use the corresponding centered node. -/
def claim4933 (r : ℕ)
    (K : ℕ → ℝ → ℝ) (i : ℕ) (c : ℝ)
    (z : Fin r → ℝ) (ε : Fin r → Fin 2)
    (signed : Fin r → ℝ) : Prop :=
  (∀ j : Fin r, ε j = 0 ∨ ε j = 1) ∧
    (∀ j : Fin r,
      signed j = K i (c + foldSign (ε j) * z j))

/-- Claim 4934: signed and folded cell matrices collect the two displayed
entry types, and their determinants are the two corresponding chirotopes. -/
def claim4934 (r : ℕ)
    (K : ℕ → ℝ → ℝ) (n : Fin r → ℕ) (c : ℝ)
    (z : Fin r → ℝ) (ε : Fin r → Fin 2)
    (signed folded : Matrix (Fin r) (Fin r) ℝ)
    (signedChirotope foldedChirotope : ℝ) : Prop :=
  (∀ j : Fin r, ε j = 0 ∨ ε j = 1) ∧
    (∀ i j : Fin r,
      signed i j = K (n i) (c + foldSign (ε j) * z j)) ∧
    (∀ i j : Fin r,
      folded i j = K (n i) (c + z j) + K (n i) (c - z j)) ∧
    signedChirotope = Matrix.det signed ∧
    foldedChirotope = Matrix.det folded

/-- Claim 4936: determinant multilinearity expands the folded determinant over
all type-B sign chambers. -/
def claim4936 (r : ℕ)
    (K : ℕ → ℝ → ℝ) (n : Fin r → ℕ)
    (c : ℝ) (z : Fin r → ℝ) : Prop :=
  Matrix.det (fun i j : Fin r ↦
      K (n i) (c + z j) + K (n i) (c - z j)) =
    ∑ ε : Fin r → Fin 2,
      Matrix.det (fun i j : Fin r ↦
        K (n i) (c + foldSign (ε j) * z j))

/-- Claim 4938: changing one node sign leaves every folded entry and the
folded-cell determinant unchanged. -/
def claim4938 (r : ℕ)
    (K : ℕ → ℝ → ℝ) (n : Fin r → ℕ)
    (c : ℝ) (z : Fin r → ℝ) (j₀ : Fin r) : Prop :=
  let z' : Fin r → ℝ := fun j ↦ if j = j₀ then -z j else z j
  (∀ i j : Fin r,
    K (n i) (c + z' j) + K (n i) (c - z' j) =
      K (n i) (c + z j) + K (n i) (c - z j)) ∧
    Matrix.det (fun i j : Fin r ↦
      K (n i) (c + z' j) + K (n i) (c - z' j)) =
      Matrix.det (fun i j : Fin r ↦
        K (n i) (c + z j) + K (n i) (c - z j))

/-- Claim 4941: normalized even jets select orders `2j`; the coefficient
minor uses factorial-normalized coefficients, while the analytic interpretation
uses the displayed derivative values and asserts no convergence between them. -/
def claim4941 (r : ℕ)
    (K : ℕ → ℝ → ℝ) (n : Fin r → ℕ) (c : ℝ)
    (j : Fin r → ℕ) (P : Fin r → Polynomial ℝ)
    (coefficient analytic : Matrix (Fin r) (Fin r) ℝ)
    (minor : ℝ) : Prop :=
  (∀ i k : Fin r,
    coefficient i k = (P i).coeff (2 * j k)) ∧
    (∀ i k : Fin r,
      analytic i k =
        iteratedDeriv (2 * j k) (fun x : ℝ ↦ K (n i) x) c /
          (Nat.factorial (2 * j k) : ℝ)) ∧
    minor = Matrix.det coefficient

/-- Claim 4944: folding a centered polynomial kills odd coefficients and
 doubles every even coefficient. -/
def claim4944 (P Q : Polynomial ℝ) : Prop :=
  (∀ x : ℝ,
    Polynomial.eval x Q = Polynomial.eval x P + Polynomial.eval (-x) P) →
    (∀ d : ℕ,
      Q.coeff d = (1 + (-1 : ℝ) ^ d) * P.coeff d) ∧
    (∀ d : ℕ, Odd d → Q.coeff d = 0) ∧
    (∀ j : ℕ, Q.coeff (2 * j) = 2 * P.coeff (2 * j))

end MathlibPlus.Open.LinearAlgebra.FoldedTypeB
