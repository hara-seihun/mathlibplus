import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch

namespace DirichletCoefficient

/-- Coefficients of a finite Dirichlet multiplier. -/
def finiteMultiplier (a : ℕ → ℝ) (N : ℕ) : ℕ → ℝ :=
  fun d => if d ≤ N then a d else 0

/-- The coefficient contributed by `Q(-L⁻¹ d/ds) ζ(s)` at `n`. -/
noncomputable def differentiatedZetaCoefficient (Q : Polynomial ℝ) (L : ℝ) : ℕ → ℝ :=
  fun n => Q.eval (Real.log (n : ℝ) / L)

/-- Coefficient convolution for a product of formal Dirichlet series. -/
def dirichletProductCoefficient (f g : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ d ∈ Nat.divisors k, f d * g (k / d)

/-- Exact finite-multiplier coefficient identities from Claim 13809. -/
noncomputable def claim13809 : Prop :=
  ∀ (a b : ℕ → ℝ) (N M k : ℕ) (Q : Polynomial ℝ) (L : ℝ),
    dirichletProductCoefficient
        (finiteMultiplier a N) (differentiatedZetaCoefficient Q L) k =
      ∑ d ∈ (Nat.divisors k).filter (fun d => d ≤ N),
        a d * Q.eval (Real.log ((k / d : ℕ) : ℝ) / L) ∧
    dirichletProductCoefficient
        (finiteMultiplier b M) (fun _ => (1 : ℝ)) k =
      ∑ d ∈ (Nat.divisors k).filter (fun d => d ≤ M), b d

end DirichletCoefficient

namespace Polyafrequency

/-- The one-sided Toeplitz matrix of a finite coefficient row. -/
def toeplitzCoefficient {n : ℕ} (a : Fin n → ℝ) (k : ℕ) : ℝ :=
  if h : k < n then a ⟨k, h⟩ else 0

def toeplitzMatrix {n : ℕ} (a : Fin n → ℝ) (i j : ℕ) : ℝ :=
  if h : i ≤ j then toeplitzCoefficient a (j - i) else 0

/-- Total nonnegativity, stated through all finite ordered minors. -/
def totallyNonnegative (M : ℕ → ℕ → ℝ) : Prop :=
  ∀ (r : ℕ) (rows cols : Fin r → ℕ),
    StrictMono rows → StrictMono cols →
      0 ≤ Matrix.det (fun i j => M (rows i) (cols j))

def totallyNonnegativeUpTo (bound : ℕ) (M : ℕ → ℕ → ℝ) : Prop :=
  ∀ (r : ℕ) (rows cols : Fin r → ℕ),
    r ≤ bound → StrictMono rows → StrictMono cols →
      0 ≤ Matrix.det (fun i j => M (rows i) (cols j))

/-- Pólya-frequency and bounded-order Pólya-frequency row predicates. -/
def PF {n : ℕ} (a : Fin n → ℝ) : Prop :=
  totallyNonnegative (toeplitzMatrix a)

def PF_r (bound : ℕ) {n : ℕ} (a : Fin n → ℝ) : Prop :=
  totallyNonnegativeUpTo bound (toeplitzMatrix a)

/-- The row-generating polynomial of a finite nonnegative row. -/
noncomputable def rowGeneratingPolynomial {n : ℕ} (a : Fin n → ℝ) : Polynomial ℝ :=
  ∑ k : Fin n, Polynomial.C (a k) * Polynomial.X ^ (k : ℕ)

/-- Having no zeros except real zeros at nonpositive points. -/
def onlyNonpositiveRealZeros (p : Polynomial ℝ) : Prop :=
  ∀ z : ℂ,
    (Polynomial.map (algebraMap ℝ ℂ) p).eval z = 0 →
      z.im = 0 ∧ z.re ≤ 0

/-- The PF row convention and its finite-row real-zero characterization (Claim 16504). -/
def claim16504 : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ),
    (∀ k, 0 ≤ a k) →
      (PF a ↔ onlyNonpositiveRealZeros (rowGeneratingPolynomial a))

/-- Total nonnegativity of the coefficient array of finite row polynomials. -/
def arrayTotallyNonnegative {n : ℕ} (a : ℕ → Fin n → ℝ) : Prop :=
  ∀ (r : ℕ) (rows : Fin r → ℕ) (cols : Fin r → Fin n),
    StrictMono rows → StrictMono cols →
      0 ≤ Matrix.det (fun i j => a (rows i) (cols j))

/-- Coefficientwise nonnegativity of a real polynomial. -/
def coefficientwiseNonnegative (p : Polynomial ℝ) : Prop :=
  ∀ k : ℕ, 0 ≤ p.coeff k

/-- Coefficientwise total nonnegativity of a Hankel matrix of row polynomials. -/
noncomputable def coefficientwiseHankelTN (A : ℕ → Polynomial ℝ) : Prop :=
  ∀ (r : ℕ) (rows cols : Fin r → ℕ),
    StrictMono rows → StrictMono cols →
      coefficientwiseNonnegative
        (Matrix.det (fun i j => A (rows i + cols j)))

/-- The coefficientwise Hankel-TN convention for `A_n(x)` (Claim 16505). -/
def claim16505 (A : ℕ → Polynomial ℝ) : Prop :=
  coefficientwiseHankelTN A

/-- Array TN and row PF alone do not imply row-polynomial Hankel TN (Claim 16511). -/
noncomputable def claim16511 : Prop :=
  ¬ ∀ (n : ℕ) (a : ℕ → Fin n → ℝ),
      arrayTotallyNonnegative a →
      (∀ i, PF (a i)) →
      coefficientwiseHankelTN (fun i => rowGeneratingPolynomial (a i))

end Polyafrequency

namespace UnionClosedProducts

/-- The union product of two (possibly infinite) set families. -/
def setUnionProduct {α : Type*}
    (A B : Set (Set α)) : Set (Set α) :=
  {s | ∃ a ∈ A, ∃ b ∈ B, s = a ∪ b}

def setFamilyEmptyTotalIntersection {α : Type*}
    (F : Set (Set α)) : Prop :=
  ∀ x : α, ∃ s, s ∈ F ∧ x ∉ s

/-- Nonempty finite intersections of members of a set family. -/
def finiteMeetClosure {α : Type*}
    (P : Set (Set α)) : Set (Set α) :=
  {s | ∃ k : ℕ, ∃ f : Fin (k + 1) → Set α,
    (∀ i, f i ∈ P) ∧ s = {x | ∀ i, x ∈ f i}}

/-- Factors lie in the product's finite meet closure (Claim 21172). -/
def claim21172 : Prop :=
  ∀ {α : Type*} (A B : Set (Set α)),
    A.Nonempty → B.Nonempty →
    setFamilyEmptyTotalIntersection A →
    setFamilyEmptyTotalIntersection B →
    let P := setUnionProduct A B
    (∀ s, s ∈ A → s ∈ finiteMeetClosure P) ∧
      (∀ s, s ∈ B → s ∈ finiteMeetClosure P)

/-- A finite family of finite sets, represented without quotienting its ground set. -/
def unionProduct {α : Type*} [DecidableEq α]
    (A B : Finset (Finset α)) : Finset (Finset α) :=
  A.biUnion (fun a => B.image (fun b => a ∪ b))

def unionClosed {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ ⦃a⦄, a ∈ F → ∀ ⦃b⦄, b ∈ F → a ∪ b ∈ F

def emptyTotalIntersection {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ x : α, ∃ s, s ∈ F ∧ x ∉ s

def admissibleFactor {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  F.Nonempty ∧ (∅ : Finset α) ∉ F ∧ unionClosed F ∧ emptyTotalIntersection F

/-- The asymmetric six-member union-product cap (Claim 21175). -/
def claim21175 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (A B : Finset (Finset α)),
    admissibleFactor A → admissibleFactor B →
    (unionProduct A B).card = 6 →
    12 ≤ min A.card B.card →
    max A.card B.card ≤ 13

/-- Sharpness of the thirteen-member cap (Claim 21177). -/
def claim21177 : Prop :=
  ∃ (n : ℕ) (A B : Finset (Finset (Fin n))),
    admissibleFactor A ∧ admissibleFactor B ∧
    (unionProduct A B).card = 6 ∧ A.card = 12 ∧ B.card = 13

/-- The fourteen-by-twelve exclusion under the six-product hypotheses (Claim 21178). -/
def claim21178 : Prop :=
  ¬ ∃ (n : ℕ) (A B : Finset (Finset (Fin n))),
    admissibleFactor A ∧ admissibleFactor B ∧
    (unionProduct A B).card = 6 ∧
    ((A.card = 14 ∧ 12 ≤ B.card) ∨ (B.card = 14 ∧ 12 ≤ A.card))

end UnionClosedProducts

end MathlibPlus.Open.ResearchFormalizationBatch
