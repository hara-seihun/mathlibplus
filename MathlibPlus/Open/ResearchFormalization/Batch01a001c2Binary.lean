import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Binary

open MeasureTheory

/-- The ordinary uniqueness assertion for an absolutely convergent Dirichlet series. -/
def claim50806 : Prop :=
  ∀ (c : ℕ → ℂ) (σ₀ : ℝ),
    (∀ s : ℂ, σ₀ < s.re →
      Summable (fun n : ℕ =>
        if 2 ≤ n then ‖c n * Complex.cpow (n : ℂ) (-s)‖ else 0)) →
    (∀ s : ℂ, σ₀ < s.re →
      (∑' n : ℕ,
        if 2 ≤ n then c n * Complex.cpow (n : ℂ) (-s) else 0) = 0) →
    ∀ n : ℕ, 2 ≤ n → c n = 0

/-- The changed scalar source has a positive rank-one Gram kernel but fails the
wave second-jet compatibility equality at the displayed point. -/
def claim50815 : Prop :=
  let μ : Measure ℝ := Measure.dirac 0
  let b : ℝ → ℝ → ℝ := fun t _ξ => (1 + t ^ 2)⁻¹
  let K : ℝ → ℝ → ℝ := fun t s => ∫ ξ : ℝ, b t ξ * b s ξ ∂μ
  (0 < μ Set.univ) ∧
    (∀ t s : ℝ, K t s = ((1 + t ^ 2) * (1 + s ^ 2))⁻¹) ∧
    (∀ t : ℝ, 0 < K t t) ∧
    (∀ m : ℕ, ∀ t : Fin m → ℝ, ∀ w : Fin m → ℝ,
      0 ≤ ∑ i : Fin m, ∑ j : Fin m,
        w i * w j * K (t i) (t j)) ∧
    (∀ t s u : ℝ, K t s * K u u = K t u * K u s) ∧
    deriv (fun t : ℝ => deriv (fun u : ℝ => K u 1) t) 0 = -1 ∧
    deriv (fun s : ℝ => deriv (fun u : ℝ => K 0 u) s) 1 = (1 / 2 : ℝ)

abbrev Tower := ℕ → Bool

def x0 : Tower := fun _ => false

def pi_n (n : ℕ) (x : Tower) : Fin n → Bool := fun k => x k

def Bad (x : Tower) : Prop := ∃ k : ℕ, x k = true

def counterfeit (n : ℕ) : Tower := fun k => if k = n then true else false

/-- The finite premise has both a concrete family of bad witnesses and a
concrete unrestricted separator, while it has no coherent bad witness. -/
def claim50824 : Prop :=
  let premise : Prop :=
    ∀ n : ℕ, ∃ y : Tower, Bad y ∧ pi_n n y = pi_n n x0
  let coherent : Prop :=
    ∃ y : Tower, Bad y ∧ ∀ n : ℕ, pi_n n y = pi_n n x0
  let D : Tower → Tower := id
  let accepted : Set Tower := {x0}
  premise ∧ ¬ coherent ∧ D x0 ∈ accepted ∧
    (∀ y : Tower, Bad y → D y ∉ accepted)

/-- Every finite cutoff has a bad counterfeit, but there is no coherent bad
sequence agreeing with the target at every cutoff. -/
def claim50826 : Prop :=
  (∀ n : ℕ,
    Bad (counterfeit n) ∧ pi_n n (counterfeit n) = pi_n n x0) ∧
    ¬ ∃ y : Tower, Bad y ∧
      ∀ n : ℕ, pi_n n y = pi_n n x0

/-- The identity certificate separates the target from every bad sequence,
although the accepted singleton is not open in the product topology. -/
def claim50827 : Prop :=
  let D : Tower → Tower := id
  let accepted : Set Tower := {x0}
  D x0 ∈ accepted ∧
    (∀ y : Tower, Bad y → D y ∉ accepted) ∧
    ¬ IsOpen accepted

/-- Every certificate factoring through a fixed cutoff agrees on the target and
that cutoff's counterfeit. -/
def claim50828 : Prop :=
  ∀ (n : ℕ) (Y : Type*) (F : (Fin n → Bool) → Y),
    (let C : Tower → Y := fun x => F (pi_n n x)
     C (counterfeit n) = C x0)

/-- No continuous certificate with an open accepted region can accept the
zero sequence while rejecting every bad sequence. -/
def claim50830 : Prop :=
  ∀ (Y : Type*) [TopologicalSpace Y] (D : Tower → Y) (U : Set Y),
    Continuous D → IsOpen U → D x0 ∈ U →
      D ⁻¹' U ∩ {x : Tower | Bad x} = ∅ → False

end MathlibPlus.Open.ResearchFormalization.Binary
