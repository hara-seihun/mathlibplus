import Mathlib

open scoped BigOperators TensorProduct

namespace MathlibPlus.Open.Research.CICoprimeShellProductsShearSterility

universe u v w

noncomputable section

/-- The increment module attached to a shear and a direction. -/
def incrementModule {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v}
    [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B]
    (s : B → A) (d : B) : Submodule (ZMod p) A :=
  Submodule.span (ZMod p)
    (Set.range (fun x : B => s (x + d) - s x - s d))

def theta {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v}
    [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B]
    (s : B → A) : (A × B) → (A × B) :=
  fun q => (q.1 + s q.2, q.2)

def linearShear {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v}
    [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B]
    (L : B →ₗ[ZMod p] A) : (A × B) → (A × B) :=
  fun q => (q.1 + L q.2, q.2)

/-- Adjacency in an additive binary Cayley relation. -/
def cayleyAdjacency {A : Type u} {B : Type v}
    [AddCommGroup A] [AddCommGroup B]
    (S : Set (A × B)) (x y : A × B) : Prop :=
  y - x ∈ S

def cayleyIsomorphism {A : Type u} {B : Type v}
    [AddCommGroup A] [AddCommGroup B]
    (f : (A × B) → (A × B)) (S T : Set (A × B)) : Prop :=
  Function.Bijective f ∧
    ∀ x y : A × B,
      cayleyAdjacency S x y ↔ cayleyAdjacency T (f x) (f y)

def identityFree {A : Type u} {B : Type v}
    [Zero A] [Zero B] (S : Set (A × B)) : Prop :=
  (0 : A × B) ∉ S

def inverseClosed {A : Type u} {B : Type v}
    [Neg A] [Neg B] (S : Set (A × B)) : Prop :=
  ∀ ⦃s : A × B⦄, s ∈ S → -s ∈ S

/-- Failure of ordinary undirected CI for a finite labelled tuple. -/
def ordinaryUndirectedTupleCIDefect {A : Type u} {B : Type v} {J : Type w}
    [AddCommGroup A] [AddCommGroup B] [Fintype J]
    (S T : J → Set (A × B)) (f : (A × B) → (A × B)) : Prop :=
  (∀ j, identityFree (S j) ∧ inverseClosed (S j)) ∧
    (∀ j, identityFree (T j) ∧ inverseClosed (T j)) ∧
    (∀ j, cayleyIsomorphism f (S j) (T j)) ∧
    ¬ ∃ e : (A × B) ≃+ (A × B),
      ∀ j, e '' S j = T j

/-- The primal solvability condition for the shear chart. -/
def hasLinearShadow {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v}
    [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B]
    (s : B → A) : Prop :=
  ∃ L : B →ₗ[ZMod p] A,
    ∀ d : B, L d - s d ∈ incrementModule (p := p) s d

/-- The full simultaneous sterility statement for one shear. -/
def sterilityCriterion {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v}
    [AddCommGroup A] [Module (ZMod p) A]
    [FiniteDimensional (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B]
    [FiniteDimensional (ZMod p) B]
    (s : B → A) : Prop :=
  ∀ (L : B →ₗ[ZMod p] A),
    (∀ d : B, L d - s d ∈ incrementModule (p := p) s d) →
      (∃ e : (A × B) ≃+ (A × B),
        ∀ q : A × B, e q = linearShear (p := p) L q) ∧
      ∀ (J : Type w) [Fintype J] (S T : J → Set (A × B)),
        (∀ j, cayleyIsomorphism (theta (p := p) s) (S j) (T j)) →
          (∀ j, linearShear (p := p) L '' S j = T j) ∧
          ((∀ j, identityFree (S j) ∧ inverseClosed (S j) ∧
              identityFree (T j) ∧ inverseClosed (T j)) →
            (∃ e : (A × B) ≃+ (A × B),
              (∀ q : A × B, e q = linearShear (p := p) L q) ∧
                ∀ j, e '' S j = T j) ∧
            ¬ ordinaryUndirectedTupleCIDefect S T (theta (p := p) s))

/-- The exact finite dual obstruction to the existence of a linear shadow. -/
def dualObstruction {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v}
    [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B]
    (s : B → A) : Prop :=
  ∃ (m : ℕ) (c : Fin m → Module.Dual (ZMod p) A) (d : Fin m → B),
    (∀ i : Fin m, ∃ k : ZMod p, ∀ x : B,
      c i (s (x + d i) - s x) = k) ∧
    (∑ i : Fin m,
      TensorProduct.tmul (ZMod p) (c i) (d i) = 0) ∧
    (∑ i : Fin m, c i (s (d i)) ≠ 0)

def exactDualObstruction {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v}
    [AddCommGroup A] [Module (ZMod p) A]
    [FiniteDimensional (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B]
    [FiniteDimensional (ZMod p) B]
    (s : B → A) : Prop :=
  hasLinearShadow (p := p) s ↔ ¬ dualObstruction (p := p) s

/-- Uniform sterility when one of the two vector spaces has dimension at most one. -/
def uniformLowDimensionalSterility {p : ℕ} [Fact p.Prime]
    {A : Type u} {B : Type v}
    [AddCommGroup A] [Module (ZMod p) A]
    [FiniteDimensional (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B]
    [FiniteDimensional (ZMod p) B] : Prop :=
  (Module.finrank (ZMod p) A ≤ 1 ∨
      Module.finrank (ZMod p) B ≤ 1) →
    ∀ (s : B → A), s 0 = 0 → hasLinearShadow (p := p) s

/-- The exact binary low-rank and dimension-three boundary. -/
def binaryThreshold : Prop :=
  (∀ (r : ℕ), r ≤ 5 →
    ∀ {A : Type u} {B : Type v}
      [AddCommGroup A] [Module (ZMod 2) A]
      [FiniteDimensional (ZMod 2) A]
      [AddCommGroup B] [Module (ZMod 2) B]
      [FiniteDimensional (ZMod 2) B],
      (A × B ≃ₗ[ZMod 2] (Fin r → ZMod 2)) →
        ∀ (s : B → A), s 0 = 0 → hasLinearShadow (p := 2) s) ∧
  (∀ {A : Type u} {B : Type v}
      [AddCommGroup A] [Module (ZMod 2) A]
      [FiniteDimensional (ZMod 2) A]
      [AddCommGroup B] [Module (ZMod 2) B]
      [FiniteDimensional (ZMod 2) B],
      Module.finrank (ZMod 2) A = 3 →
        Module.finrank (ZMod 2) B = 3 →
          ∃ s : B → A,
            s 0 = 0 ∧ ¬ hasLinearShadow (p := 2) s) ∧
  (∀ (p : ℕ) (hp : p.Prime),
    (p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11) →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ {A : Type u} {B : Type v}
        [AddCommGroup A] [Module (ZMod p) A]
        [FiniteDimensional (ZMod p) A]
        [AddCommGroup B] [Module (ZMod p) B]
        [FiniteDimensional (ZMod p) B],
        Module.finrank (ZMod p) B = 2 →
          ∀ (s : B → A), s 0 = 0 → hasLinearShadow (p := p) s)

/-- The complete admitted sharp sterility criterion and binary threshold. -/
def claim61246 : Prop :=
  ∀ (p : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ {A : Type u} {B : Type v}
      [AddCommGroup A] [Module (ZMod p) A]
      [FiniteDimensional (ZMod p) A]
      [AddCommGroup B] [Module (ZMod p) B]
      [FiniteDimensional (ZMod p) B],
      (∀ (s : B → A), s 0 = 0 → sterilityCriterion.{u, v, w} (p := p) s) ∧
      (∀ (s : B → A), s 0 = 0 → exactDualObstruction.{u, v} (p := p) s) ∧
      uniformLowDimensionalSterility.{u, v} (p := p) (A := A) (B := B) ∧
      binaryThreshold.{u, v}

end
end MathlibPlus.Open.Research.CICoprimeShellProductsShearSterility
