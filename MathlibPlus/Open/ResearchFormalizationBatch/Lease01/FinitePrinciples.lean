import Mathlib

open scoped BigOperators

noncomputable section
namespace MathlibPlus.Open.ResearchFormalizationBatch.FinitePrinciples

/-- A local relation test on representatives propagates to all translates. -/
def claim59430 : Prop :=
  ∀ (G X Y I : Type*) [Group G] [MulAction G X] [MulAction G Y]
    (f : X → Y) (R : I → X → X → Prop) (S : I → Y → Y → Prop)
    (A Q : Set X),
    (∀ (g : G) (x : X), f (g • x) = g • f x) →
    (∀ (i : I) (g : G) (x z : X),
      R i (g • x) (g • z) ↔ R i x z) →
    (∀ (i : I) (g : G) (y z : Y),
      S i (g • y) (g • z) ↔ S i y z) →
    (∀ x : X, x ∈ A → ∃ g : G, ∃ q : X, q ∈ Q ∧ g • q = x) →
    (∀ (i : I) (q z : X), q ∈ Q →
      (R i q z ↔ S i (f q) (f z))) →
    ∀ (i : I) (x z : X), x ∈ A →
      (R i x z ↔ S i (f x) (f z))

/-- Transport of invariant relation families from one stabilizer transversal. -/
def claim59710 : Prop :=
  ∀ (R T Ω I : Type*) [Group R] [Group T]
    [MulAction R Ω] [MulAction T Ω]
    (θ : R ≃* T) (U : Ω ≃ Ω)
    (P Q : I → Ω → Ω → Prop) (b : Ω) (A : Set Ω),
    (∀ (r : R) (x : Ω), U (r • x) = θ r • U x) →
    (∀ (i : I) (r : R) (x y : Ω),
      P i (r • x) (r • y) ↔ P i x y) →
    (∀ (i : I) (t : T) (x y : Ω),
      Q i (t • x) (t • y) ↔ Q i x y) →
    (∀ y : Ω, ∃ r : R, r • b = y) →
    (∀ y : Ω, ∃ r : R, ∃ q : Ω,
      r • b = b ∧ q ∈ A ∧ r • q = y) →
    ((∀ (i : I) (x y : Ω),
        P i x y ↔ Q i (U x) (U y)) ↔
      (∀ (i : I) (q : Ω), q ∈ A →
        P i b q ↔ Q i (U b) (U q)))

/-- The finite row/column mass-gap criterion. -/
def claim59435 : Prop :=
  ∀ (N P : Type*) [Fintype N] [Fintype P]
    (a : N → ℝ) (b : P → ℝ) (T : N → P → ℝ),
    (∀ i : N, ∑ j : P, T i j = 1) →
    (∀ j : P, ∑ i : N, T i j * a i ≤ b j) →
    ((∃ j : P, ∑ i : N, T i j * a i < b j) ↔
      (∑ i : N, a i < ∑ j : P, b j))

/-- Conjugacy of subgroups of order p^5, with the stated divisibility gate. -/
def subgroupConjugate {G : Type*} [Group G]
    (R T : Subgroup G) : Prop :=
  ∃ g : G, ∀ x : G, x ∈ T ↔ g * x * g⁻¹ ∈ R

def claim59438 : Prop :=
  ∀ (p : ℕ) (G : Type*) [Group G] [Fintype G],
    Nat.Prime p →
      ((∀ R T : Subgroup G,
          Nat.card R = p ^ 5 →
          Nat.card T = p ^ 5 →
          ¬ subgroupConjugate R T →
          p ^ 6 ∣ Nat.card G) ∧
       (¬(p ^ 6 ∣ Nat.card G) →
          ∀ R T : Subgroup G,
            Nat.card R = p ^ 5 →
            Nat.card T = p ^ 5 →
            subgroupConjugate R T))

/-- The support-separated wall obstruction. -/
def wallObstruction {I : Type*} (re im : I → ℝ) (m : I → ℤ)
    (partner : I → I) (T : ℝ) (i : I) : ℤ :=
  if (1 / 2 : ℝ) < re i ∧ |im i| < T then m i else 0

def claim59437 : Prop :=
  ∀ (I : Type*) (re im : I → ℝ) (m : I → ℤ) (partner : I → I),
    (∀ i : I, 0 < m i) →
    (∀ i : I, re (partner i) = 1 - re i) →
    (∀ T : ℝ, 0 < T → ∀ i : I, wallObstruction re im m partner T i = 0) →
    ∀ i : I, re i = 1 / 2

/-- Reflection reversal and filling force two-torsion, including the sharp example. -/
def claim59441 : Prop :=
  (∀ (G : Type*) [AddCommGroup G] (H Hᵣ : G),
    Hᵣ = -H → Hᵣ = H →
      2 • H = 0 ∧
      (∀ (r : ℝ) (a : ℝ → G),
        (∀ x : ℝ, a x = 0 ↔ x = 0) →
        (∀ x : G, 2 • x = 0 → x = 0) →
        H = a (2 * r - 1) →
        r = 1 / 2)) ∧
  (∃ (H Hᵣ : ZMod 2),
    H = 1 ∧ Hᵣ = 1 ∧ H ≠ 0 ∧ Hᵣ = -H ∧ Hᵣ = H)

/-- Arbitrary prescribed side patterns for exponentially close affine roots. -/
def claim59444 : Prop :=
  ∀ (σ : ℕ → ℝ),
    (∀ n : ℕ, σ n = -1 ∨ σ n = 1) →
    ∃ (r : ℕ → ℝ),
      ∀ n : ℕ,
        (∀ x : ℝ,
          x - (1 / 2 + σ n * Real.exp (-3 * (n : ℝ) / 2)) = 0 ↔
            x = r n) ∧
        |r n - 1 / 2| = Real.exp (-3 * (n : ℝ) / 2) ∧
        (σ n = 1 → 1 / 2 < r n) ∧
        (σ n = -1 → r n < 1 / 2)

/-- The exponentially decaying shell tail. -/
def claim59445 : Prop :=
  ∀ (a : ℕ → ℝ) (B : ℝ) (M : ℕ),
    0 ≤ B → 1 ≤ M →
    (∀ k : ℕ,
      |a (M + k)| ≤ B * Real.exp (-Real.pi * (M + k : ℝ) ^ 2)) →
    Summable (fun k : ℕ => |a (M + k)|) ∧
      ∑' k : ℕ, |a (M + k)| ≤
        B * Real.exp (-Real.pi * (M : ℝ) ^ 2) /
          (1 - Real.exp (-3 * Real.pi))

/-- The three-vertex reconstruction statement, with deck equality as an
explicit multiplicity-preserving matching of deleted induced graphs. -/
def claim59780 : Prop :=
  ∀ (V W : Type*) [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W),
    Fintype.card V = 3 → Fintype.card W = 3 →
    (∃ σ : V ≃ W, ∀ v : V,
      Nonempty
        (G.induce {x : V | x ≠ v} ≃g
          H.induce {y : W | y ≠ σ v})) →
    Nonempty (G ≃g H)

/-- Synchronization of two fibre cocycles over a transitive action. -/
def claim59841 : Prop :=
  ∀ (G I P : Type*) [Group G] [Group P] [MulAction G I]
    (l r : G → I → P) (b : I) (t : I → G),
    (∀ i : I, t i • b = i) →
    (∀ i : I, l 1 i = 1 ∧ r 1 i = 1) →
    (∀ (g k : G) (i : I),
      l (g * k) i = l g (k • i) * l k i) →
    (∀ (g k : G) (i : I),
      r (g * k) i = r g (k • i) * r k i) →
    ((∃ h : I → P, ∀ (g : G) (i : I),
        h (g • i) * l g i = r g i * h i) ↔
      (∃ h₀ : P, ∀ k : G, k • b = b →
        h₀ * l k b = r k b * h₀)) ∧
    (∀ h₀ : P,
      (∀ k : G, k • b = b → h₀ * l k b = r k b * h₀) →
      let h : I → P := fun i => r (t i) b * h₀ * (l (t i) b)⁻¹
      ∀ (g : G) (i : I), h (g • i) * l g i = r g i * h i)

end MathlibPlus.Open.ResearchFormalizationBatch.FinitePrinciples
