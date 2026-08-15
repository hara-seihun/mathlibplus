import Mathlib

noncomputable section
open scoped BigOperators
open Set

namespace MathlibPlus.Open.FormalizationBatch
def packetBilinear {K A B C : Type*}
    [Semiring K]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C]
    (β : A → B → C) : Prop :=
  (∀ a, β a 0 = 0 ∧
    (∀ b₁ b₂, β a (b₁ + b₂) = β a b₁ + β a b₂) ∧
    (∀ (r : K) b, β a (r • b) = r • β a b)) ∧
  (∀ b, β 0 b = 0 ∧
    (∀ a₁ a₂, β (a₁ + a₂) b = β a₁ b + β a₂ b) ∧
    (∀ (r : K) a, β (r • a) b = r • β a b))

def classTwoMul {K A B C : Type*}
    [Semiring K]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C]
    (β : A → B → C)
    (x y : A × B × C) : A × B × C :=
  (x.1 + y.1, x.2.1 + y.2.1,
    x.2.2 + y.2.2 + β x.1 y.2.1)

def classTwoInv {K A B C : Type*}
    [Semiring K]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C]
    (β : A → B → C)
    (x : A × B × C) : A × B × C :=
  (-x.1, -x.2.1, -x.2.2 + β x.1 x.2.1)

def classTwoComm {K A B C : Type*}
    [Semiring K]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C]
    (β : A → B → C)
    (x y : A × B × C) : A × B × C :=
  classTwoMul (K := K) β
    (classTwoMul (K := K) β
      (classTwoMul (K := K) β x y) (classTwoInv (K := K) β x))
    (classTwoInv (K := K) β y)

def classTwoProjection {A B C : Type*} : A × B × C → B × C :=
  fun x => (x.2.1, x.2.2)

def classTwoCosetAction {K A B C : Type*}
    [Semiring K]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C]
    (β : A → B → C)
    (bc : B × C) (g : A × B × C) : B × C :=
  (bc.1 + g.2.1, bc.2 + g.2.2 + β g.1 bc.1)

/-- Class-two group multiplication and the supplied coset action formula. -/
def claim_52936 : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)], 2 < p →
    ∀ (A B C : Type*)
      [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
      [Module (ZMod p) A] [Module (ZMod p) B] [Module (ZMod p) C]
      [FiniteDimensional (ZMod p) A]
      [FiniteDimensional (ZMod p) B]
      [FiniteDimensional (ZMod p) C],
      ∀ β : A → B → C, packetBilinear (K := ZMod p) β →
        let G := A × B × C
        let Ω := B × C
        let U : Set G := {g | ∃ a : A, g = (a, 0, 0)}
        let π : G → Ω := classTwoProjection
        let action : Ω → G → Ω := classTwoCosetAction (K := ZMod p) β
        (∀ x y : G,
            classTwoMul (K := ZMod p) β x y =
              (x.1 + y.1, x.2.1 + y.2.1,
                x.2.2 + y.2.2 + β x.1 y.2.1)) ∧
          (∀ a : A, (a, 0, 0) ∈ U) ∧
          (∀ g : G, g ∈ U → ∃ a : A, g = (a, 0, 0)) ∧
          (∀ g x : G,
            action (π x) g = π (classTwoMul (K := ZMod p) β g x)) ∧
          (∀ (a₀ : A) (b₀ : B) (c₀ : C) (b : B) (c : C),
            action (b, c) (a₀, b₀, c₀) =
              (b + b₀, c + c₀ + β a₀ b))

def betaSelfAdjoint {K A B C : Type*}
    [Semiring K]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C]
    (β : A → B → C) (F : B →ₗ[K] A) : Prop :=
  ∀ x y : B, β (F x) y = β (F y) x

def complementAction {K A B C : Type*}
    [Semiring K]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C]
    (β : A → B → C) (F : B →ₗ[K] A)
    (xz : B × C) (bc : B × C) : B × C :=
  (bc.1 + xz.1, bc.2 + xz.2 + β (F xz.1) bc.1)

def complementMul {K A B C : Type*}
    [Semiring K]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C]
    (β : A → B → C) (F : B →ₗ[K] A)
    (xz yz : B × C) : B × C :=
  (xz.1 + yz.1, xz.2 + yz.2 + β (F xz.1) yz.1)

def complementPow {K A B C : Type*}
    [Semiring K]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C]
    (β : A → B → C) (F : B →ₗ[K] A) : ℕ → B × C → B × C
  | 0, _ => (0, 0)
  | n + 1, x => complementMul (K := K) β F
      (complementPow (K := K) β F n x) x

/-- Self-adjoint regular elementary-abelian complements and their exact action law. -/
def claim_52937 : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)], 2 < p →
    ∀ (A B C : Type*)
      [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
      [Module (ZMod p) A] [Module (ZMod p) B] [Module (ZMod p) C]
      [FiniteDimensional (ZMod p) A]
      [FiniteDimensional (ZMod p) B]
      [FiniteDimensional (ZMod p) C],
      ∀ (β : A → B → C) (F : B →ₗ[ZMod p] A),
        packetBilinear (K := ZMod p) β → betaSelfAdjoint β F →
        let Ω := B × C
        let E : Set (Ω → Ω) :=
          {g | ∃ xz : B × C, g = complementAction β F xz}
        (∀ xz : B × C,
          Function.Bijective (complementAction β F xz)) ∧
          (∀ xz : B × C,
            complementAction β F xz (0, 0) = xz) ∧
          Function.Injective (fun xz : B × C => complementAction β F xz) ∧
          (∀ xz yz : B × C, ∀ bc : Ω,
            complementAction β F xz (complementAction β F yz bc) =
              complementAction β F (complementMul β F xz yz) bc) ∧
          (∀ xz yz : B × C,
            complementMul β F xz yz = complementMul β F yz xz) ∧
          (∀ xz : B × C,
            complementPow β F p xz = (0, 0)) ∧
          (∀ bc : Ω,
            Function.Bijective (fun xz : B × C => complementAction β F xz bc)) ∧
          (∀ g : Ω → Ω, g ∈ E → Function.Bijective g) ∧
          (fun bc : Ω => bc) ∈ E ∧
          (∀ g h : Ω → Ω, g ∈ E → h ∈ E →
            (fun bc => g (h bc)) ∈ E) ∧
          (∀ g h : Ω → Ω, g ∈ E → h ∈ E →
            (fun bc => g (h bc)) = (fun bc => h (g bc)))

end MathlibPlus.Open.FormalizationBatch
