import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1643Claim39890_R1647Claim39930

open scoped BigOperators

noncomputable section

/-- Affine and nonaffine local charts on a prime block. -/
def affineLocalChart {q : ℕ} (σ : Equiv.Perm (ZMod q)) : Prop :=
  ∃ a : (ZMod q)ˣ, ∃ b : ZMod q,
    ∀ x : ZMod q, σ x = (a : ZMod q) * x + b

def nonidentityAffineLocalChart {q : ℕ}
    (σ : Equiv.Perm (ZMod q)) : Prop :=
  affineLocalChart σ ∧ σ ≠ 1

def nonaffineLocalChart {q : ℕ}
    (τ : Equiv.Perm (ZMod q)) : Prop :=
  ¬ affineLocalChart τ

/-- A literal repeated-nonaffine/one-affine chart on eight outer blocks. -/
def repeatedThreeBlockChart (q : ℕ)
    (F : Equiv.Perm (Fin 8 × ZMod q)) : Prop :=
  ∃ (i j k : Fin 8)
    (σ τ : Equiv.Perm (ZMod q)),
    i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      nonidentityAffineLocalChart σ ∧ nonaffineLocalChart τ ∧
      (∀ x : ZMod q, F (i, x) = (i, σ x)) ∧
      (∀ x : ZMod q, F (j, x) = (j, τ x)) ∧
      (∀ x : ZMod q, F (k, x) = (k, τ x)) ∧
      (∀ l : Fin 8, l ≠ i → l ≠ j → l ≠ k →
        ∀ x : ZMod q, F (l, x) = (l, x))

/-- Claim 39890: the exact literal chart census at the two prime layers and
    its total arithmetic expression, with the chart carrier retained. -/
def literalFunctionCensus_claim39890 : Prop :=
  Nat.card {F : Equiv.Perm (Fin 8 × ZMod 5) //
      repeatedThreeBlockChart 5 F} = 319200 ∧
    Nat.card {F : Equiv.Perm (Fin 8 × ZMod 7) //
      repeatedThreeBlockChart 7 F} = 34426224 ∧
    319200 + 34426224 = 34745424 ∧
    8 * Nat.choose 7 2 * (19 * 100 + 41 * 4998) = 34745424

/-- The additive group used in the order-108 minimum-three-point branch. -/
abbrev Order108Group := ZMod 4 × (Fin 3 → ZMod 3)

abbrev ThreeFactor := ZMod 3

noncomputable def standardThreeFactor : AddSubgroup Order108Group :=
  AddSubgroup.closure
    {((0 : ZMod 4), Function.update (0 : Fin 3 → ZMod 3) 0 1)}

def additiveCoset (D : AddSubgroup Order108Group)
    (g : Order108Group) : Set Order108Group :=
  {x | ∃ d : D, (d : Order108Group) + g = x}

/-- A partition into all three-point cosets of a common subgroup. -/
def commonThreePointCosetSystem
    (D : AddSubgroup Order108Group) : Prop := by
  classical
  exact ∃ P : Finset (Set Order108Group),
    P.card = Fintype.card Order108Group / 3 ∧
      (∀ B ∈ P, B.ncard = 3 ∧ ∃ g, B = additiveCoset D g) ∧
      (∀ x : Order108Group, ∃! B, B ∈ P ∧ x ∈ B)

def directThreeFactor (D : AddSubgroup Order108Group) : Prop :=
  ∃ H : AddSubgroup Order108Group,
    Nonempty (H ≃+ (ZMod 4 × (Fin 2 → ZMod 3))) ∧
      D ⊓ H = ⊥ ∧ D ⊔ H = ⊤

/-- Claim 39930: a three-point common block subgroup is a direct factor
    `C₃`, with complementary factor `C₄×C₃²`. -/
def directFactorThreePointClaim_claim39930 : Prop :=
  ∀ D : AddSubgroup Order108Group,
    Nat.card D = 3 →
      commonThreePointCosetSystem D →
        directThreeFactor D

end

end MathlibPlus.Open.ResearchFormalization.R1643Claim39890_R1647Claim39930
