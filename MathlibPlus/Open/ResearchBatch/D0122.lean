import Mathlib

namespace MathlibPlus.Open.ResearchBatch.D0122

open scoped BigOperators Classical
noncomputable section

def functionSupport {F K : Type*} [Field F] [Fintype K] [DecidableEq K]
    (q : K → F) : Finset K :=
  Finset.univ.filter (fun k => q k ≠ 0)

def canonicalRegister {F K : Type*} [Field F] [Fintype K] [DecidableEq K]
    (q : K → F) : Finset (K × F) :=
  (functionSupport q).image (fun k => (k, q k))

def decodeRegister {F K : Type*} [Field F] [Fintype K] [DecidableEq K]
    (r : Finset (K × F)) (k : K) : F :=
  ∑ p ∈ r.filter (fun p => p.1 = k), p.2

def addRegisters {F K : Type*} [Field F] [Fintype K] [DecidableEq K]
    (r₁ r₂ : Finset (K × F)) : Finset (K × F) :=
  canonicalRegister (fun k => decodeRegister r₁ k + decodeRegister r₂ k)

def claim_5673
    {F K : Type*} [Field F] [Fintype K] [DecidableEq K] : Prop :=
  (∀ q : K → F, ∀ k : K,
      (q k ≠ 0 → ∃! a : F, (k, a) ∈ canonicalRegister q) ∧
        (q k = 0 → ∀ a : F, (k, a) ∉ canonicalRegister q)) ∧
    (∀ q₁ q₂ : K → F,
      addRegisters (canonicalRegister q₁) (canonicalRegister q₂) =
        canonicalRegister (fun k => q₁ k + q₂ k)) ∧
    (∀ r₁ r₂ : Finset (K × F),
      ∀ k, decodeRegister (addRegisters r₁ r₂) k =
        decodeRegister r₁ k + decodeRegister r₂ k) ∧
    (∀ r₁ r₂ r₃ : Finset (K × F),
      addRegisters (addRegisters r₁ r₂) r₃ =
          addRegisters r₁ (addRegisters r₂ r₃) ∧
        addRegisters r₁ r₂ = addRegisters r₂ r₁)

def claim_5674
    {F K : Type*} [Field F] [Fintype K] [DecidableEq K]
    (q : K → F) (w : Nat) : Prop :=
  (functionSupport q).card ≤ w ∧ (canonicalRegister q).card ≤ w ∧
    (canonicalRegister q).card = (functionSupport q).card

def rootAcceptanceCondition {F K : Type*} [Zero F]
    (q : K → F) (τ : F) : Prop :=
  q = 0 ∧ τ ≠ 0

def claim_5677 {F K : Type*} [Field F] (q : K → F) (τ : F) : Prop :=
  rootAcceptanceCondition q τ

def prefixCurrent {F B K : Type*} [Field F] [Fintype K] [DecidableEq B]
    (v : B → K → F) (order : List B) (i : Nat) : K → F :=
  ∑ b ∈ (order.take i).toFinset, v b

def claim_5678
    {F B K : Type*} [Field F] [Fintype K] [DecidableEq B]
    (v : B → K → F) (order : List B) (w : Nat) : Prop :=
  order.Nodup →
    (∀ i ≤ order.length, (functionSupport (prefixCurrent v order i)).card ≤ w) →
      ∀ (i : Nat) (hi : i < order.length),
        let b := order.get ⟨i, hi⟩
        prefixCurrent v order (i + 1) - prefixCurrent v order i = v b ∧
          Function.support (v b) ⊆
            Function.support (prefixCurrent v order i) ∪
              Function.support (prefixCurrent v order (i + 1)) ∧
          (functionSupport (v b)).card ≤ 2 * w

inductive BinaryAggregationTree (α : Type*) where
  | leaf : α → BinaryAggregationTree α
  | node : BinaryAggregationTree α → BinaryAggregationTree α → BinaryAggregationTree α

def treeLeaves {α : Type*} : BinaryAggregationTree α → List α
  | .leaf a => [a]
  | .node l r => treeLeaves l ++ treeLeaves r

def treeSubtrees {α : Type*} : BinaryAggregationTree α → List (BinaryAggregationTree α)
  | .leaf a => [.leaf a]
  | .node l r => .node l r :: (treeSubtrees l ++ treeSubtrees r)

def treeInternalCount {α : Type*} : BinaryAggregationTree α → Nat
  | .leaf _ => 0
  | .node l r => treeInternalCount l + treeInternalCount r + 1

def treeSum {F α : Type*} [AddCommMonoid F]
    (w : α → F) : BinaryAggregationTree α → F
  | .leaf a => w a
  | .node l r => treeSum w l + treeSum w r

def covers {α : Type*} [DecidableEq α]
    (H : Finset α) (T : BinaryAggregationTree α) : Prop :=
  (treeLeaves T).Nodup ∧ (treeLeaves T).toFinset = H

def oneCodeRegister {F S : Type*} [Field F] [DecidableEq S]
    (s : S) (a : F) : Finset (S × F) :=
  if a = 0 then ∅ else {(s, a)}

def claim_5679
    {F S B : Type*} [Field F] [Fintype S] [DecidableEq S] [DecidableEq B]
    (s : S) (H : Finset B) (w : B → F) : Prop :=
  (∑ b ∈ H, w b = 0) →
    ∀ T : BinaryAggregationTree B,
      covers H T →
        (∀ U ∈ treeSubtrees T,
          (oneCodeRegister s (treeSum w U)).card ≤ 1) ∧
          treeInternalCount T = H.card - 1 ∧
            oneCodeRegister s (treeSum w T) = ∅

end

end MathlibPlus.Open.ResearchBatch.D0122
