import Mathlib

namespace MathlibPlus.Open.Combinatorics.BalancedBlockClaims

abbrev F2 := ZMod 2

def OffDiagonalSymmetric {n : Nat} (s : Fin n → Fin n → F2) : Prop :=
  ∀ i j, i ≠ j → s i j = s j i

def CliqueTransversal {n k : Nat} (s : Fin n → Fin n → F2) : Prop :=
  ∃ (I : Fin k → Fin n), Function.Injective I ∧
    ∃ x : Fin k → F2,
      ∀ i j, i ≠ j → x i + x j = s (I i) (I j)

def IndependentTransversal {n k : Nat} (s : Fin n → Fin n → F2) : Prop :=
  ∃ (I : Fin k → Fin n), Function.Injective I ∧
    ∃ x : Fin k → F2,
      ∀ i j, i ≠ j → x i + x j ≠ s (I i) (I j)

def TriangleParity {n : Nat} (s : Fin n → Fin n → F2)
    (i j k : Fin n) : F2 := s i j + s i k + s j k

def AllTriangleParityOn {n k : Nat} (s : Fin n → Fin n → F2)
    (I : Fin k → Fin n) (b : F2) : Prop :=
  ∀ i j k', i ≠ j → i ≠ k' → j ≠ k' →
    TriangleParity s (I i) (I j) (I k') = b

def AllPairSignsOn {n k : Nat} (s : Fin n → Fin n → F2)
    (I : Fin k → Fin n) (b : F2) : Prop :=
  ∀ i j, i ≠ j → s (I i) (I j) = b

def claim_22235 : Prop :=
  ∀ (matching : F2 → F2), Function.Bijective matching →
    ∃ sign : F2, ∀ x y : F2, y = matching x ↔ x + y = sign

def claim_22236 : Prop :=
  ∀ (n : Nat) (s : Fin n → Fin n → F2), OffDiagonalSymmetric s →
    ((∃ x : Fin n → F2,
        ∀ i j, i ≠ j → x i + x j = s i j) ↔
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        TriangleParity s i j k = 0) ∧
    ((∃ x : Fin n → F2,
        ∀ i j, i ≠ j → x i + x j ≠ s i j) ↔
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        TriangleParity s i j k = 1)

def claim_22238 : Prop :=
  ∀ (n : Nat) (s : Fin n → Fin n → F2), OffDiagonalSymmetric s →
    (¬ CliqueTransversal (k := 5) s ∧
      ¬ IndependentTransversal (k := 5) s) →
      n ≤ 18

def claim_22239 : Prop :=
  ∃ s : Fin 18 → Fin 18 → F2,
    OffDiagonalSymmetric s ∧
      ¬ CliqueTransversal (k := 5) s ∧
      ¬ IndependentTransversal (k := 5) s

def SwitchedSign {n : Nat} (s : Fin n → Fin n → F2)
    (root i j : Fin n) : F2 :=
  if i = j then 0 else
    s i j + (if i = root then 0 else s root i) +
      (if j = root then 0 else s root j)

def Ramsey44Upper : Prop :=
  ∀ (n : Nat), 18 ≤ n →
    ∀ s : Fin n → Fin n → F2, OffDiagonalSymmetric s →
      ∃ (I : Fin 4 → Fin n), Function.Injective I ∧
        (AllPairSignsOn s I 0 ∨ AllPairSignsOn s I 1)

def Ramsey44Is18 : Prop :=
  Ramsey44Upper ∧
    ∃ s : Fin 17 → Fin 17 → F2,
      OffDiagonalSymmetric s ∧
        ¬ (∃ I : Fin 4 → Fin 17,
            Function.Injective I ∧ AllPairSignsOn s I 0) ∧
        ¬ (∃ I : Fin 4 → Fin 17,
            Function.Injective I ∧ AllPairSignsOn s I 1)

def RootedCliqueTransversal {n : Nat}
    (s : Fin n → Fin n → F2) (rootSign : Fin n → F2) : Prop :=
  ∃ (I : Fin 4 → Fin n), Function.Injective I ∧
    ∃ x : Fin 4 → F2,
      (∀ i, 0 + x i = rootSign (I i)) ∧
      (∀ i j, i ≠ j → x i + x j = s (I i) (I j))

def RootedIndependentTransversal {n : Nat}
    (s : Fin n → Fin n → F2) (rootSign : Fin n → F2) : Prop :=
  ∃ (I : Fin 4 → Fin n), Function.Injective I ∧
    ∃ x : Fin 4 → F2,
      (∀ i, 0 + x i ≠ rootSign (I i)) ∧
      (∀ i j, i ≠ j → x i + x j ≠ s (I i) (I j))

def claim_22240 : Prop :=
  (Ramsey44Is18 →
      ∀ (n : Nat) (s : Fin n → Fin n → F2), OffDiagonalSymmetric s →
        (¬ CliqueTransversal (k := 5) s ∧
          ¬ IndependentTransversal (k := 5) s) → n ≤ 18) ∧
    ∀ (n : Nat) (s : Fin n → Fin n → F2) (root : Fin n),
      OffDiagonalSymmetric s →
      (∀ i, i ≠ root → SwitchedSign s root root i = 0) ∧
      ∀ (I : Fin 4 → Fin n), Function.Injective I →
        (∀ i, I i ≠ root) →
        let e : Fin 5 → Fin n := Fin.cases root I
        Function.Injective e ∧
          ((AllTriangleParityOn (SwitchedSign s root) e 0 ↔
              AllPairSignsOn (SwitchedSign s root) I 0) ∧
            (AllTriangleParityOn (SwitchedSign s root) e 1 ↔
              AllPairSignsOn (SwitchedSign s root) I 1))

def claim_22244 : Prop :=
  ∃ (s : Fin 7 → Fin 7 → F2) (rootSign : Fin 7 → F2),
    OffDiagonalSymmetric s ∧
      (∀ i, rootSign i = 0) ∧
      ¬ RootedCliqueTransversal s rootSign ∧
      ¬ RootedIndependentTransversal s rootSign

def TriangleFree {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
    ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)

def IndependenceNumberAtMostThree {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ e : Fin 4 → V, Function.Injective e →
    ¬ (∀ i j, i ≠ j → ¬ G.Adj (e i) (e j))

def HasInducedTwoKTwo {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ e : Fin 4 → V, Function.Injective e ∧
    G.Adj (e 0) (e 1) ∧ G.Adj (e 2) (e 3) ∧
    ¬ G.Adj (e 0) (e 2) ∧ ¬ G.Adj (e 0) (e 3) ∧
    ¬ G.Adj (e 1) (e 2) ∧ ¬ G.Adj (e 1) (e 3)

def HasInducedKTwoThree {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ e : Fin 5 → V, Function.Injective e ∧
    G.Adj (e 0) (e 2) ∧ G.Adj (e 0) (e 3) ∧ G.Adj (e 0) (e 4) ∧
    G.Adj (e 1) (e 2) ∧ G.Adj (e 1) (e 3) ∧ G.Adj (e 1) (e 4) ∧
    ¬ G.Adj (e 0) (e 1) ∧ ¬ G.Adj (e 2) (e 3) ∧
    ¬ G.Adj (e 2) (e 4) ∧ ¬ G.Adj (e 3) (e 4)

def IsInducedCycleFive {V : Type} (G : SimpleGraph V) (e : Fin 5 → V) : Prop :=
  Function.Injective e ∧
    G.Adj (e 0) (e 1) ∧ G.Adj (e 1) (e 2) ∧
    G.Adj (e 2) (e 3) ∧ G.Adj (e 3) (e 4) ∧ G.Adj (e 4) (e 0) ∧
    ¬ G.Adj (e 0) (e 2) ∧ ¬ G.Adj (e 0) (e 3) ∧
    ¬ G.Adj (e 1) (e 3) ∧ ¬ G.Adj (e 1) (e 4) ∧
    ¬ G.Adj (e 2) (e 4)

def HasInducedCycleFive {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ e : Fin 5 → V, IsInducedCycleFive G e

def BipartitePartsAtMostThree {V : Type} [Fintype V]
    (G : SimpleGraph V) : Prop :=
  ∃ color : V → Bool,
    (∀ u v, G.Adj u v → color u ≠ color v) ∧
      (∀ b : Bool, Fintype.card {v // color v = b} ≤ 3)

def OutsideCycle {V : Type} (e : Fin 5 → V) (v : V) : Prop :=
  ∀ j, v ≠ e j

def AnticompleteToCycle {V : Type} (G : SimpleGraph V)
    (e : Fin 5 → V) (v : V) : Prop :=
  ∀ j, ¬ G.Adj v (e j)

def FalseTwinOfCycleVertex {V : Type} (G : SimpleGraph V)
    (e : Fin 5 → V) (v : V) (i : Fin 5) : Prop :=
  OutsideCycle e v ∧ ∀ j, G.Adj v (e j) ↔ G.Adj (e i) (e j)

def claim_22242 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    TriangleFree G →
      IndependenceNumberAtMostThree G →
        ¬ HasInducedTwoKTwo G →
          ¬ HasInducedKTwoThree G →
            Fintype.card V ≤ 6 ∧
              (¬ HasInducedCycleFive G → BipartitePartsAtMostThree G) ∧
              (∀ e : Fin 5 → V, IsInducedCycleFive G e →
                (∀ v, OutsideCycle e v →
                  (AnticompleteToCycle G e v ∨
                    ∃ i : Fin 5, FalseTwinOfCycleVertex G e v i)) ∧
                  (∀ v w, OutsideCycle e v → OutsideCycle e w → v = w))

end MathlibPlus.Open.Combinatorics.BalancedBlockClaims
