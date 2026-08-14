import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch01_01a000fa

inductive NeutralNode
  | f (i : Fin 30)
  | k (i : Fin 9)
  | g (i : Fin 19)
  | r (i : Fin 8)
  | q
deriving DecidableEq, Fintype

def neutralLe : NeutralNode → NeutralNode → Prop
  | .f i, .f j => i ≤ j
  | .f _, .k _ => True
  | .f _, .g _ => True
  | .f _, .r _ => True
  | .f _, .q => True
  | .k i, .k j => i ≤ j
  | .k i, .r j => i.val ≤ j.val
  | .k _, .q => True
  | .g i, .g j => i ≤ j
  | .g _, .r _ => True
  | .g _, .q => True
  | .r i, .r j => i ≤ j
  | .r _, .q => True
  | .q, .q => True
  | _, _ => False

def neutralLastF : Fin 30 := ⟨29, by omega⟩

def neutralKAtRoot (a : Fin 8) : Fin 9 := ⟨a.val, by omega⟩

def neutralLastK : Fin 9 := ⟨8, by omega⟩

def neutralIsLUB (x y z : NeutralNode) : Prop :=
  neutralLe x z ∧ neutralLe y z ∧
    ∀ w, neutralLe x w → neutralLe y w → neutralLe z w

def claim42321 : Prop :=
  Fintype.card NeutralNode = 67 ∧
  IsPartialOrder NeutralNode neutralLe ∧
  (∀ i j : Fin 30, neutralLe (.f i) (.f j) ↔ i ≤ j) ∧
  (∀ i j : Fin 9, neutralLe (.k i) (.k j) ↔ i ≤ j) ∧
  (∀ i j : Fin 19, neutralLe (.g i) (.g j) ↔ i ≤ j) ∧
  (∀ i j : Fin 8, neutralLe (.r i) (.r j) ↔ i ≤ j) ∧
  (∀ i : Fin 9, neutralLe (.f neutralLastF) (.k i)) ∧
  (∀ i : Fin 19, neutralLe (.f neutralLastF) (.g i)) ∧
  (∀ i : Fin 9, ∀ j : Fin 19,
    ¬ neutralLe (.k i) (.g j) ∧ ¬ neutralLe (.g j) (.k i)) ∧
  (∀ i : NeutralNode, neutralLe i .q) ∧
  (∀ a : Fin 8,
    (∀ b : Fin 19, neutralLe (.g b) (.r a)) ∧
    (∀ j : Fin 9, neutralLe (.k j) (.r a) ↔ j.val ≤ a.val))

def claim42322 : Prop :=
  (∀ a : Fin 8, ∀ b : Fin 19,
    neutralIsLUB (.k (neutralKAtRoot a)) (.g b) (.r a)) ∧
  (∀ b : Fin 19,
    neutralIsLUB (.k neutralLastK) (.g b) .q) ∧
  (∀ i j : Fin 30,
    neutralIsLUB (.f i) (.f j) (.f (max i j))) ∧
  (∀ i j : Fin 9,
    neutralIsLUB (.k i) (.k j) (.k (max i j))) ∧
  (∀ i j : Fin 19,
    neutralIsLUB (.g i) (.g j) (.g (max i j))) ∧
  (∀ i j : Fin 8,
    neutralIsLUB (.r i) (.r j) (.r (max i j))) ∧
  (∀ x y : NeutralNode, ∃! z, neutralIsLUB x y z)

def passiveSignature (j : Fin 9) (a : Fin 8) : Bool :=
  decide (j.val > a.val)

def claim42327 : Prop :=
  (∀ a : Fin 8, ∀ j : Fin 9,
    passiveSignature j a = true ↔ j.val > a.val) ∧
  Function.Injective (fun j : Fin 9 => fun a : Fin 8 => passiveSignature j a)

abbrev BlockVector (r : ℕ) := Fin r → ZMod 3
abbrev BlockGroup (r : ℕ) := ZMod 4 × BlockVector r
abbrev BlockQuotient (r : ℕ) := ZMod 2 × BlockVector r

def blockParity (a : ZMod 4) : ZMod 2 :=
  (a.val % 2 : ZMod 2)

def blockFiber (a : ZMod 4) : ZMod 2 :=
  (a.val / 2 : ZMod 2)

def blockEncode (ε t : ZMod 2) : ZMod 4 :=
  ((ε.val + 2 * t.val : ℕ) : ZMod 4)

def blockLift {r : ℕ}
    (q : BlockQuotient r ≃ BlockQuotient r)
    (s : BlockQuotient r → ZMod 2) : BlockGroup r → BlockGroup r :=
  fun p =>
    let z := q (blockParity p.1, p.2)
    (blockEncode z.1 (blockFiber p.1 + s (blockParity p.1, p.2)), z.2)

def rightRegular (α : Type*) [AddGroup α] : Set (Equiv.Perm α) :=
  {p | ∃ a : α, p = Equiv.addRight a}

def conjugateSet {α : Type*}
    (f : Equiv.Perm α) (R : Set (Equiv.Perm α)) : Set (Equiv.Perm α) :=
  {p | ∃ r, r ∈ R ∧ p = f.symm * r * f}

def isRegularCopy {α : Type*} (R : Set (Equiv.Perm α)) : Prop :=
  ∀ x y : α, ∃! p, p ∈ R ∧ p x = y

def claim42358 : Prop :=
  Fintype.card (BlockGroup 3) = 108 ∧
  Fintype.card (BlockQuotient 3) = 54 ∧
  ∀ (q : BlockQuotient 3 ≃ BlockQuotient 3)
    (s : BlockQuotient 3 → ZMod 2),
    q (0, 0) = (0, 0) →
    s (0, 0) = 0 →
    ∃ f : Equiv.Perm (BlockGroup 3),
      (∀ p, f p = blockLift q s p) ∧
      f (0, 0) = (0, 0) ∧
      isRegularCopy (conjugateSet f (rightRegular (BlockGroup 3)))

def isBlockLift {r : ℕ}
    (f : Equiv.Perm (BlockGroup r))
    (B : BlockVector r ≃ₗ[ZMod 3] BlockVector r) : Prop :=
  ∀ (a : ZMod 4) (v : BlockVector r),
    blockParity (f (a, v)).1 = blockParity a ∧
    (f (a, v)).2 = B v

def claim42368 : Prop :=
  ∀ (r : ℕ)
    (B : BlockVector r ≃ₗ[ZMod 3] BlockVector r)
    (f : Equiv.Perm (BlockGroup r)),
    isBlockLift f B →
    ∃! s : BlockQuotient r → ZMod 2,
      ∀ (a : ZMod 4) (v : BlockVector r),
        f (a, v) =
          (blockEncode (blockParity a)
            (blockFiber a + s (blockParity a, v)), B v)

end MathlibPlus.Open.ResearchFormalizationBatch01_01a000fa
