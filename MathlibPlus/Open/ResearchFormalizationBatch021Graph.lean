import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch021Graph

abbrev BlockVertex (m : ℕ) := Fin m × Fin 4

def p4Edge (a b : Fin 4) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
  (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨
  (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)

def mP4Adj {m : ℕ} (v w : BlockVertex m) : Prop :=
  v.1 = w.1 ∧ p4Edge v.2 w.2

def leftGraphAdj (m : ℕ) : BlockVertex m → BlockVertex m → Prop := mP4Adj

def rightGraphAdj (m : ℕ) : BlockVertex m → BlockVertex m → Prop := mP4Adj

def cardTransposition (i p : Fin 4) : Fin 4 :=
  if i = 0 then
    if p = 1 then 3 else if p = 3 then 1 else p
  else if i = 1 then
    if p = 2 then 3 else if p = 3 then 2 else p
  else if i = 2 then
    if p = 0 then 1 else if p = 1 then 0 else p
  else
    if p = 0 then 2 else if p = 2 then 0 else p

def prescribedCardMap {m : ℕ} (b : Fin m) (i : Fin 4) :
    BlockVertex m → BlockVertex m := fun v =>
  if v.1 = b then (v.1, cardTransposition i v.2) else v

def deletedVertex {m : ℕ} (b : Fin m) (i : Fin 4) : BlockVertex m := (b, i)

def cardAutomorphismCondition {m : ℕ} (b : Fin m) (i : Fin 4) : Prop :=
  let d := deletedVertex b i
  prescribedCardMap b i d = d ∧
    (∀ v, v ≠ d → prescribedCardMap b i v ≠ d) ∧
    (∀ v, v ≠ d → prescribedCardMap b i (prescribedCardMap b i v) = v) ∧
    (∀ v w, v ≠ d → w ≠ d →
      (mP4Adj (prescribedCardMap b i v) (prescribedCardMap b i w) ↔ mP4Adj v w)
    )

def fullGraphAutomorphismCondition {m : ℕ} (b : Fin m) (i : Fin 4) : Prop :=
  Function.Bijective (prescribedCardMap b i) ∧
    ∀ v w, mP4Adj (prescribedCardMap b i v) (prescribedCardMap b i w) ↔ mP4Adj v w

def identityGlobalIsomorphism (m : ℕ) : Prop :=
  Function.Bijective (id : BlockVertex m → BlockVertex m) ∧
    (∀ v w, leftGraphAdj m v w ↔ rightGraphAdj m (id v) (id w))

def claim_12639 : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    leftGraphAdj m = rightGraphAdj m ∧
    (∀ (b : Fin m) (i : Fin 4),
      cardAutomorphismCondition b i ∧
      ¬ fullGraphAutomorphismCondition b i) ∧
    identityGlobalIsomorphism m

end MathlibPlus.Open.ResearchFormalizationBatch021Graph
