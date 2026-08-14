import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch019ffedd3a89746fb3037ba0172c78b8

section SetSystems

variable {α : Type*} [DecidableEq α]

def pairShadow (C : Set (Finset α)) : SimpleGraph α where
  Adj u v := u ≠ v ∧ ∃ S ∈ C, ({u, v} : Finset α) ⊆ S
  symm := ⟨fun u v huv =>
    ⟨huv.1.symm, by
      obtain ⟨S, hS, hsub⟩ := huv.2
      exact ⟨S, hS, by rw [Finset.pair_comm v u]; exact hsub⟩⟩⟩
  loopless := ⟨fun u huu => huu.1 rfl⟩

def isFinsetClique (G : SimpleGraph α) (S : Finset α) : Prop :=
  ∀ ⦃u v : α⦄, u ∈ S → v ∈ S → u ≠ v → G.Adj u v

def claim_21340 : Prop :=
  ∀ (C : Set (Finset α)) (u v : α),
    (pairShadow C).Adj u v ↔
      u ≠ v ∧ ∃ S ∈ C, ({u, v} : Finset α) ⊆ S

def claim_21343 : Prop :=
  ∀ (C : Set (Finset α)) (S : Finset α), S ∈ C →
    isFinsetClique (pairShadow C) S

end SetSystems

end MathlibPlus.Open.Research.FormalizationBatch019ffedd3a89746fb3037ba0172c78b8
