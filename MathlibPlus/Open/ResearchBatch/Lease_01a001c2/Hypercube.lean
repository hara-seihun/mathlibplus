import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchBatch.Hypercube

noncomputable section
open Classical

abbrev F2 := ZMod 2
abbrev Omega (n : ℕ) (i : Fin n) := {x : Fin n → F2 // x i = 0}

def flipInFiber {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : Omega n i) : Omega n i :=
  ⟨fun k => if k = j then x.1 k + 1 else x.1 k, by simp [hij, x.2]⟩

def indicator (b : Bool) : ℝ := if b then 1 else 0

def fiberDensity {n : ℕ} (i : Fin n) (f : Omega n i → Bool) : ℝ :=
  (Fintype.card {x : Omega n i // f x = true} : ℝ) /
    Fintype.card (Omega n i)

def influenceTerm {n : ℕ} (i : Fin n) (f : Omega n i → Bool) (j : Fin n) : ℝ :=
  if hij : i ≠ j then
    (Fintype.card {x : Omega n i // f x ≠ f (flipInFiber i j hij x)} : ℝ) /
      Fintype.card (Omega n i)
  else 0

def fiberInfluence {n : ℕ} (i : Fin n) (f : Omega n i → Bool) : ℝ :=
  ∑ j, influenceTerm i f j

def edgeCount {n : ℕ} (f : ∀ i : Fin n, Omega n i → Bool) : ℝ :=
  ∑ i, (Fintype.card {x : Omega n i // f i x = true} : ℝ)

def unitFlip {n : ℕ} (i : Fin n) (x : Fin n → F2) : Fin n → F2 :=
  fun j => if j = i then x j + 1 else x j

def cubeAdj {n : ℕ} (f : ∀ i : Fin n, Omega n i → Bool)
    (x y : Fin n → F2) : Prop :=
  ∃ i : Fin n, ∃ hxi : x i = 0, y = unitFlip i x ∧
    f i ⟨x, hxi⟩ = true

def cubeGraph {n : ℕ} (f : ∀ i : Fin n, Omega n i → Bool) :
    SimpleGraph (Fin n → F2) :=
  SimpleGraph.fromRel (cubeAdj f)

def c4Free {α : Type} (G : SimpleGraph α) : Prop :=
  ∀ x y z w : α, G.Adj x y → G.Adj y z → G.Adj z w → G.Adj w x →
    x ≠ z → y ≠ w → False

/-- Claim 32765. -/
def claim_32765 : Prop :=
  ∀ n : ℕ, ∀ f : ∀ i : Fin n, Omega n i → Bool,
    (∀ i : Fin n, ∃ pᵢ : ℝ, pᵢ = fiberDensity i (f i)) ∧
    (∀ i : Fin n, ∃ Iᵢ : ℝ, Iᵢ = fiberInfluence i (f i)) ∧
    edgeCount f = (2 ^ (n - 1) : ℝ) * ∑ i, fiberDensity i (f i)

/-- Claim 32768. -/
def claim_32768 : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ f : ∀ i : Fin n, Omega n i → Bool,
      c4Free (cubeGraph f) →
      ∑ i, fiberDensity i (f i) ≤
        (n : ℝ) / 2 +
          (∑ i, fiberInfluence i (f i)) / (2 * (n - 1))

end
end MathlibPlus.Open.ResearchBatch.Hypercube
