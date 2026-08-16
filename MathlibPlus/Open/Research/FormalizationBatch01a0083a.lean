import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The adjacency relation of an ordinary additive Cayley graph. -/
def cayleyAdj {G : Type} [AddGroup G] (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ -x + y ∈ S

/-- Isomorphism of the two loopless undirected Cayley relations. -/
def cayleyGraphIso {G : Type} [AddGroup G] (S T : Set G) : Prop :=
  ∃ e : G ≃ G, ∀ x y, cayleyAdj S x y ↔ cayleyAdj T (e x) (e y)

/-- Claim 60923. -/
def claim60923 : Prop :=
  ∀ (r : ℕ),
    (r = 3 ∨ r = 4 ∨ r = 5) →
      let G := (Fin r → ZMod 2) × ZMod 9
      ∀ H : AddSubgroup G,
        let S : Set G := (H : Set G) \ {0}
        0 ∉ S ∧
          (∀ x, x ∈ S → -x ∈ S) ∧
            ∀ T : Set G,
              T ⊆ (Set.univ : Set G) \ {0} →
                (∀ x, x ∈ T → -x ∈ T) →
                  cayleyGraphIso S T →
                    ∃ α : G ≃+ G, Set.image (fun x => α x) S = T

/-- The matrix entry in row `i` and zero-based column `j` of the Vandermonde
matrix used in claim 60924. -/
def claim60924X (p i j : ℕ) : ZMod p :=
  ((i + 1 : ℕ) : ZMod p) ^ j

/-- The seven columns of `[I₄ | X]`, with the four rows and three columns
indexed by their natural coordinates. -/
def claim60924D (p : ℕ) (i : Fin 7) : Fin 4 → ZMod p :=
  fun k =>
    if i.1 < 4 then
      if i.1 = k.1 then 1 else 0
    else
      claim60924X p k.1 (i.1 - 4)

/-- Evaluation by the seven columns of `[-Xᵀ | I₃]`. -/
def claim60924U (p : ℕ) (i : Fin 7) (a : Fin 3 → ZMod p) : ZMod p :=
  if i.1 < 4 then
    ∑ j : Fin 3, (-claim60924X p i.1 j.1) * a j
  else
    ∑ j : Fin 3, (if j.1 = i.1 - 4 then a j else 0)

/-- The sampled slope supplied by the `i`th functional. -/
def claim60924Phi (p : ℕ) (i : Fin 7)
    (L : (Fin 4 → ZMod p) →ₗ[ZMod p] (Fin 3 → ZMod p)) : ZMod p :=
  claim60924U p i (L (claim60924D p i))

/-- Claim 60924. -/
def claim60924 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    let A := Fin 3 → ZMod p
    let B := Fin 4 → ZMod p
    (∃ u : Fin 7 → A →ₗ[ZMod p] ZMod p,
      ∀ i a, u i a = claim60924U p i a) ∧
      (∀ L : B →ₗ[ZMod p] A,
        ∑ i : Fin 7, claim60924Phi p i L = 0) ∧
      (∀ c : Fin 7 → ZMod p,
        (∀ L : B →ₗ[ZMod p] A,
          ∑ i : Fin 7, c i * claim60924Phi p i L = 0) ↔
          ∃ k : ZMod p, ∀ i, c i = k) ∧
      (∀ omitted : Fin 7, ∀ c : Fin 7 → ZMod p,
        (∀ L : B →ₗ[ZMod p] A,
          (Finset.univ.erase omitted).sum (fun i => c i * claim60924Phi p i L) = 0) →
          ∀ i, i ≠ omitted → c i = 0) ∧
      (∀ k : Fin 7 → ZMod p,
        (∃ L : B →ₗ[ZMod p] A, ∀ i, claim60924Phi p i L = k i) ↔
          ∑ i : Fin 7, k i = 0) ∧
      Function.Injective (claim60924D p) ∧
      (∃ f : B → A,
        f 0 = 0 ∧
          ∀ i, claim60924U p i (f (claim60924D p i)) =
            if i = 0 then 1 else 0) ∧
      (¬ ∃ L : B →ₗ[ZMod p] A,
        ∀ i, claim60924Phi p i L = if i = 0 then 1 else 0) ∧
      (∀ I : Finset (Fin 7), I ≠ Finset.univ →
        ∃ L : B →ₗ[ZMod p] A,
          ∀ i ∈ I, claim60924Phi p i L = if i = 0 then 1 else 0)

/-- Claim 60925. -/
def claim60925 : Prop :=
  let G := ZMod 4 × (Fin 3 → ZMod 3)
  ∀ S T : Set G,
    S ⊆ (Set.univ : Set G) \ {0} →
      (∀ x, x ∈ S → -x ∈ S) →
        T ⊆ (Set.univ : Set G) \ {0} →
          (∀ x, x ∈ T → -x ∈ T) →
            Nat.min S.ncard (107 - S.ncard) = 14 →
              Nat.min T.ncard (107 - T.ncard) = 14 →
                cayleyGraphIso S T →
                  ∃ α : G ≃+ G, Set.image (fun x => α x) S = T

end MathlibPlus.Open.ResearchFormalizationBatch
