import Mathlib

namespace MathlibPlus.Open

/-- Adjacency in the ordinary right-Cayley graph on `C_2^r × C_9`.
The inverse-closed and identity-free hypotheses in the aligned claim make this
relation simple and undirected. -/
def binaryTimesC9RightCayleyAdjacency
    (r : ℕ) (S : Set ((Fin r → ZMod 2) × ZMod 9))
    (x y : (Fin r → ZMod 2) × ZMod 9) : Prop :=
  ∃ s ∈ S, y = x + s

/-- Exact admitted CI assertion for ranks three through five. -/
def binaryTimesC9Rank345CI : Prop :=
  (∀ (r : ℕ),
    (r = 3 ∨ r = 4 ∨ r = 5) →
      let G := (Fin r → ZMod 2) × ZMod 9
      ∀ S : Set G,
        (∀ s ∈ S, s ≠ 0) →
        (∀ s ∈ S, -s ∈ S) →
        (S.ncard = 4 ∨ S.ncard = Fintype.card G - 5) →
        ∀ T : Set G,
          (∀ t ∈ T, t ≠ 0) →
          (∀ t ∈ T, -t ∈ T) →
          ∀ e : G ≃ G,
            (∀ x y,
              binaryTimesC9RightCayleyAdjacency r S x y ↔
                binaryTimesC9RightCayleyAdjacency r T (e x) (e y)) →
            ∃ α : G ≃+ G,
              α '' S = T) ∧
  (Fintype.card ((Fin 3 → ZMod 2) × ZMod 9) - 5 = 67) ∧
  (Fintype.card ((Fin 4 → ZMod 2) × ZMod 9) - 5 = 139) ∧
  (Fintype.card ((Fin 5 → ZMod 2) × ZMod 9) - 5 = 283)

end MathlibPlus.Open
