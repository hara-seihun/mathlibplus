import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

abbrev FourPartiteH (p r : ℕ) := Fin r → ZMod p
abbrev FourPartiteG (p r : ℕ) := ZMod 4 × FourPartiteH p r

def fourPartiteConnection (p r : ℕ) : Set (FourPartiteG p r) :=
  {g | g.1 ≠ 0}

def fourPartiteAdjacency (p r : ℕ)
    (x y : FourPartiteG p r) : Prop :=
  y - x ∈ fourPartiteConnection p r

def commonNeighborSet {G : Type*} [Fintype G]
    (adj : G → G → Prop) {k : ℕ} (xs : Fin k → G) : Set G :=
  {z | ∀ i, adj (xs i) z}

def commonNeighborCount {G : Type*} [Fintype G]
    (adj : G → G → Prop) {k : ℕ} (xs : Fin k → G) : ℕ :=
  Set.ncard (commonNeighborSet adj xs)

def withinFiberMap {p r : ℕ}
    (τ : ZMod 4 → (FourPartiteH p r ≃ FourPartiteH p r)) :
    FourPartiteG p r → FourPartiteG p r :=
  fun x => (x.1, τ x.1 x.2)

def graphAutomorphism {G : Type*}
    (adj : G → G → Prop) (f : G → G) : Prop :=
  Function.Bijective f ∧ ∀ x y, adj x y ↔ adj (f x) (f y)

/-- R-4553, S4: the displayed Cayley graph is complete four-partite, with
fibre-controlled common-neighbor counts and all within-fibre permutations as
automorphisms. -/
def claim53678 : Prop :=
  ∀ p r : ℕ, (hp : Nat.Prime p) → p % 2 = 1 → 1 ≤ r →
    letI : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
    let H := FourPartiteH p r
    let G := FourPartiteG p r
    let S := fourPartiteConnection p r
    let adj := fourPartiteAdjacency p r
    (∀ x y : G, x.1 = y.1 →
      commonNeighborCount adj (fun i : Fin 2 => if i = 0 then x else y) =
        3 * Fintype.card H) ∧
    (∀ x y : G, x.1 ≠ y.1 →
      commonNeighborCount adj (fun i : Fin 2 => if i = 0 then x else y) =
        2 * Fintype.card H) ∧
    (∀ (k : ℕ) (xs ys : Fin k → G),
      (∀ i, (xs i).1 = (ys i).1) →
      commonNeighborCount adj xs = commonNeighborCount adj ys) ∧
    (∀ τ : ZMod 4 → (H ≃ H),
      graphAutomorphism adj (withinFiberMap τ))

end

end MathlibPlus.Open.ResearchFormalization
