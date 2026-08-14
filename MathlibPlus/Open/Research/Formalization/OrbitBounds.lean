import Mathlib

noncomputable section
open scoped BigOperators Classical

namespace MathlibPlus.Open.Research.Formalization.R0363

def graphPreservedByPermutation {V : Type*}
    (G : SimpleGraph V) (σ : Equiv.Perm V) : Prop :=
  ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y

def primeOrderPermutation {V : Type*} [Fintype V]
    (p : ℕ) (σ : Equiv.Perm V) : Prop :=
  Nat.Prime p ∧ orderOf σ = p

def graphRowDistance {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x y : V) : ℕ :=
  (Finset.univ.filter (fun z => G.Adj x z ≠ G.Adj y z)).card

def claim20433_fixed_coordinates_constant_on_moved_orbit : Prop :=
  ∀ {V : Type*} [Fintype V]
    (p : ℕ) (σ : Equiv.Perm V) (G : SimpleGraph V) (x : V),
    primeOrderPermutation p σ → graphPreservedByPermutation G σ →
    x ∈ σ.support →
    ∀ z : V, σ z = z →
      (∀ k l : ℕ,
        decide (G.Adj ((σ : V → V)^[k] x) z) =
          decide (G.Adj ((σ : V → V)^[l] x) z)) ∧
      (∀ k l : ℕ,
        (if decide (G.Adj ((σ : V → V)^[k] x) z) =
            decide (G.Adj ((σ : V → V)^[l] x) z) then (0 : ℕ) else 1) = 0)

def internalRegular {V : Type*} [Fintype V]
    (H : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ x, (Finset.univ.filter (fun y => H.Adj x y)).card = r

def blockColumnWeight {p : ℕ}
    (B : Fin p → Fin p → Bool) (z : Fin p) : ℕ :=
  (Finset.univ.filter (fun x => B x z = true)).card

def blockRowDistanceSum {p : ℕ}
    (B : Fin p → Fin p → Bool) : ℕ :=
  ∑ x : Fin p,
    ∑ y ∈ (Finset.univ.filter (fun y : Fin p => x < y)),
      ∑ z : Fin p, if B x z = B y z then 0 else 1

def graphRowDistanceSum {p m : ℕ}
    (G : SimpleGraph (Fin m)) (embed : Fin p → Fin m) : ℕ :=
  ∑ x : Fin p,
    ∑ y ∈ (Finset.univ.filter (fun y : Fin p => x < y)),
      graphRowDistance G (embed x) (embed y)

def ownRowDistanceSum {p : ℕ} (H : SimpleGraph (Fin p)) : ℕ :=
  ∑ x : Fin p,
    ∑ y ∈ (Finset.univ.filter (fun y : Fin p => x < y)),
      graphRowDistance H x y

def claim20435_contribution_bounds_of_moved_orbit_blocks : Prop :=
  ∀ (p r : ℕ) (H : SimpleGraph (Fin p))
    (B : Fin p → Fin p → Bool),
    Nat.Prime p → internalRegular H r →
      ownRowDistanceSum H = p * r * (p - r) ∧
      (blockRowDistanceSum B =
          ∑ z : Fin p,
            blockColumnWeight B z * (p - blockColumnWeight B z)) ∧
      (∀ z : Fin p,
        blockColumnWeight B z * (p - blockColumnWeight B z) ≤ p * p / 4) ∧
      blockRowDistanceSum B ≤ p * (p * p / 4)

def claim20436_lower_pair_distance_total_on_one_moved_orbit : Prop :=
  ∀ (p r : ℕ) (embed : Fin p → Fin 43)
    (H : SimpleGraph (Fin p)) (G : SimpleGraph (Fin 43)),
    Function.Injective embed → Nat.Prime p → internalRegular H r →
      (∀ x y : Fin p,
        H.Adj x y ↔ G.Adj (embed x) (embed y)) →
      (∀ x y : Fin p, x < y →
        8 ≤ graphRowDistance G (embed x) (embed y) ∧
        (H.Adj x y →
          10 ≤ graphRowDistance G (embed x) (embed y))) →
      8 * Nat.choose p 2 + p * r ≤
        graphRowDistanceSum G embed

end MathlibPlus.Open.Research.Formalization.R0363
