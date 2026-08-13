import Mathlib.Data.Set.Lattice
import Mathlib.Data.ZMod.Basic

namespace MathlibPlus.Open.GraphTheory

/-- Exact local-transposition atom containment from claim 55107.  An atom is
represented by the two-element (possibly degenerate) set `{d, -d}`; the
conditional branches on the right omit the zero vector as in the source. -/
def localTranspositionAtomContainment_claim55107 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 2 < p →
    ∀ (r : ℕ), 2 ≤ r →
      ∀ (a b : Fin r → ZMod p),
        a ≠ 0 → b ≠ 0 → a ≠ b →
        let V := Fin r → ZMod p
        let δ : V := b - a
        let f : V → V := fun x =>
          if x = a then b else if x = b then a else x
        let atom : V → Set V := fun d => {d, -d}
        let targetLabels : V → Set (Set V) := fun d =>
          {S | ∃ x y : V,
            (x - y = d ∨ x - y = -d) ∧ S = atom (f x - f y)}
        (∀ d : V, d ≠ 0 →
          targetLabels d ⊆
            {atom d} ∪
              (if d + δ = 0 then (∅ : Set (Set V))
               else {atom (d + δ)}) ∪
              (if d - δ = 0 then (∅ : Set (Set V))
               else {atom (d - δ)})) ∧
          atom (f a - f b) = atom δ

end MathlibPlus.Open.GraphTheory
