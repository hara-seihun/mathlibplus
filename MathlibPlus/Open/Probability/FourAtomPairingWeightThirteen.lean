import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Probability

/-- Exact finite pairing-existence screen for positive-weight four-atom laws of total weight thirteen on three signs.  The carrier is deliberately local to this finite registry
statement; it records the complete Bellman-area comparison, not an external
verifier digest. -/
noncomputable def fourAtomPairingWeightThirteen : Prop :=
  let Table := Fin 8 → ℚ
  let sign : Fin 8 → Fin 3 → ℚ := fun x i =>
    if Nat.testBit x.val i.val then 1 else -1
  let oneQuery : Fin 3 → Table → Prop := fun root branch =>
    (∃ c : ℚ, (c = -1 ∨ c = 1) ∧ ∀ x, branch x = c) ∨
    (∃ j : Fin 3, j ≠ root ∧
      ∃ s : ℚ, (s = -1 ∨ s = 1) ∧
        ∀ x, branch x = s * sign x j)
  let depthTwo : Table → Prop := fun t =>
    ∃ (root : Fin 3) (low high : Table),
      oneQuery root low ∧ oneQuery root high ∧
      ∀ x, t x = if sign x root = 1 then high x else low x
  let meanOn : Table → (Fin 8 → Prop) → ℚ := fun f cell => by
    classical
    let points := (Finset.univ : Finset (Fin 8)).filter cell
    exact (∑ x ∈ points, f x) / points.card
  let varianceOn : Table → (Fin 8 → Prop) → ℚ := fun f cell => by
    classical
    let points := (Finset.univ : Finset (Fin 8)).filter cell
    let m := meanOn f cell
    exact (∑ x ∈ points, (f x - m) ^ 2) / points.card
  let variance : Table → ℚ := fun f => varianceOn f (fun _ => True)
  let Policy := {p : Fin 3 × (Bool → Fin 3) // ∀ b : Bool, p.2 b ≠ p.1}
  let policyArea : Table → Policy → ℚ := fun f p =>
    let root := p.1.1
    let second : Bool → Fin 3 := p.1.2
    variance f +
      (∑ b : Bool,
        varianceOn f (fun x => Nat.testBit x.val root.val = b)) / 2 +
      (∑ b : Bool, ∑ c : Bool,
        varianceOn f (fun x =>
          Nat.testBit x.val root.val = b ∧
            Nat.testBit x.val (second b).val = c)) / 4
  let area : Table → ℚ := fun f =>
    (Finset.univ.image (policyArea f)).min' (by
      classical
      have hp : ∀ b : Bool, (1 : Fin 3) ≠ 0 := by intro b; decide
      apply Finset.image_nonempty.mpr
      exact ⟨⟨(0, fun _ => 1), hp⟩, by simp⟩)
  let pairTarget : Table → Table → ℕ → ℕ → Table := fun f g a b x =>
    ((a : ℚ) * f x + (b : ℚ) * g x) / (a + b)
  let bound : Table → Table → Table → Table → (Fin 4 → ℕ) → ℕ → Prop :=
    fun t0 t1 t2 t3 w W =>
      let target : Table := fun x =>
        ((w 0 : ℚ) * t0 x + (w 1 : ℚ) * t1 x +
          (w 2 : ℚ) * t2 x + (w 3 : ℚ) * t3 x) / W
      let p01 := pairTarget t0 t1 (w 0) (w 1)
      let p23 := pairTarget t2 t3 (w 2) (w 3)
      let p02 := pairTarget t0 t2 (w 0) (w 2)
      let p13 := pairTarget t1 t3 (w 1) (w 3)
      let p03 := pairTarget t0 t3 (w 0) (w 3)
      let p12 := pairTarget t1 t2 (w 1) (w 2)
      area target ≤ ((w 0 + w 1 : ℕ) : ℚ) / W * area p01 +
          ((w 2 + w 3 : ℕ) : ℚ) / W * area p23 ∨
        area target ≤ ((w 0 + w 2 : ℕ) : ℚ) / W * area p02 +
          ((w 1 + w 3 : ℕ) : ℚ) / W * area p13 ∨
        area target ≤ ((w 0 + w 3 : ℕ) : ℚ) / W * area p03 +
          ((w 1 + w 2 : ℕ) : ℚ) / W * area p12
  ∀ (W : ℕ), (W = 13) →
    ∀ (t0 t1 t2 t3 : Table) (w : Fin 4 → ℕ),
      (∀ i, depthTwo (![t0, t1, t2, t3] i)) →
      (∀ i j, i ≠ j → (![t0, t1, t2, t3] i ≠
        (![t0, t1, t2, t3] j))) →
      (∀ i, 0 < w i) →
      (∑ i : Fin 4, w i = W) →
      bound t0 t1 t2 t3 w W

end MathlibPlus.Open.Probability
