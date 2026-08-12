import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Tactic

namespace MathlibPlus.GraphTheory.Claim22877

open scoped BigOperators

/-!
Formalization of admitted claim 22877.  The four colors are ordered as the
words `00`, `01`, `10`, `11`.  The exact row masses and the spanning-star
consequence are retained.  The FAL-card and outside-host block predicates are
left as explicit interfaces because the claim packet gives no Lean definitions
for them.
-/

/-- The three exact row masses contract all four color coordinates to one
value: a vector annihilated by every row is constant on the four colors. -/
theorem exactFourColorRows_contract
    (k : ℕ) :
    let scale : ℚ :=
      (Nat.factorial (k + 8) : ℚ) / (Nat.factorial k : ℚ)
    let rowAB : Fin 4 → ℚ := scale • ![(1 : ℚ), -1, 0, 0]
    let rowCA : Fin 4 → ℚ := scale • ![(1 : ℚ), 0, -1, 0]
    let rowCD : Fin 4 → ℚ := (scale / 2) • ![(1 : ℚ), 0, 0, -1]
    (rowAB = scale • ![(1 : ℚ), -1, 0, 0]) ∧
      (rowCA = scale • ![(1 : ℚ), 0, -1, 0]) ∧
      (rowCD = (scale / 2) • ![(1 : ℚ), 0, 0, -1]) ∧
      ∀ v : Fin 4 → ℚ,
        (∑ i : Fin 4, rowAB i * v i) = 0 →
        (∑ i : Fin 4, rowCA i * v i) = 0 →
        (∑ i : Fin 4, rowCD i * v i) = 0 →
        v 0 = v 1 ∧ v 0 = v 2 ∧ v 0 = v 3 := by
  dsimp
  have hscale : 0 <
      (Nat.factorial (k + 8) : ℚ) / (Nat.factorial k : ℚ) := by
    have hfac : (0 : ℚ) < (Nat.factorial k : ℚ) := by positivity
    positivity
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro v hab hca hcd
  simp [Fin.sum_univ_succ] at hab hca hcd
  have hab' :
      ((Nat.factorial (k + 8) : ℚ) / (Nat.factorial k : ℚ)) *
        (v 0 - v 1) = 0 := by
    linarith [hab]
  have hca' :
      ((Nat.factorial (k + 8) : ℚ) / (Nat.factorial k : ℚ)) *
        (v 0 - v 2) = 0 := by
    linarith [hca]
  have hcd' :
      (((Nat.factorial (k + 8) : ℚ) / (Nat.factorial k : ℚ)) / 2) *
        (v 0 - v 3) = 0 := by
    linarith [hcd]
  have hv01 : v 0 - v 1 = 0 :=
    (mul_eq_zero.mp hab').resolve_left (ne_of_gt hscale)
  have hv02 : v 0 - v 2 = 0 :=
    (mul_eq_zero.mp hca').resolve_left (ne_of_gt hscale)
  have hscale2 : 0 <
      ((Nat.factorial (k + 8) : ℚ) / (Nat.factorial k : ℚ)) / 2 := by
    positivity
  have hv03 : v 0 - v 3 = 0 :=
    (mul_eq_zero.mp hcd').resolve_left (ne_of_gt hscale2)
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The four colors and the three nonzero supports are the displayed spanning
star. -/
theorem twoColorSupports_form_spanningStar_claim22877 :
    let V := Fin 2 × Fin 2
    let c : V := (0, 0)
    let a : V := (0, 1)
    let b : V := (1, 0)
    let d : V := (1, 1)
    let G : SimpleGraph V := SimpleGraph.starGraph c
    G.IsTree ∧
      G.Adj c a ∧ G.Adj c b ∧ G.Adj c d ∧
      (∀ x y : V, G.Adj x y ↔
        (x = c ∧ y = a) ∨ (x = a ∧ y = c) ∨
        (x = c ∧ y = b) ∨ (x = b ∧ y = c) ∨
        (x = c ∧ y = d) ∨ (x = d ∧ y = c)) := by
  dsimp
  let c : Fin 2 × Fin 2 := (0, 0)
  let a : Fin 2 × Fin 2 := (0, 1)
  let b : Fin 2 × Fin 2 := (1, 0)
  let d : Fin 2 × Fin 2 := (1, 1)
  let G : SimpleGraph (Fin 2 × Fin 2) := SimpleGraph.starGraph c
  refine ⟨SimpleGraph.isTree_starGraph c, ?_, ?_, ?_, ?_⟩
  · exact SimpleGraph.starGraph_center_adj (by simp [c, a])
  · exact SimpleGraph.starGraph_center_adj (by simp [c, b])
  · exact SimpleGraph.starGraph_center_adj (by simp [c, d])
  · intro x y
    rw [SimpleGraph.starGraph_adj]
    constructor
    · rintro ⟨hxy, hcenter | hcenter⟩
      · by_cases hx : x = c
        · subst x
          fin_cases y <;> simp_all [c, a, b, d]
        · have : x = a ∨ x = b ∨ x = d := by
            fin_cases x <;> simp_all [c, a, b, d]
          rcases this with rfl | rfl | rfl <;>
            fin_cases y <;> simp_all [c, a, b, d]
      · by_cases hy : y = c
        · subst y
          fin_cases x <;> simp_all [c, a, b, d]
        · have : y = a ∨ y = b ∨ y = d := by
            fin_cases y <;> simp_all [c, a, b, d]
          rcases this with rfl | rfl | rfl <;>
            fin_cases x <;> simp_all [c, a, b, d]
    · intro h
      rcases h with h | h | h | h | h | h <;>
        rcases h with ⟨hx, hy⟩ <;>
        simp_all [c, a, b, d]

end MathlibPlus.GraphTheory.Claim22877
