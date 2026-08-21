-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-- The odd-period part of admitted claim 31115, stated on eight cyclic
coordinates. The source's additional derivative notation is not needed for
this constancy consequence. -/
theorem oddPeriodicWord_constant_claim31115 {α : Type*} (c : Fin 8 → α) :
    let shift : Fin 8 → Fin 8 → Fin 8 := fun i d =>
      ⟨(i.val + d.val) % 8, Nat.mod_lt _ (by omega)⟩
    ∀ d : Fin 8, d.val % 2 = 1 →
      (∀ i : Fin 8, c (shift i d) = c i) →
      ∀ i : Fin 8, c i = c 0 := by
  dsimp
  intro d hd hper i
  fin_cases d <;> simp_all <;> fin_cases i
  all_goals
    have h0 := hper (0 : Fin 8)
    have h1 := hper (1 : Fin 8)
    have h2 := hper (2 : Fin 8)
    have h3 := hper (3 : Fin 8)
    have h4 := hper (4 : Fin 8)
    have h5 := hper (5 : Fin 8)
    have h6 := hper (6 : Fin 8)
    have h7 := hper (7 : Fin 8)
    simp at h0 h1 h2 h3 h4 h5 h6 h7
    aesop

/-- The exact direction-count and density arithmetic in the explicit
`Q₅` staircase witness of admitted claim 36925. The fourth coordinate is
free in each displayed formula, so the counts are doubled from the displayed
three-variable expressions. -/
theorem q5StaircaseWitness_counts_claim36925 :
    let f₀ : (Fin 4 → Bool) → Bool := fun x => x 0 && (x 1 || x 2)
    let f₁ : (Fin 4 → Bool) → Bool := fun x => x 1 || x 2
    let f₂ : (Fin 4 → Bool) → Bool := fun x => (!x 0) && x 2
    let f₃ : (Fin 4 → Bool) → Bool := fun x => (!x 0) || (!x 1)
    let f₄ : (Fin 4 → Bool) → Bool :=
      fun x => (!x 2) && ((!x 0) || (!x 1))
    let count : ((Fin 4 → Bool) → Bool) → ℕ := fun f =>
      Fintype.card {x : Fin 4 → Bool // f x = true}
    count f₀ = 6 ∧ count f₁ = 12 ∧ count f₂ = 4 ∧
      count f₃ = 12 ∧ count f₄ = 6 ∧
      count f₀ + count f₁ + count f₂ + count f₃ + count f₄ = 40 ∧
      count f₀ < 16 ∧ count f₁ < 16 ∧ count f₂ < 16 ∧
      count f₃ < 16 ∧ count f₄ < 16 ∧
      (count f₀ + count f₁ + count f₂ + count f₃ + count f₄ : ℚ) / 16 = 5 / 2 := by
  native_decide

end MathlibPlus.Combinatorics
