import Mathlib.Tactic

namespace MathlibPlus.Combinatorics

/-- The coordinatewise common-completion criterion behind claim 47899.
For a signed integral boundary `v`, two nonnegative realizable vectors differ by
`v` exactly when the positive and negative Jordan parts of `v` admit one common
nonnegative completion.  The predicate `D` is the source's realizable leaf-deck
carrier; its tree-specific definition is intentionally left to the alignment.
-/
theorem commonCompletion_iff_claim47899
    {ι : Type*} (D : (ι → ℤ) → Prop) (v : ι → ℤ) :
    (∃ p m : ι → ℤ,
      (∀ i, 0 ≤ p i) ∧
      (∀ i, 0 ≤ m i) ∧
      D p ∧ D m ∧ p - m = v) ↔
      (∃ z : ι → ℤ,
        (∀ i, 0 ≤ z i) ∧
        D (fun i => max (v i) 0 + z i) ∧
        D (fun i => max (-v i) 0 + z i)) := by
  have hdecomp : ∀ a b : ℤ,
      a = max (a - b) 0 + min a b ∧
      b = max (b - a) 0 + min a b := by
    intro a b
    by_cases hab : a ≤ b
    · have h₁ : max (a - b) 0 = 0 := max_eq_right (by omega)
      have h₂ : min a b = a := min_eq_left hab
      have h₃ : max (b - a) 0 = b - a := max_eq_left (by omega)
      omega
    · have hba : b ≤ a := by omega
      have h₁ : max (a - b) 0 = a - b := max_eq_left (by omega)
      have h₂ : min a b = b := min_eq_right hba
      have h₃ : max (b - a) 0 = 0 := max_eq_right (by omega)
      omega
  have hparts : ∀ a : ℤ, max a 0 - max (-a) 0 = a := by
    intro a
    by_cases ha : 0 ≤ a
    · have h₁ : max a 0 = a := max_eq_left ha
      have h₂ : max (-a) 0 = 0 := max_eq_right (by omega)
      omega
    · have h₁ : max a 0 = 0 := max_eq_right (by omega)
      have h₂ : max (-a) 0 = -a := max_eq_left (by omega)
      omega
  constructor
  · rintro ⟨p, m, hp, hm, hDp, hDm, hpm⟩
    let z : ι → ℤ := fun i => min (p i) (m i)
    have hz : ∀ i, 0 ≤ z i := by
      intro i
      exact le_min (hp i) (hm i)
    have hplus : (fun i => max (v i) 0 + z i) = p := by
      funext i
      have hi := (hdecomp (p i) (m i)).1
      have hpm_i := congrFun hpm i
      simp only [Pi.sub_apply] at hpm_i
      rw [hpm_i] at hi
      exact hi.symm
    have hminus : (fun i => max (-v i) 0 + z i) = m := by
      funext i
      have hi := (hdecomp (p i) (m i)).2
      have hpm_i := congrFun hpm i
      simp only [Pi.sub_apply] at hpm_i
      have hdiff : m i - p i = -v i := by omega
      rw [hdiff] at hi
      exact hi.symm
    refine ⟨z, hz, ?_, ?_⟩
    · rw [hplus]
      exact hDp
    · rw [hminus]
      exact hDm
  · rintro ⟨z, hz, hDp, hDm⟩
    let p : ι → ℤ := fun i => max (v i) 0 + z i
    let m : ι → ℤ := fun i => max (-v i) 0 + z i
    have hp : ∀ i, 0 ≤ p i := by
      intro i
      exact add_nonneg (le_max_right _ _) (hz i)
    have hm : ∀ i, 0 ≤ m i := by
      intro i
      exact add_nonneg (le_max_right _ _) (hz i)
    have hpm : p - m = v := by
      funext i
      dsimp [p, m]
      have hi := hparts (v i)
      omega
    exact ⟨p, m, hp, hm, by simpa [p] using hDp, by simpa [m] using hDm, hpm⟩

/-- In a fixed completed pair, the common cancellation vector in claim 47899
is forced coordinatewise to be the minimum of the two nonnegative decks. -/
theorem commonCompletion_min_claim47899
    {ι : Type*} (p m v z : ι → ℤ)
    (hp : ∀ i, p i = max (v i) 0 + z i)
    (hm : ∀ i, m i = max (-v i) 0 + z i)
    (hpm : p - m = v) :
    z = fun i => min (p i) (m i) := by
  funext i
  have hvi := congrFun hpm i
  simp only [Pi.sub_apply] at hvi
  by_cases h : 0 ≤ v i
  · have hpv : max (v i) 0 = v i := max_eq_left h
    have hmv : max (-v i) 0 = 0 := max_eq_right (by omega)
    have hmz : m i = z i := by simpa [hmv] using hm i
    have hle : m i ≤ p i := by omega
    rw [min_eq_right hle, ← hmz]
  · have hpv : max (v i) 0 = 0 := max_eq_right (by omega)
    have hmv : max (-v i) 0 = -v i := max_eq_left (by omega)
    have hpz : p i = z i := by simpa [hpv] using hp i
    have hle : p i ≤ m i := by omega
    rw [min_eq_left hle, ← hpz]

end MathlibPlus.Combinatorics
