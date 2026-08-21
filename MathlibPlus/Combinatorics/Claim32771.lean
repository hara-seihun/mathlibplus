-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Combinatorics

/--
Claim 32771.  Two explicit coordinate-dependent edge systems on `Q₃` have
identical coordinate densities and hence identical thresholded basis-direction
Cayley projections, while only the second contains a coordinate square.
The oriented edge indicators are evaluated on the endpoint whose indicated
coordinate is `false`; the square condition below is the exact four-edge
condition for this orientation.
-/
theorem claim32771_coordinateDensityProjectionCounterexample :
    let V := Fin 3 → Bool
    let flip : V → Fin 3 → V := fun x i j => if i = j then !x i else x j
    let good : Fin 3 → V → Bool := fun i x =>
      if i = 0 then !x 2 else if i = 1 then x 2 else false
    let bad : Fin 3 → V → Bool := fun i x =>
      if i = 0 then !x 2 else if i = 1 then !x 2 else false
    let density : (Fin 3 → V → Bool) → Fin 3 → ℚ := fun f i =>
      ((Finset.univ.filter (fun x : V => x i = false ∧ f i x = true)).card : ℚ) /
        ((Finset.univ.filter (fun x : V => x i = false)).card : ℚ)
    let unit : Fin 3 → (Fin 3 → ZMod 2) := fun i j =>
      if i = j then 1 else 0
    let thresholdSet : (Fin 3 → V → Bool) → ℝ → Finset (Fin 3 → ZMod 2) :=
      fun f τ => (Finset.univ.filter (fun i => (density f i : ℝ) ≥ τ)).image unit
    let squareFree : (Fin 3 → V → Bool) → Prop := fun f =>
      ∀ i j : Fin 3, i ≠ j → ∀ x : V,
        x i = false → x j = false →
          ¬(f i x = true ∧ f i (flip x j) = true ∧
            f j x = true ∧ f j (flip x i) = true)
    let x₀ : V := fun _ => false
    let badSquare : Prop :=
      bad 0 x₀ = true ∧ bad 0 (flip x₀ 1) = true ∧
        bad 1 x₀ = true ∧ bad 1 (flip x₀ 0) = true
    (∀ i : Fin 3, density good i = density bad i) ∧
      density good 0 = 1 / 2 ∧ density good 1 = 1 / 2 ∧ density good 2 = 0 ∧
      density bad 0 = 1 / 2 ∧ density bad 1 = 1 / 2 ∧ density bad 2 = 0 ∧
      (∀ τ : ℝ, thresholdSet good τ = thresholdSet bad τ) ∧
      squareFree good ∧ badSquare ∧ ¬squareFree bad := by
  classical
  let V := Fin 3 → Bool
  let flip : V → Fin 3 → V := fun x i j => if i = j then !x i else x j
  let good : Fin 3 → V → Bool := fun i x =>
    if i = 0 then !x 2 else if i = 1 then x 2 else false
  let bad : Fin 3 → V → Bool := fun i x =>
    if i = 0 then !x 2 else if i = 1 then !x 2 else false
  let density : (Fin 3 → V → Bool) → Fin 3 → ℚ := fun f i =>
    ((Finset.univ.filter (fun x : V => x i = false ∧ f i x = true)).card : ℚ) /
      ((Finset.univ.filter (fun x : V => x i = false)).card : ℚ)
  let unit : Fin 3 → (Fin 3 → ZMod 2) := fun i j =>
    if i = j then 1 else 0
  let thresholdSet : (Fin 3 → V → Bool) → ℝ → Finset (Fin 3 → ZMod 2) :=
    fun f τ => (Finset.univ.filter (fun i => (density f i : ℝ) ≥ τ)).image unit
  let squareFree : (Fin 3 → V → Bool) → Prop := fun f =>
    ∀ i j : Fin 3, i ≠ j → ∀ x : V,
      x i = false → x j = false →
        ¬(f i x = true ∧ f i (flip x j) = true ∧
          f j x = true ∧ f j (flip x i) = true)
  let x₀ : V := fun _ => false
  let badSquare : Prop :=
    bad 0 x₀ = true ∧ bad 0 (flip x₀ 1) = true ∧
      bad 1 x₀ = true ∧ bad 1 (flip x₀ 0) = true
  change
    (∀ i : Fin 3, density good i = density bad i) ∧
      density good 0 = 1 / 2 ∧ density good 1 = 1 / 2 ∧ density good 2 = 0 ∧
      density bad 0 = 1 / 2 ∧ density bad 1 = 1 / 2 ∧ density bad 2 = 0 ∧
      (∀ τ : ℝ, thresholdSet good τ = thresholdSet bad τ) ∧
      squareFree good ∧ badSquare ∧ ¬squareFree bad
  have hdens : ∀ i : Fin 3, density good i = density bad i := by
    native_decide
  have hvals : density good 0 = 1 / 2 ∧ density good 1 = 1 / 2 ∧ density good 2 = 0 := by
    native_decide
  have hvalsBad : density bad 0 = 1 / 2 ∧ density bad 1 = 1 / 2 ∧ density bad 2 = 0 := by
    native_decide
  have hgood : squareFree good := by
    native_decide
  have hbadSquare : badSquare := by
    native_decide
  have hbad : ¬squareFree bad := by
    native_decide
  refine ⟨hdens, hvals.1, hvals.2.1, hvals.2.2, hvalsBad.1, hvalsBad.2.1, hvalsBad.2.2, ?_, hgood, hbadSquare, hbad⟩
  intro τ
  unfold thresholdSet
  exact congrArg (fun s : Finset (Fin 3) => s.image unit) (Finset.filter_congr fun i hi => by rw [hdens i])

end MathlibPlus.Combinatorics
