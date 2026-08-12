import Mathlib.Tactic

namespace MathlibPlus.Analysis

/--
Claim 48030 (R-3567#S1): an exact two-coordinate Boolean cut-area
counterexample to submodularity.  The local `mean`, `variance`, and
`areaTwo` lets are the source's recurrence
`A(u) = Var(u) + min_i E A(u_{i,σ})`, with constant tables having area zero.
The cube is represented by `Fin 2 → Bool`; the four vertices are the four
Boolean vectors, and masks `3`, `5`, `1`, and `7` are represented by `e`,
`f`, `i`, and `u` below.
-/
theorem claim48030_booleanCutArea_notSubmodularWitness :
    let mean : {n : ℕ} → ((Fin n → Bool) → ℚ) → ℚ :=
      fun {n} u =>
        (∑ x : Fin n → Bool, u x) / (Fintype.card (Fin n → Bool) : ℚ)
    let variance : {n : ℕ} → ((Fin n → Bool) → ℚ) → ℚ :=
      fun {n} u =>
        ∑ x : Fin n → Bool, (u x - mean u) ^ 2 /
          (Fintype.card (Fin n → Bool) : ℚ)
    let areaZero : ((Fin 0 → Bool) → ℚ) → ℚ := fun _ => 0
    let areaOne : ((Fin 1 → Bool) → ℚ) → ℚ :=
      fun u => variance u +
        (areaZero (fun _ => u ![false]) +
          areaZero (fun _ => u ![true])) / 2
    let areaTwo : ((Fin 2 → Bool) → ℚ) → ℚ :=
      fun u => variance u + min
        ((areaOne (fun x => u ![false, x 0]) +
            areaOne (fun x => u ![true, x 0])) / 2)
        ((areaOne (fun x => u ![x 0, false]) +
            areaOne (fun x => u ![x 0, true])) / 2)
    let indicator : Finset (Fin 2 → Bool) → (Fin 2 → Bool) → ℚ :=
      fun s x => if x ∈ s then 1 else 0
    let submodular : (Finset (Fin 2 → Bool) → ℚ) → Prop :=
      fun F => ∀ s t, F (s ∪ t) + F (s ∩ t) ≤ F s + F t
    let z : Fin 2 → Bool := ![false, false]
    let x : Fin 2 → Bool := ![true, false]
    let y : Fin 2 → Bool := ![false, true]
    let w : Fin 2 → Bool := ![true, true]
    let e : Finset (Fin 2 → Bool) := {z, x}
    let f : Finset (Fin 2 → Bool) := {z, y}
    let i : Finset (Fin 2 → Bool) := {z}
    let u : Finset (Fin 2 → Bool) := {z, x, y}
    Finset.univ = {z, x, y, w} ∧
      e ∩ f = i ∧ e ∪ f = u ∧
      areaTwo (indicator e) = (1 : ℚ) / 4 ∧
      areaTwo (indicator f) = (1 : ℚ) / 4 ∧
      areaTwo (indicator i) = (5 : ℚ) / 16 ∧
      areaTwo (indicator u) = (5 : ℚ) / 16 ∧
      (areaTwo (indicator e) +
        areaTwo (indicator f) -
        areaTwo (indicator i) -
        areaTwo (indicator u)) = -(1 : ℚ) / 8 ∧
      ¬ submodular (fun s => areaTwo (indicator s)) := by
  native_decide

end MathlibPlus.Analysis
