import Mathlib

namespace MathlibPlus.Analysis.Claim47470

/-!
Formalization of admitted claim 47470.  The sample space is the finite product
`Bool × Fin 12`, with Boolean signs represented by `1` and `-1` in `ℚ` and
with the flipped coordinate indexed by the second component.  Conditional
variance is computed by the exact finite posterior fibers of the first `r`
coordinates, so the displayed area is a kernel-checked rational certificate.
The source's phrase about adaptive orders is represented by the explicit
finite exchangeability equation below rather than by an unprovided decision-
tree interface.
-/

theorem z_identity :
    let Ω := Bool × Fin 12
    let y : Ω → ℚ := fun ω => if ω.1 then 1 else -1
    let xb : Ω → Fin 12 → Bool := fun ω i =>
      if i = ω.2 then !ω.1 else ω.1
    let x : Ω → Fin 12 → ℚ := fun ω i => if xb ω i then 1 else -1
    let p : Fin 12 → ℚ := fun _ => 1 / 12
    let z : Ω → ℚ := fun ω => ∑ i : Fin 12, p i * x ω i
    ∀ ω : Ω, z ω = (5 / 6 : ℚ) * y ω := by
  native_decide

theorem exchangeability :
    let Ω := Bool × Fin 12
    let xb : Ω → Fin 12 → Bool := fun ω i =>
      if i = ω.2 then !ω.1 else ω.1
    ∀ σ : Equiv.Perm (Fin 12), ∀ v : Fin 12 → Bool,
      (∑ ω : Ω, if (fun i => xb ω i) = v then (1 : ℚ) else 0) =
        ∑ ω : Ω, if (fun i => xb ω (σ i)) = v then 1 else 0 := by
  dsimp
  intro σ v
  let e : (Bool × Fin 12) ≃ (Bool × Fin 12) :=
    Equiv.prodCongr (Equiv.refl Bool) σ
  apply Fintype.sum_equiv e
  intro ω
  have hvec : (fun i =>
      (if σ i = (e ω).2 then !(e ω).1 else (e ω).1)) =
      (fun i => if i = ω.2 then !ω.1 else ω.1) := by
    funext i
    change (if σ i = σ ω.2 then !ω.1 else ω.1) =
      (if i = ω.2 then !ω.1 else ω.1)
    by_cases h : i = ω.2
    · subst i
      simp
    · have hσ : σ i ≠ σ ω.2 := by
        intro h'
        exact h (σ.injective h')
      simp [h, hσ]
  simpa only [hvec]

theorem posterior_area :
    let Ω := Bool × Fin 12
    let y : Ω → ℚ := fun ω => if ω.1 then 1 else -1
    let xb : Ω → Fin 12 → Bool := fun ω i =>
      if i = ω.2 then !ω.1 else ω.1
    let x : Ω → Fin 12 → ℚ := fun ω i => if xb ω i then 1 else -1
    let p : Fin 12 → ℚ := fun _ => 1 / 12
    let z : Ω → ℚ := fun ω => ∑ i : Fin 12, p i * x ω i
    let idx : ∀ r : Fin 12, Fin r.val → Fin 12 := fun r i =>
      ⟨i.val, Nat.lt_trans i.isLt r.isLt⟩
    let obs : ∀ r : Fin 12, Ω → (Fin r.val → Bool) :=
      fun r ω i => xb ω (idx r i)
    let sameObs : ∀ r : Fin 12, Ω → Ω → Prop :=
      fun r ω ω' => ∀ i : Fin r.val, obs r ω i = obs r ω' i
    let count : ∀ r : Fin 12, Ω → ℚ := fun r ω =>
      ∑ ω' : Ω, if sameObs r ω ω' then 1 else 0
    let mean : ∀ r : Fin 12, Ω → ℚ := fun r ω =>
      (∑ ω' : Ω, if sameObs r ω ω' then z ω' else 0) / count r ω
    let condVar : ∀ r : Fin 12, Ω → ℚ := fun r ω =>
      (∑ ω' : Ω,
        if sameObs r ω ω' then (z ω' - mean r ω) ^ 2 else 0) / count r ω
    let area : ℚ := ∑ r : Fin 12, (∑ ω : Ω, condVar r ω) / 24
    area = (1325 : ℚ) / 1296 ∧ 1 < area := by
  native_decide

end MathlibPlus.Analysis.Claim47470
