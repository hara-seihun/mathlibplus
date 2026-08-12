import Mathlib

set_option maxHeartbeats 1000000

namespace MathlibPlus.Algebra.CoordinateLineNormalization

abbrev K := ZMod 3

private lemma zmod3_cases (a : K) : a = 0 ∨ a = 1 ∨ a = -1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · right; right
    change (2 : K) = -1
    decide

private lemma normalized_ext
    {V X : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup X] [Module K X]
    (b : Module.Basis (Fin 2) K X)
    (g₁ g₂ : X → V)
    (hodd₁ : ∀ x, g₁ (-x) = -g₁ x)
    (hline₁ : ∀ t : K, g₁ (t • b 0) = 0 ∧ g₁ (t • b 1) = 0)
    (hodd₂ : ∀ x, g₂ (-x) = -g₂ x)
    (hline₂ : ∀ t : K, g₂ (t • b 0) = 0 ∧ g₂ (t • b 1) = 0)
    (hA : g₁ (b 0 + b 1) = g₂ (b 0 + b 1))
    (hB : g₁ (b 0 - b 1) = g₂ (b 0 - b 1)) :
    g₁ = g₂ := by
  funext x
  have hx : x = (b.repr x 0) • b 0 + (b.repr x 1) • b 1 := by
    calc
      x = ∑ i, (b.repr x) i • b i := (b.sum_repr x).symm
      _ = (b.repr x 0) • b 0 + (b.repr x 1) • b 1 := by
        rw [Fin.sum_univ_two]
  rw [hx]
  let a : K := b.repr x 0
  let c : K := b.repr x 1
  have ha : a = 0 ∨ a = 1 ∨ a = -1 := zmod3_cases a
  have hc : c = 0 ∨ c = 1 ∨ c = -1 := zmod3_cases c
  have hzero₁ : g₁ 0 = 0 := by simpa using (hline₁ 0).1
  have hzero₂ : g₂ 0 = 0 := by simpa using (hline₂ 0).1
  have haxis₁0 : g₁ (b 0) = 0 := by simpa using (hline₁ 1).1
  have haxis₂0 : g₂ (b 0) = 0 := by simpa using (hline₂ 1).1
  have haxis₁1 : g₁ (b 1) = 0 := by simpa using (hline₁ 1).2
  have haxis₂1 : g₂ (b 1) = 0 := by simpa using (hline₂ 1).2
  have hAneg : g₁ (-(b 0 + b 1)) = g₂ (-(b 0 + b 1)) := by
    rw [hodd₁, hodd₂, hA]
  have hBswap : g₁ (b 1 - b 0) = g₂ (b 1 - b 0) := by
    rw [show b 1 - b 0 = -(b 0 - b 1) by abel, hodd₁, hodd₂, hB]
  have hAneg' : g₁ (-b 0 + -b 1) = g₂ (-b 0 + -b 1) := by
    simpa [add_comm, add_left_comm, add_assoc] using hAneg
  have hBswap' : g₁ (b 1 + -b 0) = g₂ (b 1 + -b 0) := by
    simpa [sub_eq_add_neg] using hBswap
  rcases ha with ha | ha | ha <;>
    rcases hc with hc | hc | hc <;>
      simp_all [a, c, ha, hc, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

private lemma line_zero
    {V X : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup X] [Module K X]
    (b : Module.Basis (Fin 2) K X) (f : X → V)
    (hf : ∀ x, f (-x) = -f x)
    (ell : X →ₗ[K] V)
    (h0 : ell (b 0) = -f (b 0))
    (h1 : ell (b 1) = -f (b 1)) :
    ∀ t : K, (f (t • b 0) + ell (t • b 0) = 0) ∧
      (f (t • b 1) + ell (t • b 1) = 0) := by
  intro t
  have hf0 : f 0 = 0 := by
    have hodd0 : f 0 = -f 0 := by simpa using hf 0
    have htwo : (2 : K) • f 0 = 0 := by
      calc
        (2 : K) • f 0 = f 0 + f 0 := by rw [two_smul]
        _ = f 0 + (-f 0) := congrArg (fun y => f 0 + y) hodd0
        _ = 0 := add_neg_cancel _
    have htwo_ne : (2 : K) ≠ 0 := by
      intro h
      have hd : (3 : ℤ) ∣ (0 - 2) :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub 2 0 3).mp h
      norm_num at hd
    exact (smul_eq_zero.mp htwo).resolve_left htwo_ne
  have ht : t = 0 ∨ t = 1 ∨ t = -1 := zmod3_cases t
  rcases ht with rfl | rfl | rfl
  · simp [hf0]
  · constructor <;> simp [h0, h1]
  · rw [neg_smul, neg_smul]
    constructor <;> simp [hf, h0, h1]

private lemma ell_unique
    {V X : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup X] [Module K X]
    (b : Module.Basis (Fin 2) K X) (f : X → V) :
    ∃! ell : X →ₗ[K] V,
      ell (b 0) = -f (b 0) ∧ ell (b 1) = -f (b 1) := by
  let ell : X →ₗ[K] V := (b.constr K) (fun i => -f (b i))
  have h0 : ell (b 0) = -f (b 0) := by
    dsimp [ell]
    exact b.constr_basis K (fun i => -f (b i)) 0
  have h1 : ell (b 1) = -f (b 1) := by
    dsimp [ell]
    exact b.constr_basis K (fun i => -f (b i)) 1
  refine ⟨ell, ⟨h0, h1⟩, ?_⟩
  intro ell' h
  apply LinearMap.ext
  intro x
  have hx : x = (b.repr x 0) • b 0 + (b.repr x 1) • b 1 := by
    calc
      x = ∑ i, (b.repr x) i • b i := (b.sum_repr x).symm
      _ = (b.repr x 0) • b 0 + (b.repr x 1) • b 1 := by
        rw [Fin.sum_univ_two]
  calc
    ell' x = ell' ((b.repr x 0) • b 0 + (b.repr x 1) • b 1) :=
      congrArg ell' hx
    _ = (b.repr x 0) • (-f (b 0)) + (b.repr x 1) • (-f (b 1)) := by
      rw [map_add, map_smul, map_smul, h.1, h.2]
    _ = ell ((b.repr x 0) • b 0 + (b.repr x 1) • b 1) := by
      rw [map_add, map_smul, map_smul]
      rw [h0, h1]
    _ = ell x := (congrArg ell hx).symm

/-- Claim 28868.  In the source's ternary two-dimensional setting, choose a basis
`b 0, b 1` and an odd map `f`.  The unique linear correction takes the values
`-f (b i)` on the basis vectors; the corrected map vanishes on both coordinate
lines, and odd coordinate-line-normalized maps are determined by their values at
`b 0 + b 1` and `b 0 - b 1`. -/
theorem coordinateLineNormalization_claim28868
    {V X : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup X] [Module K X]
    (b : Module.Basis (Fin 2) K X) (f : X → V)
    (hf : ∀ x, f (-x) = -f x) :
    ∃! ell : X →ₗ[K] V,
      ell (b 0) = -f (b 0) ∧ ell (b 1) = -f (b 1) ∧
      (let g : X → V := fun x => f x + ell x
       (∀ x, g (-x) = -g x) ∧
       (∀ t : K, g (t • b 0) = 0 ∧ g (t • b 1) = 0) ∧
       (∀ g₁ g₂ : X → V,
        (∀ x, g₁ (-x) = -g₁ x) →
        (∀ t : K, g₁ (t • b 0) = 0 ∧ g₁ (t • b 1) = 0) →
        (∀ x, g₂ (-x) = -g₂ x) →
        (∀ t : K, g₂ (t • b 0) = 0 ∧ g₂ (t • b 1) = 0) →
        g₁ (b 0 + b 1) = g₂ (b 0 + b 1) →
        g₁ (b 0 - b 1) = g₂ (b 0 - b 1) →
        g₁ = g₂)) := by
  obtain ⟨ell, hell, hell_unique⟩ := ell_unique b f
  refine ⟨ell, ?_, ?_⟩
  · refine ⟨hell.1, hell.2, ?_⟩
    dsimp
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rw [hf x, map_neg]
      abel
    · exact line_zero b f hf ell hell.1 hell.2
    · intro g₁ g₂ hodd₁ hline₁ hodd₂ hline₂ hA hB
      exact normalized_ext b g₁ g₂ hodd₁ hline₁ hodd₂ hline₂ hA hB
  · intro ell' h
    exact hell_unique ell' ⟨h.1, h.2.1⟩

end MathlibPlus.Algebra.CoordinateLineNormalization
