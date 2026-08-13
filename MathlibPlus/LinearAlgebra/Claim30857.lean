import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim30857

variable {𝔽 W V : Type*}
variable [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W]
  [AddCommGroup V] [Module 𝔽 V]

/-- For a nonzero fibre normal, a triangular shear maps the affine hyperplane
`a w + b v = t` to an affine hyperplane exactly when the scalar shadow `b ∘ c`
is affine. -/
theorem image_affine_hyperplane_iff_scalar_shadow_claim30857
    [Fintype 𝔽] [FiniteDimensional 𝔽 W] [FiniteDimensional 𝔽 V]
    (c : W → V) (a : W →ₗ[𝔽] 𝔽) (b : V →ₗ[𝔽] 𝔽) (t : 𝔽)
    (hb : b ≠ 0) :
    (let H : Set (W × V) := {x | a x.1 + b x.2 = t}
     let q : W × V → W × V := fun x => (x.1, x.2 + c x.1)
     ((∃ a' : W →ₗ[𝔽] 𝔽, ∃ b' : V →ₗ[𝔽] 𝔽, ∃ t' : 𝔽,
          (a' ≠ 0 ∨ b' ≠ 0) ∧
            q '' H = {x | a' x.1 + b' x.2 = t'}) ↔
       ∃ a' : W →ₗ[𝔽] 𝔽, ∃ t' : 𝔽,
         ∀ w : W, b (c w) = (t' - t) + (a w - a' w))) := by
  dsimp
  have hb_exists : ∃ v₀ : V, b v₀ ≠ 0 := by
    by_contra h
    apply hb
    ext v
    by_contra hv
    exact h ⟨v, hv⟩
  obtain ⟨v₀, hv₀⟩ := hb_exists
  have hsurj : Function.Surjective b := by
    intro y
    refine ⟨(y / b v₀) • v₀, ?_⟩
    rw [map_smul]
    exact div_mul_cancel₀ y hv₀
  constructor
  · rintro ⟨a', b', t', hnonzero, hEq⟩
    have hker : LinearMap.ker b = LinearMap.ker b' := by
      apply le_antisymm
      · intro u hu
        change b' u = 0
        let v : V := (t / b v₀) • v₀
        have hv : b v = t := by
          dsimp [v]
          rw [map_smul]
          exact div_mul_cancel₀ t hv₀
        have hsource : (0, v) ∈ {x : W × V | a x.1 + b x.2 = t} := by
          dsimp
          simp only [map_zero, zero_add, hv]
        have hsource' : (0, v + u) ∈
            {x : W × V | a x.1 + b x.2 = t} := by
          dsimp
          rw [map_zero, zero_add, map_add, hv]
          change t + b u = t
          rw [hu]
          simp
        have himage := hEq ▸ (show (0, v + c 0) ∈
            (fun x : W × V => (x.1, x.2 + c x.1)) ''
              {x : W × V | a x.1 + b x.2 = t} from ⟨(0, v), hsource, rfl⟩)
        have himage' := hEq ▸ (show (0, (v + u) + c 0) ∈
            (fun x : W × V => (x.1, x.2 + c x.1)) ''
              {x : W × V | a x.1 + b x.2 = t} from
                ⟨(0, v + u), hsource', rfl⟩)
        change a' 0 + b' (v + c 0) = t' at himage
        change a' 0 + b' ((v + u) + c 0) = t' at himage'
        simp only [map_zero, map_add] at himage himage'
        linear_combination himage' - himage
      · intro u hu
        change b' u = 0 at hu
        change b u = 0
        let v : V := (t / b v₀) • v₀
        have hv : b v = t := by
          dsimp [v]
          rw [map_smul]
          exact div_mul_cancel₀ t hv₀
        have hsource : (0, v) ∈ {x : W × V | a x.1 + b x.2 = t} := by
          dsimp
          simp only [map_zero, zero_add, hv]
        have himage0 := hEq ▸ (show (0, v + c 0) ∈
            (fun x : W × V => (x.1, x.2 + c x.1)) ''
              {x : W × V | a x.1 + b x.2 = t} from ⟨(0, v), hsource, rfl⟩)
        have htarget : (0, (v + c 0) + u) ∈
            {x : W × V | a' x.1 + b' x.2 = t'} := by
          change a' 0 + b' ((v + c 0) + u) = t'
          change a' 0 + b' (v + c 0) = t' at himage0
          simp only [map_zero, map_add] at himage0 ⊢
          simpa [hu] using himage0
        obtain ⟨z, hz, hqz⟩ := hEq.symm ▸ htarget
        change a z.1 + b z.2 = t at hz
        have hfirst : z.1 = 0 := congrArg Prod.fst hqz
        have hsecond : z.2 + c z.1 = (v + c 0) + u := congrArg Prod.snd hqz
        rw [hfirst] at hsecond
        have hzu : z.2 = v + u := by
          calc
            z.2 = (z.2 + c 0) - c 0 := by abel
            _ = ((v + c 0) + u) - c 0 := by rw [hsecond]
            _ = v + u := by abel
        rw [hfirst, hzu, map_add] at hz
        have hvsource : a 0 + b v = t := by
          simp only [map_zero, zero_add, hv]
        linear_combination hz - hvsource
    let lam : 𝔽 := b' v₀ / b v₀
    have hb'smul : b' = lam • b := by
      ext v
      have hker_mem : v - (b v / b v₀) • v₀ ∈ LinearMap.ker b := by
        change b (v - (b v / b v₀) • v₀) = 0
        rw [map_sub, map_smul, smul_eq_mul]
        exact sub_eq_zero.mpr (div_mul_cancel₀ (b v) hv₀).symm
      rw [hker] at hker_mem
      change b' (v - (b v / b v₀) • v₀) = 0 at hker_mem
      rw [map_sub, map_smul, smul_eq_mul] at hker_mem
      have hrel : b' v = (b v / b v₀) * b' v₀ :=
        sub_eq_zero.mp hker_mem
      change b' v = lam * b v
      dsimp [lam]
      calc
        b' v = (b v / b v₀) * b' v₀ := hrel
        _ = (b' v₀ / b v₀) * b v := by field_simp [hv₀]
    have hlam : lam ≠ 0 := by
      intro hlam0
      have hb'zero : b' = 0 := by
        rw [hb'smul, hlam0]
        simp
      have hvker : v₀ ∈ LinearMap.ker b' := by
        rw [hb'zero]
        simp
      have hvker' : v₀ ∈ LinearMap.ker b := hker.symm ▸ hvker
      exact hv₀ (show b v₀ = 0 from hvker')
    let a'' : W →ₗ[𝔽] 𝔽 := lam⁻¹ • a'
    let t'' : 𝔽 := t' / lam
    refine ⟨a'', t'', ?_⟩
    intro w
    let v : V := ((t - a w) / b v₀) • v₀
    have hv : b v = t - a w := by
      dsimp [v]
      rw [map_smul]
      exact div_mul_cancel₀ (t - a w) hv₀
    have hsource : a w + b v = t := by rw [hv]; ring
    have htarget : a' w + b' (v + c w) = t' := by
      have hmem : (w, v) ∈ {x : W × V | a x.1 + b x.2 = t} := hsource
      have himage : (w, v + c w) ∈
          (fun x : W × V => (x.1, x.2 + c x.1)) ''
            {x : W × V | a x.1 + b x.2 = t} := by
        exact ⟨(w, v), hmem, rfl⟩
      have himage' := hEq ▸ himage
      change a' w + b' (v + c w) = t' at himage'
      exact himage'
    have hb'point (z : V) : b' z = lam * b z := by
      rw [hb'smul]
      rfl
    rw [map_add, hb'point, hb'point, hv] at htarget
    dsimp [a'', t'']
    field_simp [hlam] at htarget ⊢
    linear_combination htarget
  · rintro ⟨a', t', hshadow⟩
    refine ⟨a', b, t', Or.inr hb, ?_⟩
    ext x
    constructor
    · rintro ⟨y, hyH, rfl⟩
      change a' y.1 + b (y.2 + c y.1) = t'
      have hsource : a y.1 + b y.2 = t := hyH
      have hshadow' := hshadow y.1
      rw [map_add]
      linear_combination hsource + hshadow'
    · intro hx
      change a' x.1 + b x.2 = t' at hx
      refine ⟨(x.1, x.2 - c x.1), ?_, ?_⟩
      · change a x.1 + b (x.2 - c x.1) = t
        have hshadow' := hshadow x.1
        rw [map_sub]
        linear_combination hx - hshadow'
      · apply Prod.ext
        · rfl
        · simp

end MathlibPlus.LinearAlgebra.Claim30857
