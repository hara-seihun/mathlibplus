import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Abel

namespace MathlibPlus.Open.GraphTheory

open scoped Pointwise

noncomputable section

/--
A normalized prime-central shear has one additive shadow that agrees on every
quiet direction and has the same image on every compatible connection set.
The shadow is quantified before the compatible set, retaining the simultaneous
form of the claim.
-/
def primeCentralShearUniversalLinearShadow : Prop :=
  ∀ (p n : ℕ), p.Prime →
    ∀ f : (Fin n → ZMod p) → ZMod p, f 0 = 0 →
      ∃ ell : (Fin n → ZMod p) →+ ZMod p,
        (∀ d, (∀ x, f (x + d) - f x - f d = 0) → ell d = f d) ∧
          ∀ S : Set ((Fin n → ZMod p) × ZMod p),
            (∀ x, (fun q : (Fin n → ZMod p) × ZMod p =>
              (q.1, q.2 + (f (x + q.1) - f x - f q.1))) '' S = S) →
              (fun q => (q.1, q.2 + ell q.1)) '' S =
                (fun q => (q.1, q.2 + f q.1)) '' S

end

end MathlibPlus.Open.GraphTheory

namespace MathlibPlus.GraphTheory

noncomputable section

private abbrev primeCentralShearDerivative {p n : ℕ}
    (f : (Fin n → ZMod p) → ZMod p) (x d : Fin n → ZMod p) : ZMod p :=
  f (x + d) - f x - f d

private abbrev primeCentralShearQuiet {p n : ℕ}
    (f : (Fin n → ZMod p) → ZMod p) (d : Fin n → ZMod p) : Prop :=
  ∀ x, primeCentralShearDerivative f x d = 0

private abbrev primeCentralShearDerivativeTranslation {p n : ℕ}
    (f : (Fin n → ZMod p) → ZMod p) (x : Fin n → ZMod p) :
    (Fin n → ZMod p) × ZMod p → (Fin n → ZMod p) × ZMod p :=
  fun q => (q.1, q.2 + primeCentralShearDerivative f x q.1)

private abbrev primeCentralShearCompatible {p n : ℕ}
    (f : (Fin n → ZMod p) → ZMod p)
    (S : Set ((Fin n → ZMod p) × ZMod p)) : Prop :=
  ∀ x, (primeCentralShearDerivativeTranslation f x) '' S = S

private abbrev primeCentralShearImage {p n : ℕ}
    (g : (Fin n → ZMod p) → ZMod p)
    (S : Set ((Fin n → ZMod p) × ZMod p)) :
    Set ((Fin n → ZMod p) × ZMod p) :=
  (fun q => (q.1, q.2 + g q.1)) '' S

private theorem quiet_eq {p n : ℕ}
    {f : (Fin n → ZMod p) → ZMod p} {d : Fin n → ZMod p}
    (hd : primeCentralShearQuiet f d) (x : Fin n → ZMod p) :
    f (x + d) = f x + f d := by
  have h := hd x
  dsimp [primeCentralShearDerivative] at h
  have h' : f (x + d) - (f x + f d) = 0 := by
    convert h using 1; abel
  exact sub_eq_zero.mp h'

private theorem quiet_zero {p n : ℕ}
    {f : (Fin n → ZMod p) → ZMod p} (hf : f 0 = 0) :
    primeCentralShearQuiet f 0 := by
  intro x
  simp [primeCentralShearDerivative, hf]

private theorem quiet_add {p n : ℕ}
    {f : (Fin n → ZMod p) → ZMod p} {d e : Fin n → ZMod p}
    (hd : primeCentralShearQuiet f d) (he : primeCentralShearQuiet f e) :
    primeCentralShearQuiet f (d + e) := by
  intro x
  have hxe : f ((x + d) + e) = f (x + d) + f e := quiet_eq he (x + d)
  have hxd : f (x + d) = f x + f d := quiet_eq hd x
  have hde : f (d + e) = f d + f e := by
    simpa [add_comm] using (quiet_eq hd e)
  dsimp [primeCentralShearDerivative]
  rw [show x + (d + e) = (x + d) + e by abel, hxe, hxd, hde]
  abel

private theorem quiet_neg {p n : ℕ}
    {f : (Fin n → ZMod p) → ZMod p} (hf : f 0 = 0)
    {d : Fin n → ZMod p} (hd : primeCentralShearQuiet f d) :
    primeCentralShearQuiet f (-d) := by
  intro x
  have hfd : f (-d) = -f d := by
    have h := quiet_eq hd (-d)
    apply eq_neg_of_add_eq_zero_left
    simpa [hf] using h.symm
  have hxd : f (x + (-d)) = f x - f d := by
    have h := quiet_eq hd (x + (-d))
    apply (eq_sub_iff_add_eq).2
    simpa [add_assoc] using h.symm
  dsimp [primeCentralShearDerivative]
  rw [hxd, hfd]
  abel

private def quietAddSubgroup {p n : ℕ}
    (f : (Fin n → ZMod p) → ZMod p) (hf : f 0 = 0) :
    AddSubgroup (Fin n → ZMod p) :=
  { carrier := {d | primeCentralShearQuiet f d}
    zero_mem' := quiet_zero hf
    add_mem' := by
      intro d e hd he
      exact quiet_add hd he
    neg_mem' := by
      intro d hd
      exact quiet_neg hf hd }

private theorem quiet_extension {p n : ℕ} (hp : p.Prime)
    (f : (Fin n → ZMod p) → ZMod p) (hf : f 0 = 0) :
    ∃ ell : (Fin n → ZMod p) →+ ZMod p,
      ∀ d, primeCentralShearQuiet f d → ell d = f d := by
  letI : Fact p.Prime := ⟨hp⟩
  let K₀ := quietAddSubgroup f hf
  let K : Submodule (ZMod p) (Fin n → ZMod p) :=
    AddSubgroup.toZModSubmodule p K₀
  let r : K →+ ZMod p :=
    { toFun := fun d => f d
      map_zero' := by simpa using hf
      map_add' := by
        intro d e
        exact quiet_eq e.property d }
  let rlin : K →ₗ[ZMod p] ZMod p := r.toZModLinearMap p
  obtain ⟨L, hL⟩ := LinearMap.exists_extend rlin
  let ell : (Fin n → ZMod p) →+ ZMod p := L.toAddMonoidHom
  refine ⟨ell, ?_⟩
  intro d hd
  let kd : K := ⟨d, hd⟩
  have hLd := congrArg (fun g : K →ₗ[ZMod p] ZMod p => g kd) hL
  simpa [ell, rlin, r, kd, K, K₀] using hLd

private theorem compatible_nsmul {p n : ℕ}
    {f : (Fin n → ZMod p) → ZMod p}
    {S : Set ((Fin n → ZMod p) × ZMod p)}
    (hS : primeCentralShearCompatible f S)
    (x : Fin n → ZMod p) (d : Fin n → ZMod p) (z : ZMod p)
    (hz : (d, z) ∈ S) (k : ℕ) :
    (d, z + k • primeCentralShearDerivative f x d) ∈ S := by
  induction k with
  | zero => simpa using hz
  | succ k ih =>
      have ht := hS x
      rw [← ht]
      refine ⟨(d, z + k • primeCentralShearDerivative f x d), ih, ?_⟩
      dsimp [primeCentralShearDerivativeTranslation]
      congr 1
      rw [add_nsmul]
      abel

private theorem compatible_translate_all {p n : ℕ} (hp : p.Prime)
    {f : (Fin n → ZMod p) → ZMod p}
    {S : Set ((Fin n → ZMod p) × ZMod p)}
    (hS : primeCentralShearCompatible f S)
    {d : Fin n → ZMod p} {z : ZMod p} (hz : (d, z) ∈ S)
    {x : Fin n → ZMod p}
    (ha : primeCentralShearDerivative f x d ≠ 0) (c : ZMod p) :
    (d, z + c) ∈ S := by
  letI : Fact p.Prime := ⟨hp⟩
  let a := primeCentralShearDerivative f x d
  let u : ZMod p := c / a
  let k : ℕ := u.val
  have hka : k • a = c := by
    calc
      k • a = (k : ZMod p) * a := nsmul_eq_mul k a
      _ = u * a := by rw [ZMod.natCast_zmod_val]
      _ = c := by dsimp [u]; exact div_mul_cancel₀ c ha
  have hk := compatible_nsmul hS x d z hz k
  simpa [a, hka] using hk

/-- The quiet-direction extension and prime-order fibre saturation prove the registry claim. -/
theorem primeCentralShearUniversalLinearShadow_proved :
    MathlibPlus.Open.GraphTheory.primeCentralShearUniversalLinearShadow := by
  intro p n hp f hf
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ell, hell⟩ := quiet_extension hp f hf
  refine ⟨ell, ?_, ?_⟩
  · intro d hd
    apply hell d
    simpa [primeCentralShearQuiet, primeCentralShearDerivative] using hd
  · intro S hS
    have hS' : primeCentralShearCompatible f S := by
      simpa [primeCentralShearCompatible, primeCentralShearDerivativeTranslation,
        primeCentralShearDerivative] using hS
    change primeCentralShearImage ell S = primeCentralShearImage f S
    apply Set.Subset.antisymm
    · intro q hq
      change q ∈ (fun q : (Fin n → ZMod p) × ZMod p => (q.1, q.2 + ell q.1)) '' S at hq
      rcases hq with ⟨⟨d, z⟩, hz, rfl⟩
      by_cases hd : primeCentralShearQuiet f d
      · refine ⟨(d, z), hz, ?_⟩
        dsimp [primeCentralShearImage]
        rw [hell d hd]
      · have hnonquiet : ∃ x, primeCentralShearDerivative f x d ≠ 0 := by
          by_contra h
          apply hd
          intro x
          by_contra hx
          exact h ⟨x, hx⟩
        obtain ⟨x, hx⟩ := hnonquiet
        have hz' := compatible_translate_all hp hS' hz hx (ell d - f d)
        refine ⟨(d, z + (ell d - f d)), hz', ?_⟩
        dsimp [primeCentralShearImage]
        congr 1
        abel
    · intro q hq
      change q ∈ (fun q : (Fin n → ZMod p) × ZMod p => (q.1, q.2 + f q.1)) '' S at hq
      rcases hq with ⟨⟨d, z⟩, hz, rfl⟩
      by_cases hd : primeCentralShearQuiet f d
      · refine ⟨(d, z), hz, ?_⟩
        dsimp [primeCentralShearImage]
        rw [hell d hd]
      · have hnonquiet : ∃ x, primeCentralShearDerivative f x d ≠ 0 := by
          by_contra h
          apply hd
          intro x
          by_contra hx
          exact h ⟨x, hx⟩
        obtain ⟨x, hx⟩ := hnonquiet
        have hz' := compatible_translate_all hp hS' hz hx (f d - ell d)
        refine ⟨(d, z + (f d - ell d)), hz', ?_⟩
        dsimp [primeCentralShearImage]
        congr 1
        abel

end

end MathlibPlus.GraphTheory
