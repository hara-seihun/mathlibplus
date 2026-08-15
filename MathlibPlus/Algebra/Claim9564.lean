import Mathlib

namespace MathlibPlus.Algebra.Claim9564

abbrev R := LaurentPolynomial ℚ
abbrev K := FractionRing R

noncomputable def negInt : ℤ →+ ℤ :=
  { toFun := Neg.neg
    map_zero' := neg_zero
    map_add' := by intro a b; exact neg_add _ _ }

noncomputable def barR : R →+* R :=
  AddMonoidAlgebra.mapDomainRingHom ℚ negInt

lemma bar_T (n : ℤ) : barR (LaurentPolynomial.T n) = LaurentPolynomial.T (-n) := by
  change AddMonoidAlgebra.mapDomain (negInt : ℤ → ℤ) (AddMonoidAlgebra.single n 1) =
    AddMonoidAlgebra.single (-n) 1
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

lemma bar_C (a : ℚ) : barR (LaurentPolynomial.C a) = LaurentPolynomial.C a := by
  change AddMonoidAlgebra.mapDomain (negInt : ℤ → ℤ) (AddMonoidAlgebra.single 0 a) =
    AddMonoidAlgebra.single 0 a
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

lemma bar_involutive : Function.Involutive barR := by
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | C_mul_T n a =>
      simp only [map_mul, bar_C, bar_T]
      simp

lemma bar_injective : Function.Injective barR := by
  intro x y h
  calc
    x = barR (barR x) := (bar_involutive x).symm
    _ = barR (barR y) := congrArg barR h
    _ = y := bar_involutive y

noncomputable def barK : K →+* K :=
  IsLocalization.lift (M := nonZeroDivisors R) (S := K) (P := K)
    (g := (algebraMap R K).comp barR) (by
      intro y
      apply (isUnit_iff_ne_zero).2
      intro h
      have hy0 : (y : R) ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero).mp y.property
      apply hy0
      apply bar_injective
      apply (IsFractionRing.injective R K)
      simpa using h)

lemma barK_base (x : R) : barK (algebraMap R K x) = algebraMap R K (barR x) := by
  exact IsLocalization.lift_eq (M := nonZeroDivisors R) (S := K) (P := K)
    (g := (algebraMap R K).comp barR) _ x

lemma barK_involutive : Function.Involutive barK := by
  intro z
  have hcomp : barK.comp barK = RingHom.id K := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply, barK_base, RingHom.id_apply]
    rw [bar_involutive]
  exact congrArg (fun h : K →+* K => h z) hcomp

noncomputable def Ksub : Submodule R K :=
  (Algebra.linearMap R K).range

abbrev Q := K ⧸ Ksub

lemma barK_mem_Ksub {z : K} (hz : z ∈ Ksub) : barK z ∈ Ksub := by
  rcases hz with ⟨r, hr⟩
  refine ⟨barR r, ?_⟩
  rw [← hr]
  change algebraMap R K (barR r) = barK (algebraMap R K r)
  rw [barK_base]

noncomputable def barQ : Q → Q :=
  Quotient.lift (fun z : K => Submodule.Quotient.mk (barK z)) (by
    intro x y hxy
    rw [← sub_eq_zero]
    apply (Submodule.Quotient.mk_eq_zero Ksub).2
    change barK x - barK y ∈ Ksub
    rw [← map_sub]
    have hxy' : Submodule.Quotient.mk x = Submodule.Quotient.mk y := Quotient.sound hxy
    exact barK_mem_Ksub ((Submodule.Quotient.eq Ksub).mp hxy'))

lemma barQ_involutive : Function.Involutive barQ := by
  intro q
  induction q using Quotient.inductionOn with
  | _ z =>
      change Submodule.Quotient.mk (barK (barK z)) = Submodule.Quotient.mk z
      rw [barK_involutive]

noncomputable def u : R := LaurentPolynomial.T (1 : ℤ)
noncomputable def uInv : R := LaurentPolynomial.T (-1 : ℤ)
noncomputable def f : R := u + uInv - LaurentPolynomial.C 3
noncomputable def I : Ideal R := Ideal.span ({f} : Set R)
abbrev M := R ⧸ I

lemma bar_u : barR u = uInv := by
  change barR (LaurentPolynomial.T (1 : ℤ)) = LaurentPolynomial.T (-1 : ℤ)
  exact bar_T 1

lemma bar_f : barR f = f := by
  change barR (LaurentPolynomial.T (1 : ℤ) + LaurentPolynomial.T (-1 : ℤ) -
    LaurentPolynomial.C 3) = LaurentPolynomial.T (1 : ℤ) + LaurentPolynomial.T (-1 : ℤ) -
      LaurentPolynomial.C 3
  simp only [map_sub, map_add, bar_T, bar_C]
  ring

lemma f_ne_zero : f ≠ 0 := by
  intro hf
  have h := congrArg (fun p : R => p.coeff 1) hf
  change AddMonoidAlgebra.coeff
      (AddMonoidAlgebra.single (1 : ℤ) 1 + AddMonoidAlgebra.single (-1 : ℤ) 1 -
        AddMonoidAlgebra.single (0 : ℤ) 3) 1 =
      AddMonoidAlgebra.coeff (0 : R) 1 at h
  rw [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_single] at h
  simp at h

lemma fK_ne_zero : algebraMap R K f ≠ 0 := by
  intro h
  apply f_ne_zero
  apply (IsFractionRing.injective R K)
  simpa using h

lemma quotient_diff_mem {a a' : R}
    (h : Ideal.Quotient.mk I a = Ideal.Quotient.mk I a') : a - a' ∈ I := by
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  rw [map_sub, h, sub_self]

noncomputable def raw (a b : R) : Q :=
  Submodule.Quotient.mk
    (algebraMap R K a * barK (algebraMap R K b) * (algebraMap R K f)⁻¹)

lemma raw_congr_left {a a' b : R}
    (h : Ideal.Quotient.mk I a = Ideal.Quotient.mk I a') : raw a b = raw a' b := by
  apply (Submodule.Quotient.eq Ksub).2
  change algebraMap R K a * barK (algebraMap R K b) * (algebraMap R K f)⁻¹ -
      (algebraMap R K a' * barK (algebraMap R K b) * (algebraMap R K f)⁻¹) ∈ Ksub
  rcases Ideal.mem_span_singleton'.mp (quotient_diff_mem h) with ⟨r, hr⟩
  have hdiff : a - a' = r * f := hr.symm
  have heq :
      algebraMap R K a * barK (algebraMap R K b) * (algebraMap R K f)⁻¹ -
          algebraMap R K a' * barK (algebraMap R K b) * (algebraMap R K f)⁻¹ =
        algebraMap R K r * barK (algebraMap R K b) := by
    calc
      _ = (algebraMap R K a - algebraMap R K a') *
          barK (algebraMap R K b) * (algebraMap R K f)⁻¹ := by ring
      _ = algebraMap R K (a - a') *
          barK (algebraMap R K b) * (algebraMap R K f)⁻¹ := by rw [map_sub]
      _ = algebraMap R K (r * f) *
          barK (algebraMap R K b) * (algebraMap R K f)⁻¹ := by rw [hdiff]
      _ = algebraMap R K r * barK (algebraMap R K b) := by
        rw [map_mul]
        calc
          algebraMap R K r * algebraMap R K f * barK (algebraMap R K b) *
              (algebraMap R K f)⁻¹ =
              algebraMap R K r * barK (algebraMap R K b) *
                (algebraMap R K f * (algebraMap R K f)⁻¹) := by ring
          _ = algebraMap R K r * barK (algebraMap R K b) * 1 := by
            rw [mul_inv_cancel₀ fK_ne_zero]
          _ = algebraMap R K r * barK (algebraMap R K b) := by ring
  rw [heq]
  refine ⟨r * barR b, ?_⟩
  change algebraMap R K (r * barR b) = algebraMap R K r * barK (algebraMap R K b)
  rw [map_mul, barK_base]

lemma raw_congr_right {a b b' : R}
    (h : Ideal.Quotient.mk I b = Ideal.Quotient.mk I b') : raw a b = raw a b' := by
  apply (Submodule.Quotient.eq Ksub).2
  change algebraMap R K a * barK (algebraMap R K b) * (algebraMap R K f)⁻¹ -
      (algebraMap R K a * barK (algebraMap R K b') * (algebraMap R K f)⁻¹) ∈ Ksub
  rcases Ideal.mem_span_singleton'.mp (quotient_diff_mem h) with ⟨r, hr⟩
  have hdiff : b - b' = r * f := hr.symm
  have heq :
      algebraMap R K a * barK (algebraMap R K b) * (algebraMap R K f)⁻¹ -
          algebraMap R K a * barK (algebraMap R K b') * (algebraMap R K f)⁻¹ =
        algebraMap R K a * algebraMap R K (barR r) := by
    calc
      _ = algebraMap R K a * (barK (algebraMap R K b) -
          barK (algebraMap R K b')) * (algebraMap R K f)⁻¹ := by ring
      _ = algebraMap R K a * barK (algebraMap R K (b - b')) *
          (algebraMap R K f)⁻¹ := by
            have hbar : barK (algebraMap R K b) - barK (algebraMap R K b') =
                barK (algebraMap R K b - algebraMap R K b') :=
              (map_sub barK (algebraMap R K b) (algebraMap R K b')).symm
            rw [hbar, map_sub (algebraMap R K) b b']
      _ = algebraMap R K a * barK (algebraMap R K (r * f)) *
          (algebraMap R K f)⁻¹ := by rw [hdiff]
      _ = algebraMap R K a * (algebraMap R K (barR r) * algebraMap R K f) *
          (algebraMap R K f)⁻¹ := by
            have hbar : barK (algebraMap R K (r * f)) =
                algebraMap R K (barR r) * algebraMap R K f := by
              calc
                barK (algebraMap R K (r * f)) =
                    barK (algebraMap R K r * algebraMap R K f) := by
                      rw [map_mul (algebraMap R K) r f]
                _ = barK (algebraMap R K r) * barK (algebraMap R K f) :=
                  map_mul barK _ _
                _ = algebraMap R K (barR r) * algebraMap R K (barR f) := by
                  rw [barK_base, barK_base]
                _ = algebraMap R K (barR r) * algebraMap R K f := by rw [bar_f]
            rw [hbar]
      _ = algebraMap R K a * algebraMap R K (barR r) := by
        calc
          algebraMap R K a * (algebraMap R K (barR r) * algebraMap R K f) *
              (algebraMap R K f)⁻¹ =
              algebraMap R K a * algebraMap R K (barR r) *
                (algebraMap R K f * (algebraMap R K f)⁻¹) := by ring
          _ = algebraMap R K a * algebraMap R K (barR r) * 1 := by
            rw [mul_inv_cancel₀ fK_ne_zero]
          _ = algebraMap R K a * algebraMap R K (barR r) := by ring
  rw [heq]
  refine ⟨a * barR r, ?_⟩
  change algebraMap R K (a * barR r) = algebraMap R K a * algebraMap R K (barR r)
  rw [map_mul]

noncomputable def lambda : M → M → Q :=
  Quotient.lift
    (fun a : R =>
      Quotient.lift (fun b : R => raw a b) (by
        intro b b' h
        have hmk : Ideal.Quotient.mk I b = Ideal.Quotient.mk I b' := Quotient.sound h
        exact raw_congr_right hmk))
    (by
      intro a a' h
      funext q
      induction q using Quotient.inductionOn with
      | _ b =>
          have hmk : Ideal.Quotient.mk I a = Ideal.Quotient.mk I a' := Quotient.sound h
          exact raw_congr_left hmk)

lemma raw_hermitian (a b : R) : raw a b = barQ (raw b a) := by
  have hF : barK (algebraMap R K f) = algebraMap R K f := by
    rw [barK_base, bar_f]
  have hbar : barK (algebraMap R K b * barK (algebraMap R K a) *
      (algebraMap R K f)⁻¹) =
      barK (algebraMap R K b) * algebraMap R K a * (algebraMap R K f)⁻¹ := by
    calc
      barK (algebraMap R K b * barK (algebraMap R K a) *
          (algebraMap R K f)⁻¹) =
          barK (algebraMap R K b) *
            barK (barK (algebraMap R K a) * (algebraMap R K f)⁻¹) := by
              simp only [map_mul]
              ring
      _ = barK (algebraMap R K b) *
            (barK (barK (algebraMap R K a)) * barK ((algebraMap R K f)⁻¹)) := by
              simp only [map_mul]
      _ = barK (algebraMap R K b) * algebraMap R K a *
            (algebraMap R K f)⁻¹ := by
              rw [barK_involutive, map_inv₀, hF]
              ring
  change Submodule.Quotient.mk
      (algebraMap R K a * barK (algebraMap R K b) * (algebraMap R K f)⁻¹) =
    Submodule.Quotient.mk
      (barK (algebraMap R K b * barK (algebraMap R K a) *
        (algebraMap R K f)⁻¹))
  rw [hbar]
  congr 1
  ring

lemma lambda_hermitian : ∀ x y : M, lambda x y = barQ (lambda y x) := by
  intro x y
  induction x using Quotient.inductionOn with
  | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
          exact raw_hermitian a b

end MathlibPlus.Algebra.Claim9564
