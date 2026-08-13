import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Coinvariants

noncomputable section

open scoped BigOperators
open Representation GroupAlgebra

namespace MathlibPlus.Open.LinearAlgebra

/-- Claim 29615: for a finite group representation over a characteristic-zero
field, Reynolds averaging identifies coinvariants with invariants.  The
specified value on every quotient generator makes the word “canonical”
mathematical rather than an unqualified existence assertion. -/
def claim29615 : Prop :=
  ∀ (K Γ M : Type*) [Field K] [CharZero K] [Fintype Γ] [Group Γ]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M],
    ∀ ρ : Representation K Γ M,
      ∃ e : ρ.Coinvariants ≃ₗ[K] ρ.invariants,
        ∀ m : M,
          ((e (Representation.Coinvariants.mk ρ m) : ρ.invariants) : M) =
            (Fintype.card Γ : K)⁻¹ • ∑ g : Γ, ρ g m

end MathlibPlus.Open.LinearAlgebra

namespace MathlibPlus.LinearAlgebra

variable {K Γ M : Type*} [Field K] [CharZero K] [Fintype Γ] [Group Γ]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- Kernel-checked Reynolds equivalence for claim 29615. -/
theorem claim29615_reynolds (ρ : Representation K Γ M) :
    ∃ e : ρ.Coinvariants ≃ₗ[K] ρ.invariants,
      ∀ m : M,
        ((e (Representation.Coinvariants.mk ρ m) : ρ.invariants) : M) =
          (Fintype.card Γ : K)⁻¹ • ∑ g : Γ, ρ g m := by
  letI : Invertible (Fintype.card Γ : K) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card Γ : K) ≠ 0)
  have hform (v : M) : ρ.averageMap v =
      (Fintype.card Γ : K)⁻¹ • ∑ x : Γ, ρ x v := by
    simp [Representation.averageMap, GroupAlgebra.average, invOf_eq_inv]
  have hcomm (g : Γ) : ρ.averageMap ∘ₗ ρ g = ρ.averageMap := by
    ext m
    change ρ.averageMap (ρ g m) = ρ.averageMap m
    rw [hform, hform]
    rw [show (∑ x : Γ, ρ x (ρ g m)) = ∑ x : Γ, ρ (x * g) m by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Module.End.mul_apply, ← map_mul]]
    rw [Function.Bijective.sum_comp (Group.mulRight_bijective g) (fun x : Γ => ρ x m)]
  let avg : M →ₗ[K] ρ.invariants :=
    (ρ.averageMap.codRestrict ρ.invariants (fun v => ρ.averageMap_invariant v))
  have havg_mk : ∀ v : M,
      (Representation.Coinvariants.mk ρ v) =
        Representation.Coinvariants.mk ρ (ρ.averageMap v) := by
    intro v
    rw [hform]
    rw [map_smul, map_sum]
    simp [Representation.Coinvariants.mk_self_apply]
    have hcard : (Fintype.card Γ : K) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hquot : ∀ g : Γ, avg ∘ₗ ρ g = avg := by
    intro g
    ext v
    change ρ.averageMap (ρ g v) = ρ.averageMap v
    exact congrArg (fun f : M →ₗ[K] M => f v) (hcomm g)
  let lift : ρ.Coinvariants →ₗ[K] ρ.invariants :=
    Representation.Coinvariants.lift ρ avg hquot
  have hlift_mk (v : M) : lift (Representation.Coinvariants.mk ρ v) = avg v := by
    rfl
  have hsurj : Function.Surjective lift := by
    intro y
    refine ⟨Representation.Coinvariants.mk ρ (y : M), ?_⟩
    apply Subtype.ext
    simpa [lift, avg] using ρ.averageMap_id (y : M) y.property
  have hinj : Function.Injective lift := by
    intro x
    refine Representation.Coinvariants.induction_on x ?_
    intro v y
    refine Representation.Coinvariants.induction_on y ?_
    intro w hvw
    have hp : ρ.averageMap v = ρ.averageMap w := by
      have hvw' := congrArg (fun z : ρ.invariants => (z : M)) hvw
      simpa [hlift_mk, avg] using hvw'
    calc
      Representation.Coinvariants.mk ρ v =
          Representation.Coinvariants.mk ρ (ρ.averageMap v) := havg_mk v
      _ = Representation.Coinvariants.mk ρ (ρ.averageMap w) := by rw [hp]
      _ = Representation.Coinvariants.mk ρ w := (havg_mk w).symm
  let e : ρ.Coinvariants ≃ₗ[K] ρ.invariants :=
    LinearEquiv.ofBijective lift ⟨hinj, hsurj⟩
  refine ⟨e, ?_⟩
  intro v
  change ((lift (Representation.Coinvariants.mk ρ v) : ρ.invariants) : M) = _
  rw [hlift_mk]
  exact hform v

end MathlibPlus.LinearAlgebra
