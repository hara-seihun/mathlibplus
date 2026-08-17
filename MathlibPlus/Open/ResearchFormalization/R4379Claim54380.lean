import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R4379Claim54380


open scoped BigOperators

abbrev SupportIndex (E : Type*) (S : Finset E) := {e : E // e ∈ S}
abbrev SupportSpan {E V : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V]
    (L : (E → ℚ) →ₗ[ℚ] V) (S : Finset E) :=
  Submodule.span ℚ (Set.range (fun e : SupportIndex E S => L (Pi.single e.1 1)))

def scalarSupport {E : Type*} [Fintype E] [DecidableEq E]
    (q : E → ℚ) : Finset E :=
  Finset.univ.filter (fun e => q e ≠ 0)

def positiveScalarCircuit {E V : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V]
    (L : (E → ℚ) →ₗ[ℚ] V) (q : E → ℚ) (S : Finset E) : Prop :=
  S.Nonempty ∧
    2 ≤ S.card ∧
      (∀ e, e ∈ S ↔ q e ≠ 0) ∧
        (∀ e, e ∈ S → 0 < q e) ∧
          L q = 0 ∧
            ∀ r : E → ℚ, L r = 0 → r ≠ 0 →
              scalarSupport r ⊆ S → scalarSupport r = S

def supportColumn {E V : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V]
    (L : (E → ℚ) →ₗ[ℚ] V) (S : Finset E)
    (e : SupportIndex E S) : SupportSpan L S :=
  ⟨L (Pi.single e.1 1), Submodule.subset_span (Set.mem_range_self e)⟩

def discardedSpan {E V : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V]
    (L : (E → ℚ) →ₗ[ℚ] V) (S T : Finset E) :
    Submodule ℚ (SupportSpan L S) :=
  Submodule.span ℚ
    (Set.range (fun e : {e : SupportIndex E S // e.1 ∉ T} =>
      supportColumn L S e.1))

abbrev contractionQuotient {E V : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V]
    (L : (E → ℚ) →ₗ[ℚ] V) (S T : Finset E) :=
  (SupportSpan L S) ⧸ discardedSpan L S T

def contractionColumn {E V : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V]
    (L : (E → ℚ) →ₗ[ℚ] V) (S T : Finset E)
    (hTS : T ⊆ S) (e : {e : E // e ∈ T}) :
    contractionQuotient L S T :=
  Submodule.Quotient.mk (supportColumn L S ⟨e.1, hTS e.2⟩)

def finiteLinearCombination {I M : Type*} [Fintype I]
    [AddCommGroup M] [Module ℚ M] (v : I → M) :
    (I → ℚ) →ₗ[ℚ] M :=
  { toFun := fun c => ∑ i : I, c i • v i
    map_add' := by
      intro c d
      simp [add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro a c
      change (∑ i : I, (a * c i) • v i) = a • ∑ i : I, c i • v i
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_smul] }

def contractionMap {E V : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V]
    (L : (E → ℚ) →ₗ[ℚ] V) (S T : Finset E)
    (hTS : T ⊆ S) :
    (T → ℚ) →ₗ[ℚ] contractionQuotient L S T :=
  finiteLinearCombination (fun e : {e : E // e ∈ T} =>
    contractionColumn L S T hTS e)

def normalizedSupportWeight {E : Type*} [Fintype E]
    (q : E → ℚ) (S : Finset E) (e : E) : ℚ :=
  q e / ∑ f ∈ S, q f

def nestedSpan {E V : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V]
    (L : (E → ℚ) →ₗ[ℚ] V) (S T U : Finset E)
    (hTS : T ⊆ S) :
    Submodule ℚ (contractionQuotient L S T) :=
  Submodule.span ℚ
    (Set.range (fun e : {e : E // e ∈ T \ U} =>
      contractionColumn L S T hTS
        ⟨e.1, (Finset.mem_sdiff.mp e.2).1⟩))

abbrev nestedQuotient {E V : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V]
    (L : (E → ℚ) →ₗ[ℚ] V) (S T U : Finset E)
    (hTS : T ⊆ S) :=
  contractionQuotient L S T ⧸ nestedSpan L S T U hTS

def nestedColumn {E V : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V]
    (L : (E → ℚ) →ₗ[ℚ] V) (S T U : Finset E)
    (hTS : T ⊆ S) (hUT : U ⊆ T) (e : {e : E // e ∈ U}) :
    contractionQuotient L S T :=
  contractionColumn L S T hTS ⟨e.1, hUT e.2⟩

def nestedContractionsCompose {E V : Type*} [Fintype E] [DecidableEq E]
    [AddCommGroup V] [Module ℚ V]
    (L : (E → ℚ) →ₗ[ℚ] V) (q : E → ℚ) (S : Finset E) : Prop :=
  positiveScalarCircuit L q S →
    ∀ U T : Finset E, U.Nonempty →
      ∀ hUT : U ⊆ T, ∀ hTS : T ⊆ S,
        (∃ e : nestedQuotient L S T U hTS ≃ₗ[ℚ]
            contractionQuotient L S U,
          ∀ u : {u : E // u ∈ U},
            e (Submodule.Quotient.mk
              (nestedColumn L S T U hTS hUT u)) =
              contractionColumn L S U (fun _ hx => hTS (hUT hx)) u) ∧
        (∀ u : E, u ∈ U →
          let weights := normalizedSupportWeight q S
          let weightT := ∑ f ∈ T, weights f
          let weightU := ∑ f ∈ U, weights f
          (weights u / weightT) /
              (∑ f ∈ U, weights f / weightT) = weights u / weightU)


end MathlibPlus.Open.ResearchFormalization.R4379Claim54380
