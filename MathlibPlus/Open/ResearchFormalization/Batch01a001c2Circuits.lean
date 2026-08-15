import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Circuits

/-- The two scalar response classes determined by a positive circuit. -/
def claim52760 : Prop :=
  ∀ (S W Z : Type*) [Fintype S] [Nonempty S]
    [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    [AddCommGroup Z] [Module ℚ Z] [FiniteDimensional ℚ Z]
    (L : (S → ℚ) →ₗ[ℚ] W) (ell : S → W) (q : S → ℚ) (a : S → Z),
    (∀ c, L c = ∑ e, c e • ell e) ∧
    (∀ e, 0 < q e) ∧
    LinearMap.ker L = Submodule.span ℚ ({q} : Set (S → ℚ)) →
    let Q₀ : ℚ := ∑ e, q e
    let lambda : S → ℚ := fun e => q e / Q₀
    ∃! bar_a : Z,
      bar_a = ∑ e, lambda e • a e ∧
      ∃! Phi : W →ₗ[ℚ] Z,
        (∀ e, a e = bar_a + Phi (ell e)) ∧
        (∑ e, q e • a e = Q₀ • bar_a) ∧
        ((∑ e, q e • a e) ≠ 0 ↔ bar_a ≠ 0)

/-- Canonical centering and all nonempty contraction minors. -/
def claim52761 : Prop :=
  ∀ (S W Z : Type*) [Fintype S] [DecidableEq S] [Nonempty S]
    [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    [AddCommGroup Z] [Module ℚ Z] [FiniteDimensional ℚ Z]
    (L : (S → ℚ) →ₗ[ℚ] W) (ell : S → W) (q : S → ℚ)
    (a : S → Z) (bar_a : Z) (Phi : W →ₗ[ℚ] Z) (u : S → Z),
    (∀ c, L c = ∑ e, c e • ell e) ∧
    (∀ e, 0 < q e) ∧
    LinearMap.ker L = Submodule.span ℚ ({q} : Set (S → ℚ)) ∧
    (∀ e, a e = bar_a + Phi (ell e)) ∧
    (∀ e, u e = bar_a) ∧
    (let Q₀ : ℚ := ∑ e, q e
     let lambda : S → ℚ := fun e => q e / Q₀
     bar_a = ∑ e, lambda e • a e) →
    let Q₀ : ℚ := ∑ e, q e
    ∀ T : Finset S, T.Nonempty →
      let qT : ℚ := ∑ e ∈ T, q e
      let U_T : Submodule ℚ W :=
        Submodule.span ℚ {w : W | ∃ e : S, e ∉ T ∧ w = ell e}
      (∀ e ∈ T, 0 < q e / qT) ∧
      (∑ e ∈ T, q e / qT) = 1 ∧
      (∑ e ∈ T, (q e / qT) • Submodule.mkQ U_T (ell e)) = 0 ∧
      (∑ e ∈ T, q e • u e) = qT • bar_a ∧
      ((∑ e ∈ T, q e • u e) ≠ 0 ↔ (Q₀ • bar_a) ≠ 0)

def binaryRawRestrictionExamples52763 : Prop :=
  let S := Bool
  let q : S → ℚ := fun _ => 1
  let ell : S → ℚ := fun e => if e = false then 1 else -1
  let lambda : S → ℚ := fun _ => 1 / 2
  let T : Finset S := {false}
  let a₁ : S → ℚ := fun e => if e = false then 0 else 2
  let a₂ : S → ℚ := fun e => if e = false then 1 else -1
  (q = (fun _ => (1 : ℚ))) ∧
    (∑ e, lambda e • ell e = 0) ∧
    (∑ e, lambda e • a₁ e = 1) ∧
    (∑ e ∈ T, (lambda e / (∑ f ∈ T, lambda f)) • a₁ e = 0) ∧
    (∑ e, lambda e • a₂ e = 0) ∧
    (∑ e ∈ T, (lambda e / (∑ f ∈ T, lambda f)) • a₂ e = 1)

/-- The exact raw-restriction centering defect. -/
def claim52763 : Prop :=
  ∀ (S W Z : Type*) [Fintype S] [DecidableEq S] [Nonempty S]
    [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    [AddCommGroup Z] [Module ℚ Z] [FiniteDimensional ℚ Z]
    (L : (S → ℚ) →ₗ[ℚ] W) (ell : S → W) (q : S → ℚ)
    (a : S → Z) (bar_a : Z) (Phi : W →ₗ[ℚ] Z),
    (∀ c, L c = ∑ e, c e • ell e) ∧
    (∀ e, 0 < q e) ∧
    LinearMap.ker L = Submodule.span ℚ ({q} : Set (S → ℚ)) ∧
    (∀ e, a e = bar_a + Phi (ell e)) ∧
    (let Q₀ : ℚ := ∑ e, q e
     let lambda : S → ℚ := fun e => q e / Q₀
     bar_a = ∑ e, lambda e • a e ∧
     (∑ e, lambda e • ell e) = 0) →
    (∀ T : Finset S, T.Nonempty →
      let Q₀ : ℚ := ∑ e, q e
      let lambda : S → ℚ := fun e => q e / Q₀
      let lambdaT : ℚ := ∑ e ∈ T, lambda e
      let bT : W := ∑ e ∈ T, lambda e • ell e
      let barT : Z := ∑ e ∈ T, (lambda e / lambdaT) • a e
      let bComp : W := ∑ e ∈ (Finset.univ \ T), lambda e • ell e
      barT = bar_a + lambdaT⁻¹ • Phi bT ∧
      barT = bar_a - lambdaT⁻¹ • Phi bComp ∧
      (barT = bar_a ↔ Phi bT = 0)) ∧
    binaryRawRestrictionExamples52763

/-- The one-support projected defect criterion and its universal form. -/
def claim52770 : Prop :=
  ∀ (S W Z Y : Type*) [Fintype S] [DecidableEq S] [Nonempty S]
    [AddCommGroup W] [Module ℚ W]
    [AddCommGroup Z] [Module ℚ Z]
    [AddCommGroup Y] [Module ℚ Y]
    (L : (S → ℚ) →ₗ[ℚ] W) (ell : S → W) (q : S → ℚ)
    (a : S → Z) (bar_a : Z) (Phi : W →ₗ[ℚ] Z)
    (Psi : Z →ₗ[ℚ] Y),
    (∀ c, L c = ∑ e, c e • ell e) ∧
    (∀ e, 0 < q e) ∧
    LinearMap.ker L = Submodule.span ℚ ({q} : Set (S → ℚ)) ∧
    (let Q₀ : ℚ := ∑ e, q e
     let lambda : S → ℚ := fun e => q e / Q₀
     bar_a = ∑ e, lambda e • a e) ∧
    (∀ e, a e = bar_a + Phi (ell e)) →
    let Q₀ : ℚ := ∑ e, q e
    let lambda : S → ℚ := fun e => q e / Q₀
    (∀ T : Finset S, T.Nonempty →
      let lambdaT : ℚ := ∑ e ∈ T, lambda e
      let bT : W := ∑ e ∈ T, lambda e • ell e
      let barT : Z := ∑ e ∈ T, (lambda e / lambdaT) • a e
      (Psi barT = Psi bar_a ↔ Psi (Phi bT) = 0)) ∧
    ((∀ T : Finset S, T.Nonempty →
        let lambdaT : ℚ := ∑ e ∈ T, lambda e
        let barT : Z := ∑ e ∈ T, (lambda e / lambdaT) • a e
        Psi barT = Psi bar_a) ↔
      ∀ w : W, Psi (Phi w) = 0)

/-- Proper support barycenters cannot vanish in a positive scalar circuit. -/
def claim52771 : Prop :=
  ∀ (S W : Type*) [Fintype S] [DecidableEq S] [Nonempty S]
    [AddCommGroup W] [Module ℚ W]
    (L : (S → ℚ) →ₗ[ℚ] W) (ell : S → W) (q : S → ℚ),
    (∀ c, L c = ∑ e, c e • ell e) ∧
    (∀ e, 0 < q e) ∧
    LinearMap.ker L = Submodule.span ℚ ({q} : Set (S → ℚ)) →
    let Q₀ : ℚ := ∑ e, q e
    let lambda : S → ℚ := fun e => q e / Q₀
    ∀ T : Finset S, T.Nonempty → T ≠ Finset.univ →
      (∑ e ∈ T, lambda e • ell e) ≠ 0

/-- Normalized support barycenters and complementary support identity. -/
def claim52774 : Prop :=
  ∀ (S W : Type*) [Fintype S] [DecidableEq S] [Nonempty S]
    [AddCommGroup W] [Module ℚ W]
    (L : (S → ℚ) →ₗ[ℚ] W) (ell : S → W) (q : S → ℚ),
    Fintype.card S ≠ 1 →
    (∀ c, L c = ∑ e, c e • ell e) ∧
    (∀ e, 0 < q e) ∧
    LinearMap.ker L = Submodule.span ℚ ({q} : Set (S → ℚ)) →
    let Q₀ : ℚ := ∑ e, q e
    let lambda : S → ℚ := fun e => q e / Q₀
    (∑ e, lambda e = 1) ∧
    (∑ e, lambda e • ell e = 0) ∧
    (∀ T : Finset S, T.Nonempty → T ≠ Finset.univ →
      let bT : W := ∑ e ∈ T, lambda e • ell e
      bT ≠ 0 ∧
      (∑ e ∈ (Finset.univ \ T), lambda e • ell e) = -bT)

/-- The feasible centered-support family and its closure properties. -/
def claim52775 : Prop :=
  ∀ (S W Y : Type*) [Fintype S] [DecidableEq S] [Nonempty S]
    [AddCommGroup W] [Module ℚ W]
    [AddCommGroup Y] [Module ℚ Y] [FiniteDimensional ℚ Y]
    [Nontrivial Y]
    (ell : S → W) (lambda : S → ℚ) (K : W →ₗ[ℚ] Y),
    (∀ e, 0 < lambda e) ∧ (∑ e, lambda e = 1) ∧
    (∑ e, lambda e • ell e = 0) ∧
    (∀ T : Finset S, T.Nonempty → T ≠ Finset.univ →
      (∑ e ∈ T, lambda e • ell e) ≠ 0) →
    let feasible : Finset S → Prop := fun T =>
      T.Nonempty ∧ T ≠ Finset.univ ∧
        K (∑ e ∈ T, lambda e • ell e) = 0
    (∀ T : Finset S, T.Nonempty → T ≠ Finset.univ →
      feasible T ↔
        (∑ e ∈ T, lambda e • K (ell e)) = 0) ∧
    (∀ T : Finset S, feasible T ↔ feasible (Finset.univ \ T)) ∧
    (∀ T U : Finset S, feasible T → feasible U →
      T ∩ U = ∅ → T ∪ U ≠ Finset.univ → feasible (T ∪ U)) ∧
    (∀ T : Finset S, feasible T →
      ∃ A : Finset S, A ⊆ T ∧ feasible A ∧
        ∀ B : Finset S, B ⊂ A → ¬ feasible B)

/-- Every proper-support condition is the proper evaluation kernel of the
corresponding nonzero barycenter. -/
def claim52776 : Prop :=
  ∀ (S W Y : Type*) [Fintype S] [DecidableEq S] [Nonempty S]
    [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    [AddCommGroup Y] [Module ℚ Y] [FiniteDimensional ℚ Y]
    [Nontrivial Y]
    (ell : S → W) (lambda : S → ℚ),
    (∀ e, 0 < lambda e) ∧ (∑ e, lambda e = 1) ∧
    (∑ e, lambda e • ell e = 0) ∧
    (∀ T : Finset S, T.Nonempty → T ≠ Finset.univ →
      (∑ e ∈ T, lambda e • ell e) ≠ 0) →
    let barycenter : Finset S → W := fun T =>
      ∑ e ∈ T, lambda e • ell e
    let condition : Finset S → Set (W →ₗ[ℚ] Y) := fun T =>
      {K | K (barycenter T) = 0}
    let proper : Finset S → Prop := fun T =>
      T.Nonempty ∧ T ≠ Finset.univ
    (∀ T : Finset S, proper T →
      ∃ ev : (W →ₗ[ℚ] Y) →ₗ[ℚ] Y,
        (∀ K, ev K = K (barycenter T)) ∧
        Function.Surjective ev ∧
        condition T = (ev.ker : Set (W →ₗ[ℚ] Y)) ∧
        ev.ker ≠ ⊤ ∧
        Module.finrank ℚ ((W →ₗ[ℚ] Y) ⧸ ev.ker) = Module.finrank ℚ Y) ∧
    (∀ T : Finset S, proper T →
      condition T = condition (Finset.univ \ T)) ∧
    Set.ncard (Set.range (fun T : {T : Finset S // proper T} =>
      condition T.1)) ≤ 2 ^ (Fintype.card S - 1) - 1

end MathlibPlus.Open.ResearchFormalization.Circuits
