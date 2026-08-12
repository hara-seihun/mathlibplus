import Mathlib

namespace MathlibPlus.GraphTheory

universe u v

/-- A relabelling carries each directed right-Cayley relation in `S` to the
corresponding relation in `T`.  Labels are preserved, not merely permuted. -/
def IsCayleyRelationIso {G : Type u} {H : Type v} [Group G] [Group H]
    {κ : Type} (S : κ → Set G) (T : κ → Set H) (f : G ≃ H) : Prop :=
  ∀ i x y, x⁻¹ * y ∈ S i ↔ (f x)⁻¹ * f y ∈ T i

/-- CI for a fixed label type of directed binary Cayley relations. -/
def IsCayleyRelCI (G : Type u) [Group G] (κ : Type) : Prop :=
  ∀ (S T : κ → Set G) (f : G ≃ G), IsCayleyRelationIso S T f →
    ∃ φ : G ≃* G, ∀ i, φ '' S i = T i

/-- Binary-relational Cayley CI (`CI^(2)`): CI for every finite label type. -/
def IsCayleyCI2 (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (κ : Type) [Finite κ], IsCayleyRelCI G κ

/-- Directed Cayley-graph CI, expressed as the one-label relational case. -/
def IsCayleyDCI (G : Type u) [Group G] [Finite G] : Prop :=
  IsCayleyRelCI G PUnit

/-- Ordinary undirected Cayley-graph CI in the exact `SimpleGraph.mulCayley`
model used by the open quotient node. -/
def IsCayleyGraphCI (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (S T : Set G), S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
    Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
      ∃ φ : G ≃* G, φ '' S = T

/-- The first implication in the fixed-group hierarchy: arbitrary finite
binary-relation tuples include one directed relation. -/
theorem isCayleyDCI_of_isCayleyCI2 {G : Type u} [Group G] [Finite G]
    (hG : IsCayleyCI2 G) : IsCayleyDCI G := by
  exact hG PUnit

private theorem mem_iff_mulCayley_adj {G : Type u} [Group G]
    (S : Set G) (hS_inv : S = S⁻¹) (hS_one : 1 ∉ S) (x y : G) :
    x⁻¹ * y ∈ S ↔ (SimpleGraph.mulCayley S).Adj x y := by
  rw [SimpleGraph.mulCayley_adj]
  constructor
  · intro hxy
    refine ⟨?_, Or.inl hxy⟩
    intro h
    subst y
    apply hS_one
    simpa using hxy
  · rintro ⟨_, hxy | hyx⟩
    · exact hxy
    · rw [hS_inv]
      simpa using hyx

/-- The second implication in the fixed-group hierarchy: directed CI implies
ordinary undirected graph CI. -/
theorem isCayleyGraphCI_of_isCayleyDCI {G : Type u} [Group G] [Finite G]
    (hG : IsCayleyDCI G) : IsCayleyGraphCI G := by
  intro S T hS_inv hT_inv hS_one hT_one hIso
  obtain ⟨f⟩ := hIso
  have hf : IsCayleyRelationIso (fun _ : PUnit => S) (fun _ : PUnit => T) f.toEquiv := by
    intro _ x y
    rw [mem_iff_mulCayley_adj S hS_inv hS_one,
      mem_iff_mulCayley_adj T hT_inv hT_one]
    exact f.map_rel_iff.symm
  obtain ⟨φ, hφ⟩ := hG (fun _ : PUnit => S) (fun _ : PUnit => T) f.toEquiv hf
  exact ⟨φ, hφ PUnit.unit⟩

/-- Kernel marking makes binary-relational CI hereditary to normal quotients.
The extra `none` label records the kernel relation, while `some i` pulls back
the quotient relation labelled `i`. -/
theorem isCayleyCI2_quotient {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hG : IsCayleyCI2 G) :
    IsCayleyCI2 (G ⧸ N) := by
  intro κ _
  intro S T f hf
  let K := N ⧸ (⊥ : Subgroup G).subgroupOf N
  let c : G ≃ (G ⧸ N) × K :=
    (QuotientGroup.quotientEquivSelf G).symm.trans
      (Subgroup.quotientEquivProdOfLE (show (⊥ : Subgroup G) ≤ N from bot_le))
  let p : (G ⧸ N) × K ≃ (G ⧸ N) × K :=
    Equiv.prodCongr f (Equiv.refl _)
  let F : G ≃ G := c.trans (p.trans c.symm)
  have hc_fst (x : G) : (c x).1 = (x : G ⧸ N) := rfl
  have hF (x : G) : (F x : G ⧸ N) = f (x : G ⧸ N) := by
    rw [← hc_fst (F x), ← hc_fst x]
    simp [F, p]
  have quotient_eq_iff (x y : G) :
      x⁻¹ * y ∈ N ↔ (x : G ⧸ N) = (y : G ⧸ N) := by
    rw [← QuotientGroup.eq_one_iff]
    change (x : G ⧸ N)⁻¹ * (y : G ⧸ N) = 1 ↔
      (x : G ⧸ N) = (y : G ⧸ N)
    exact inv_mul_eq_one
  let S' : Option κ → Set G
    | none => N
    | some i => (QuotientGroup.mk' N) ⁻¹' S i
  let T' : Option κ → Set G
    | none => N
    | some i => (QuotientGroup.mk' N) ⁻¹' T i
  have hFrel : IsCayleyRelationIso S' T' F := by
    intro i x y
    cases i with
    | none =>
        change x⁻¹ * y ∈ N ↔ (F x)⁻¹ * F y ∈ N
        rw [quotient_eq_iff, quotient_eq_iff, hF, hF]
        exact f.injective.eq_iff.symm
    | some i =>
        change (x⁻¹ * y : G ⧸ N) ∈ S i ↔ ((F x)⁻¹ * F y : G ⧸ N) ∈ T i
        change (x : G ⧸ N)⁻¹ * (y : G ⧸ N) ∈ S i ↔
          (F x : G ⧸ N)⁻¹ * (F y : G ⧸ N) ∈ T i
        simpa only [hF] using hf i (x : G ⧸ N) (y : G ⧸ N)
  obtain ⟨α, hα⟩ := hG (Option κ) S' T' F hFrel
  have hN_image : α '' (N : Set G) = (N : Set G) := hα none
  have hN_map : N.map α = N := by
    ext x
    change x ∈ α '' (N : Set G) ↔ x ∈ (N : Set G)
    rw [hN_image]
  let β : (G ⧸ N) ≃* (G ⧸ N) := QuotientGroup.congr N N α hN_map
  refine ⟨β, ?_⟩
  intro i
  have hi : α '' ((QuotientGroup.mk' N) ⁻¹' S i) =
      (QuotientGroup.mk' N) ⁻¹' T i := hα (some i)
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N w
    have hx : x ∈ (QuotientGroup.mk' N) ⁻¹' S i := hw
    have hαx : α x ∈ (QuotientGroup.mk' N) ⁻¹' T i := by
      rw [← hi]
      exact ⟨x, hx, rfl⟩
    exact hαx
  · intro hz
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N z
    have hy : y ∈ (QuotientGroup.mk' N) ⁻¹' T i := hz
    rw [← hi] at hy
    rcases hy with ⟨x, hx, hxy⟩
    refine ⟨(x : G ⧸ N), hx, ?_⟩
    change (α x : G ⧸ N) = (y : G ⧸ N)
    rw [hxy]

/-- The common fixed-group consequence web: `CI^(2)` implies DCI and ordinary
undirected CI. -/
theorem isCayleyGraphCI_of_isCayleyCI2 {G : Type u} [Group G] [Finite G]
    (hG : IsCayleyCI2 G) : IsCayleyGraphCI G :=
  isCayleyGraphCI_of_isCayleyDCI (isCayleyDCI_of_isCayleyCI2 hG)

/-- Kernel-marked quotient transfer followed by the one-label specialization. -/
theorem isCayleyDCI_quotient_of_isCayleyCI2 {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hG : IsCayleyCI2 G) : IsCayleyDCI (G ⧸ N) :=
  isCayleyDCI_of_isCayleyCI2 (isCayleyCI2_quotient N hG)

/-- Kernel-marked quotient transfer followed by undirected specialization. -/
theorem isCayleyGraphCI_quotient_of_isCayleyCI2
    {G : Type u} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hG : IsCayleyCI2 G) : IsCayleyGraphCI (G ⧸ N) :=
  isCayleyGraphCI_of_isCayleyCI2 (isCayleyCI2_quotient N hG)

end MathlibPlus.GraphTheory
