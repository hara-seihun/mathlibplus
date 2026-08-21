-- UNVERIFIED (too-heavy): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.GroupTheory.CayleyDerivativeShadow

/-- The normalized relative derivative of a permutation at a base point. -/
def relativeDerivative {G : Type*} [Group G]
    (f : Equiv.Perm G) (x : G) : Equiv.Perm G :=
  ((((Equiv.mulLeft x).trans f).trans (Equiv.mulLeft (f x)⁻¹)).trans f.symm)

@[simp]
theorem relativeDerivative_apply {G : Type*} [Group G]
    (f : Equiv.Perm G) (x s : G) :
    relativeDerivative f x s = f.symm ((f x)⁻¹ * f (x * s)) := rfl

/-- One forward saturation step under every relative derivative. -/
def relativeDerivativeStep {G : Type*} [Fintype G] [Group G] [DecidableEq G]
    (f : Equiv.Perm G) (A : Finset G) : Finset G :=
  A ∪ Finset.univ.biUnion (fun x => A.map (relativeDerivative f x).toEmbedding)

/-- The bounded relative-derivative reachability set. On a finite group, `|G|`
forward saturation steps suffice for every generated orbit. -/
def relativeDerivativeReachable {G : Type*} [Fintype G] [Group G] [DecidableEq G]
    (f : Equiv.Perm G) (s : G) : Finset G :=
  (relativeDerivativeStep f)^[Fintype.card G] {s}

/-- A finite group has the binary Cayley shadow property when every normalized
permutation has one group-automorphism shadow whose discrepancy is reachable
from each point by relative derivatives. -/
def HasBinaryCayleyShadow (G : Type*) [Fintype G] [Group G] [DecidableEq G] : Prop :=
  ∀ f : Equiv.Perm G, f 1 = 1 →
    ∃ α : G ≃* G, ∀ s : G,
      f.symm (α s) ∈ relativeDerivativeReachable f s

private theorem reachable_subset_of_derivative_invariant
    {G : Type*} [Fintype G] [Group G] [DecidableEq G]
    (f : Equiv.Perm G) (A : Finset G)
    (hA : ∀ x s : G, relativeDerivative f x s ∈ A ↔ s ∈ A)
    {s : G} (hs : s ∈ A) : relativeDerivativeReachable f s ⊆ A := by
  have hstep : ∀ B : Finset G, B ⊆ A → relativeDerivativeStep f B ⊆ A := by
    intro B hB z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hB hz
    · obtain ⟨x, -, hz⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hz
      exact (hA x y).2 (hB hy)
  have hiter : ∀ (n : ℕ) (B : Finset G), B ⊆ A →
      ((relativeDerivativeStep f)^[n]) B ⊆ A := by
    intro n
    induction n with
    | zero =>
        intro B hB
        simpa using hB
    | succ n ih =>
        intro B hB
        rw [Function.iterate_succ_apply]
        exact ih _ (hstep B hB)
  exact hiter _ {s} (by simpa using hs)

/-- The binary Cayley shadow property is a sufficient common mechanism for
simultaneous CI of every finite fixed-label tuple of directed binary Cayley
relations. -/
theorem binaryRelationalCI_of_hasBinaryCayleyShadow
    (G : Type*) [Fintype G] [Group G] [DecidableEq G]
    (hG : HasBinaryCayleyShadow G) :
    ∀ (ι : Type*) [Finite ι] (S T : ι → Finset G) (e : G ≃ G),
      (∀ i x y, x⁻¹ * y ∈ S i ↔ (e x)⁻¹ * e y ∈ T i) →
      ∃ α : G ≃* G, ∀ i, (S i).map α.toEquiv.toEmbedding = T i := by
  intro ι _ S T e he
  let f : Equiv.Perm G := e.trans (Equiv.mulLeft (e 1)⁻¹)
  have hf1 : f 1 = 1 := by
    simp [f]
  have hdiff (x y : G) : (f x)⁻¹ * f y = (e x)⁻¹ * e y := by
    simp [f, mul_assoc]
  have hef (i : ι) (x y : G) :
      x⁻¹ * y ∈ S i ↔ (f x)⁻¹ * f y ∈ T i := by
    rw [hdiff]
    exact he i x y
  obtain ⟨α, hα⟩ := hG f hf1
  let h : Equiv.Perm G := α.toEquiv.trans f.symm
  refine ⟨α, ?_⟩
  intro i
  have hqmem (x s : G) :
      relativeDerivative f x s ∈ S i ↔ s ∈ S i := by
    have hxs := hef i x (x * s)
    have h1 := hef i 1 (relativeDerivative f x s)
    simp only [inv_mul_cancel_left] at hxs
    simp only [inv_one, one_mul, hf1, relativeDerivative_apply,
      Equiv.apply_symm_apply] at h1
    exact h1.trans hxs.symm
  have hh (s : G) (hs : s ∈ S i) : h s ∈ S i := by
    apply reachable_subset_of_derivative_invariant f (S i) hqmem hs
    exact hα s
  have himage : (S i).map h.toEmbedding ⊆ S i := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hz
    exact hh s hs
  have himage_eq : (S i).map h.toEmbedding = S i := by
    apply Finset.eq_of_subset_of_card_le himage
    simp
  have hh_iff (s : G) : h s ∈ S i ↔ s ∈ S i := by
    constructor
    · intro hs
      have : h s ∈ (S i).map h.toEmbedding := by simpa [himage_eq] using hs
      obtain ⟨t, ht, hts⟩ := Finset.mem_map.mp this
      exact (h.injective hts) ▸ ht
    · exact hh s
  calc
    (S i).map α.toEquiv.toEmbedding = (S i).map f.toEmbedding := by
      apply Finset.ext
      intro z
      constructor
      · intro hz
        obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hz
        refine Finset.mem_map.mpr ⟨h s, (hh_iff s).2 hs, ?_⟩
        simp [h]
      · intro hz
        obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hz
        refine Finset.mem_map.mpr ⟨h.symm s, (hh_iff (h.symm s)).1 ?_, ?_⟩
        · simpa using hs
        · simp [h]
    _ = T i := by
      apply Finset.ext
      intro z
      constructor
      · intro hz
        obtain ⟨s, hs, hsz⟩ := Finset.mem_map.mp hz
        subst z
        have ht := (hef i 1 s).1 (by simpa using hs)
        simpa [hf1] using ht
      · intro hz
        refine Finset.mem_map.mpr ⟨f.symm z, ?_, f.apply_symm_apply z⟩
        have hs := (hef i 1 (f.symm z)).2 (by simpa [hf1] using hz)
        simpa using hs

/-- The order-ten dihedral group has the binary Cayley shadow property. -/
theorem dihedralGroupFive_hasBinaryCayleyShadow :
    HasBinaryCayleyShadow (DihedralGroup 5) := by
  unfold HasBinaryCayleyShadow
  native_decide

/-- Every finite fixed-label tuple of directed binary Cayley relations on the
order-ten dihedral group is CI. -/
theorem dihedralGroupFive_binaryRelationalCI :
    ∀ (ι : Type*) [Finite ι]
      (S T : ι → Finset (DihedralGroup 5)) (e : DihedralGroup 5 ≃ DihedralGroup 5),
      (∀ i x y, x⁻¹ * y ∈ S i ↔ (e x)⁻¹ * e y ∈ T i) →
      ∃ α : DihedralGroup 5 ≃* DihedralGroup 5,
        ∀ i, (S i).map α.toEquiv.toEmbedding = T i :=
  binaryRelationalCI_of_hasBinaryCayleyShadow _ dihedralGroupFive_hasBinaryCayleyShadow

end MathlibPlus.GroupTheory.CayleyDerivativeShadow
