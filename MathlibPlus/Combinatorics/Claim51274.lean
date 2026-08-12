import Mathlib

namespace MathlibPlus.Combinatorics.Claim51274

/-- Claim 51274: for `k ≥ 3` and `q = k - 1`, the word-to-set map for
block transversals is injective, every member has exactly one point in each
block, and the family has cardinality `q^n`.

The source's one-based finite sets are represented by the cardinality-equivalent
zero-based types `Fin n` and `Fin q`. The construction objects are theorem-local
so this statement submission does not introduce unreviewed public definitions. -/
theorem claim51274 (k n : ℕ) (_hk : 3 ≤ k) :
    let q := k - 1
    let Point := Fin n × Fin q
    let block : Fin n → Finset Point :=
      fun j => Finset.univ.image (fun b : Fin q => (j, b))
    let transversal : (Fin n → Fin q) → Finset Point :=
      fun x => Finset.univ.image (fun j : Fin n => (j, x j))
    let transversals : Finset (Finset Point) :=
      Finset.univ.image transversal
    Function.Injective transversal ∧
      (∀ T, T ∈ transversals →
        ∀ j : Fin n, ∃! b : Fin q, (j, b) ∈ T ∧ (j, b) ∈ block j) ∧
      transversals.card = q ^ n := by
  let q := k - 1
  let Point := Fin n × Fin q
  let block : Fin n → Finset Point :=
    fun j => Finset.univ.image (fun b : Fin q => (j, b))
  let transversal : (Fin n → Fin q) → Finset Point :=
    fun x => Finset.univ.image (fun j : Fin n => (j, x j))
  let transversals : Finset (Finset Point) :=
    Finset.univ.image transversal
  change Function.Injective transversal ∧
    (∀ T, T ∈ transversals →
      ∀ j : Fin n, ∃! b : Fin q, (j, b) ∈ T ∧ (j, b) ∈ block j) ∧
    transversals.card = q ^ n
  have hblock (j : Fin n) (b : Fin q) : (j, b) ∈ block j := by
    simp [block]
  have hmem (x : Fin n → Fin q) (j : Fin n) :
      (j, x j) ∈ transversal x := by
    simp [transversal]
  have huniq (x : Fin n → Fin q) (j : Fin n) (b : Fin q)
      (hb : (j, b) ∈ transversal x) : b = x j := by
    simp only [transversal, Finset.mem_image, Finset.mem_univ, true_and] at hb
    rcases hb with ⟨i, h⟩
    cases h
    rfl
  have hinj : Function.Injective transversal := by
    intro x y h
    funext j
    exact huniq y j (x j) (h ▸ hmem x j)
  have htrans (x : Fin n → Fin q) :
      ∀ j : Fin n, ∃! b : Fin q,
        (j, b) ∈ transversal x ∧ (j, b) ∈ block j := by
    intro j
    refine ⟨x j, ⟨hmem x j, hblock j (x j)⟩, ?_⟩
    intro b hb
    exact huniq x j b hb.1
  have hcard : transversals.card = q ^ n := by
    change (Finset.image transversal Finset.univ).card = q ^ n
    rw [Finset.card_image_of_injective _ hinj]
    simp
  refine ⟨hinj, ?_, hcard⟩
  intro T hT j
  rcases Finset.mem_image.mp hT with ⟨x, -, rfl⟩
  exact htrans x j

end MathlibPlus.Combinatorics.Claim51274
