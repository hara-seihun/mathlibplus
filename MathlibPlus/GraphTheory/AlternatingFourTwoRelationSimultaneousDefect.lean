import Mathlib

namespace MathlibPlus.GraphTheory.AlternatingFourTwoRelationSimultaneousDefect

private abbrev G := alternatingGroup (Fin 4)
private def p0 : G := ⟨1, by change Equiv.Perm.sign 1 = 1; native_decide⟩
private def p1 : G := ⟨(Equiv.swap (1 : Fin 4) 2) * Equiv.swap 2 3, by change Equiv.Perm.sign ((Equiv.swap (1 : Fin 4) 2) * Equiv.swap 2 3) = 1; native_decide⟩
private def p2 : G := ⟨(Equiv.swap (1 : Fin 4) 2) * Equiv.swap 1 3, by change Equiv.Perm.sign ((Equiv.swap (1 : Fin 4) 2) * Equiv.swap 1 3) = 1; native_decide⟩
private def p3 : G := ⟨(Equiv.swap (0 : Fin 4) 1) * Equiv.swap 2 3, by change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 1) * Equiv.swap 2 3) = 1; native_decide⟩
private def p4 : G := ⟨(Equiv.swap (0 : Fin 4) 1) * Equiv.swap 1 2, by change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 1) * Equiv.swap 1 2) = 1; native_decide⟩
private def p5 : G := ⟨(Equiv.swap (0 : Fin 4) 1) * Equiv.swap 1 3, by change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 1) * Equiv.swap 1 3) = 1; native_decide⟩
private def p6 : G := ⟨(Equiv.swap (0 : Fin 4) 2) * Equiv.swap 1 2, by change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 2) * Equiv.swap 1 2) = 1; native_decide⟩
private def p7 : G := ⟨(Equiv.swap (0 : Fin 4) 2) * Equiv.swap 2 3, by change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 2) * Equiv.swap 2 3) = 1; native_decide⟩
private def p8 : G := ⟨(Equiv.swap (0 : Fin 4) 2) * Equiv.swap 1 3, by change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 2) * Equiv.swap 1 3) = 1; native_decide⟩
private def p9 : G := ⟨(Equiv.swap (0 : Fin 4) 3) * Equiv.swap 1 3, by change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 3) * Equiv.swap 1 3) = 1; native_decide⟩
private def p10 : G := ⟨(Equiv.swap (0 : Fin 4) 3) * Equiv.swap 2 3, by change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 3) * Equiv.swap 2 3) = 1; native_decide⟩
private def p11 : G := ⟨(Equiv.swap (0 : Fin 4) 3) * Equiv.swap 1 2, by change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 3) * Equiv.swap 1 2) = 1; native_decide⟩
private def g : Fin 12 → G := ![p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11]
private def gInv (x : G) : Fin 12 :=
  if x = p0 then 0 else if x = p1 then 1 else if x = p2 then 2 else
  if x = p3 then 3 else if x = p4 then 4 else if x = p5 then 5 else
  if x = p6 then 6 else if x = p7 then 7 else if x = p8 then 8 else
  if x = p9 then 9 else if x = p10 then 10 else 11
private theorem g_left : ∀ i : Fin 12, gInv (g i) = i := by native_decide
private theorem g_right : ∀ x : G, g (gInv x) = x := by native_decide
private def e : Fin 12 ≃ G :=
  { toFun := g, invFun := gInv, left_inv := g_left, right_inv := g_right }
private def qi : Fin 12 → Fin 12 := ![0,5,7,8,4,1,6,2,3,9,10,11]
private theorem qi_left : ∀ i : Fin 12, qi (qi i) = i := by native_decide
private def qIndex : Fin 12 ≃ Fin 12 :=
  { toFun := qi, invFun := qi, left_inv := qi_left, right_inv := qi_left }
private def q : G ≃ G := e.symm.trans (qIndex.trans e)
private def idxS : Fin 2 → Finset (Fin 12) := ![{3}, {2,4,7,8,9}]
private def idxT : Fin 2 → Finset (Fin 12) := ![{8}, {2,3,4,7,9}]
private def S (i : Fin 2) : Set G := {x | e.symm x ∈ idxS i}
private def T (i : Fin 2) : Set G := {x | e.symm x ∈ idxT i}
private def conjFun (c : Equiv.Perm (Fin 4)) (x : G) : G :=
  ⟨c * x.1 * c⁻¹, by
    change Equiv.Perm.sign (c * x.1 * c⁻¹) = 1
    simp only [map_mul]
    have hx := x.property
    change Equiv.Perm.sign x.1 = 1 at hx
    rw [hx]
    simp⟩
private def conjEquiv (c : Equiv.Perm (Fin 4)) : G ≃ G :=
  { toFun := conjFun c
    invFun := conjFun c⁻¹
    left_inv := by
      intro x
      apply Subtype.ext
      change c⁻¹ * (c * x.1 * c⁻¹) * (c⁻¹)⁻¹ = x.1
      group
    right_inv := by
      intro x
      apply Subtype.ext
      change c * (c⁻¹ * x.1 * (c⁻¹)⁻¹) * c⁻¹ = x.1
      group }
private def conjMulEquiv (c : Equiv.Perm (Fin 4)) : G ≃* G :=
  { toEquiv := conjEquiv c
    map_mul' := by
      intro x y
      apply Subtype.ext
      change c * (x.1 * y.1) * c⁻¹ =
        (c * x.1 * c⁻¹) * (c * y.1 * c⁻¹)
      group }
private def c0 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (1 : Fin 4) 2) * Equiv.swap 2 3
private def c1 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (1 : Fin 4) 2) * Equiv.swap 1 3
private theorem hS0 : S 0 = ({e 3} : Set G) := by
  ext x
  simp [S, idxS]
  native_decide +revert
private theorem hS1 : S 1 = ({e 2, e 4, e 7, e 8, e 9} : Set G) := by
  ext x
  simp [S, idxS]
  native_decide +revert
private theorem hT0 : T 0 = ({e 8} : Set G) := by
  ext x
  simp [T, idxT]
  native_decide +revert
private theorem hT1 : T 1 = ({e 2, e 3, e 4, e 7, e 9} : Set G) := by
  ext x
  simp [T, idxT]
  native_decide +revert
private theorem c0_3 : (conjMulEquiv c0) (e 3) = e 8 := by native_decide
private theorem c1_on_S1 : (conjMulEquiv c1) (e 2) = e 2 ∧
    (conjMulEquiv c1) (e 4) = e 9 ∧
    (conjMulEquiv c1) (e 7) = e 4 ∧
    (conjMulEquiv c1) (e 8) = e 3 ∧
    (conjMulEquiv c1) (e 9) = e 7 := by native_decide

private theorem q_one : q 1 = 1 := by native_decide
private theorem q_involutive : ∀ x : G, q (q x) = x := by native_decide
private theorem relation_iso : ∀ i : Fin 2, ∀ x y : G,
    x⁻¹ * y ∈ S i ↔ (q x)⁻¹ * q y ∈ T i := by
  simp only [S, T]
  native_decide
private theorem identity_free : ∀ i : Fin 2, 1 ∉ S i ∧ 1 ∉ T i := by
  simp only [S, T]
  native_decide
private theorem disjoint_relations :
    Disjoint (S 0) (S 1) ∧ Disjoint (T 0) (T 1) := by
  constructor
  · rw [Set.disjoint_left]
    simp only [S]
    native_decide +revert
  · rw [Set.disjoint_left]
    simp only [T]
    native_decide +revert
private theorem relation_sizes :
    Set.ncard (S 0) = 1 ∧ Set.ncard (S 1) = 5 ∧
      Set.ncard (T 0) = 1 ∧ Set.ncard (T 1) = 5 := by
  rw [hS0, hS1, hT0, hT1]
  simp
private theorem q_on_relations :
    q (e 3) = e 8 ∧ q (e 2) = e 7 ∧ q (e 4) = e 4 ∧
      q (e 7) = e 2 ∧ q (e 8) = e 3 ∧ q (e 9) = e 9 := by
  native_decide
private theorem q_symm_apply (x : G) : q.symm x = q x := by
  apply q.injective
  rw [q.apply_symm_apply, q_involutive]
private theorem q_image : ∀ i : Fin 2, T i = q '' S i := by
  obtain ⟨q3, q2, q4, q7, q8, q9⟩ := q_on_relations
  have qsym := q_symm_apply
  intro i
  fin_cases i
  · change T 0 = q '' S 0
    rw [hS0, hT0]
    ext x
    simp [q3]
  · change T 1 = q '' S 1
    rw [hS1, hT1]
    ext x
    simp [qsym, q2, q4, q7, q8, q9]
    native_decide +revert
private theorem aut0_image : (conjMulEquiv c0) '' S 0 = T 0 := by
  rw [hS0, hT0]
  ext x
  simp [c0_3] <;> native_decide +revert
private theorem aut1_image : (conjMulEquiv c1) '' S 1 = T 1 := by
  obtain ⟨h2, h4, h7, h8, h9⟩ := c1_on_S1
  rw [hS1, hT1]
  ext x
  simp [h2, h4, h7, h8, h9, eq_comm] <;> native_decide +revert

private def word (a b : G) : Fin 12 → G :=
  ![1, a, a⁻¹, b, b * a⁻¹, b * a, a * b, a * b * a,
    a * b * a⁻¹, a⁻¹ * b, a⁻¹ * b * a⁻¹, a⁻¹ * b * a]

private theorem word_generators : ∀ i : Fin 12, word p1 p3 i = e i := by
  native_decide

private theorem bad_word : ∀ j : Fin 12, ∃ i : Fin 12,
    i ∈ idxS 1 ∧ e.symm (word (e j) (e 8) i) ∉ idxT 1 := by
  native_decide

private theorem map_word (α : G ≃* G) (i : Fin 12) :
    α (e i) = word (α p1) (α p3) i := by
  rw [← word_generators i]
  fin_cases i <;> simp [word]

private theorem no_common (α : G ≃* G)
    (h0 : α '' S 0 = T 0) (h1 : α '' S 1 = T 1) : False := by
  have hp3S : p3 ∈ S 0 := by
    rw [hS0]
    native_decide
  have hp3T : α p3 ∈ T 0 := by
    rw [← h0]
    exact ⟨p3, hp3S, rfl⟩
  have hB : α p3 = e 8 := by
    rw [hT0] at hp3T
    simpa using hp3T
  let j : Fin 12 := e.symm (α p1)
  have hA : α p1 = e j := by
    dsimp [j]
    exact (e.apply_symm_apply _).symm
  obtain ⟨i, hiS, hiBad⟩ := bad_word j
  have hiS' : e i ∈ S 1 := by
    simp [S, hiS]
  have hiT : α (e i) ∈ T 1 := by
    rw [← h1]
    exact ⟨e i, hiS', rfl⟩
  have hword : α (e i) = word (e j) (e 8) i := by
    rw [map_word, hA, hB]
  have hiT' : e.symm (α (e i)) ∈ idxT 1 := by
    simpa [T] using hiT
  rw [hword] at hiT'
  exact hiBad hiT'

private theorem my_conj_injective :
    Function.Injective (fun c : Equiv.Perm (Fin 4) => conjMulEquiv c) := by
  native_decide

private def isGroupMap (a b : G) : Prop :=
  (∀ i j : Fin 12,
    word a b (e.symm (e i * e j)) = word a b i * word a b j) ∧
  Function.Injective (word a b)

private theorem classify_pair : ∀ a b : G, isGroupMap a b →
    ∃ c : Equiv.Perm (Fin 4),
      a = conjMulEquiv c p1 ∧ b = conjMulEquiv c p3 := by
  simp only [isGroupMap]
  native_decide

private theorem isGroupMap_of_mulEquiv (α : G ≃* G) :
    isGroupMap (α p1) (α p3) := by
  constructor
  · intro i j
    calc
      word (α p1) (α p3) (e.symm (e i * e j)) =
          α (e (e.symm (e i * e j))) := (map_word α _).symm
      _ = α (e i * e j) := by rw [e.apply_symm_apply]
      _ = α (e i) * α (e j) := α.map_mul _ _
      _ = word (α p1) (α p3) i * word (α p1) (α p3) j := by
        rw [map_word, map_word]
  · intro i j hij
    apply e.injective
    apply α.injective
    rw [map_word, map_word]
    exact hij

private theorem all_aut_conj (α : G ≃* G) :
    ∃ c : Equiv.Perm (Fin 4), α = conjMulEquiv c := by
  obtain ⟨c, hA, hB⟩ := classify_pair (α p1) (α p3)
    (isGroupMap_of_mulEquiv α)
  refine ⟨c, ?_⟩
  apply MulEquiv.ext
  intro x
  let i : Fin 12 := e.symm x
  have hx : e i = x := e.apply_symm_apply _
  calc
    α x = α (e i) := by rw [hx]
    _ = word (α p1) (α p3) i := map_word α i
    _ = word ((conjMulEquiv c) p1) ((conjMulEquiv c) p3) i := by rw [hA, hB]
    _ = (conjMulEquiv c) (e i) := (map_word (conjMulEquiv c) i).symm
    _ = (conjMulEquiv c) x := by rw [hx]

private abbrev trPredicate (i : Fin 2) (c : Equiv.Perm (Fin 4)) : Prop :=
  ∀ j : Fin 12, j ∈ idxS i ↔
    e.symm ((conjMulEquiv c) (e j)) ∈ idxT i

private theorem tr_filter_card0 : (Finset.univ.filter (fun c : Equiv.Perm (Fin 4) => trPredicate 0 c)).card = 8 := by
  simp only [trPredicate]
  native_decide
private theorem tr_filter_card1 : (Finset.univ.filter (fun c : Equiv.Perm (Fin 4) => trPredicate 1 c)).card = 4 := by
  simp only [trPredicate]
  native_decide

private theorem trPredicate_iff (i : Fin 2) (c : Equiv.Perm (Fin 4)) :
    trPredicate i c ↔ (conjMulEquiv c) '' S i = T i := by
  constructor
  · intro h
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      let k : Fin 12 := e.symm y
      have hk : e k = y := e.apply_symm_apply _
      have hks : k ∈ idxS i := by simpa [S] using hy
      have hkt : e.symm ((conjMulEquiv c) (e k)) ∈ idxT i := (h k).mp hks
      simpa [T, hk] using hkt
    · intro hx
      let y : G := (conjMulEquiv c).symm x
      have hyt : e.symm ((conjMulEquiv c) y) ∈ idxT i := by
        rw [show (conjMulEquiv c) y = x from (conjMulEquiv c).apply_symm_apply x]
        simpa [T] using hx
      rw [← e.apply_symm_apply y] at hyt
      have hys : e.symm y ∈ idxS i := (h (e.symm y)).mpr hyt
      refine ⟨y, ?_, (conjMulEquiv c).apply_symm_apply x⟩
      simpa [S] using hys
  · intro h j
    have hmem : e j ∈ S i ↔ (conjMulEquiv c) (e j) ∈ T i := by
      rw [← h]
      constructor
      · intro hj
        exact ⟨e j, hj, rfl⟩
      · intro hj
        rcases hj with ⟨y, hy, heq⟩
        have : y = e j := (conjMulEquiv c).injective heq
        simpa [this] using hy
    simpa [S, T] using hmem

private abbrev CTrans (i : Fin 2) :=
  {c : Equiv.Perm (Fin 4) // trPredicate i c}
private abbrev ATrans (i : Fin 2) :=
  {α : G ≃* G // α '' S i = T i}

private theorem cTrans_card0 : Fintype.card (CTrans 0) = 8 := by
  simp only [CTrans, trPredicate]
  native_decide
private theorem cTrans_card1 : Fintype.card (CTrans 1) = 4 := by
  simp only [CTrans, trPredicate]
  native_decide

private noncomputable def autEquiv : Equiv.Perm (Fin 4) ≃ (G ≃* G) :=
  Equiv.ofBijective (fun c => conjMulEquiv c)
    ⟨my_conj_injective, by
      intro α
      obtain ⟨c, h⟩ := all_aut_conj α
      exact ⟨c, h.symm⟩⟩

private noncomputable def transporterEquiv (i : Fin 2) : CTrans i ≃ ATrans i :=
  Equiv.subtypeEquiv autEquiv (fun c => trPredicate_iff i c)

private theorem transporter_card0 : Fintype.card (ATrans 0) = 8 := by
  rw [← Fintype.card_congr (transporterEquiv 0)]
  simp only [CTrans, trPredicate]
  native_decide
private theorem transporter_card1 : Fintype.card (ATrans 1) = 4 := by
  rw [← Fintype.card_congr (transporterEquiv 1)]
  simp only [CTrans, trPredicate]
  native_decide

end MathlibPlus.GraphTheory.AlternatingFourTwoRelationSimultaneousDefect

namespace MathlibPlus.Open.GraphTheory

/--
The exact two-relation right-Cayley witness in the indexed alternating group
`A₄`.  The relation isomorphism is not required to be a homomorphism; the two
coordinate transporter fibres are nevertheless counted among all group
automorphisms and are disjoint.
-/
def alternatingFourTwoRelationSimultaneousDefect : Prop :=
  let G := alternatingGroup (Fin 4)
  ∃ (S T : Fin 2 → Set G) (q : G ≃ G),
    q 1 = 1 ∧
    (∀ x : G, q (q x) = x) ∧
    Disjoint (S 0) (S 1) ∧
    Disjoint (T 0) (T 1) ∧
    (∀ i : Fin 2, 1 ∉ S i ∧ 1 ∉ T i) ∧
    Set.ncard (S 0) = 1 ∧ Set.ncard (S 1) = 5 ∧
      Set.ncard (T 0) = 1 ∧ Set.ncard (T 1) = 5 ∧
    (∀ i : Fin 2, ∀ x y : G,
      x⁻¹ * y ∈ S i ↔ (q x)⁻¹ * q y ∈ T i) ∧
    (∀ i : Fin 2, T i = q '' S i) ∧
    (∃ α₀ : G ≃* G, α₀ '' S 0 = T 0) ∧
    (∃ α₁ : G ≃* G, α₁ '' S 1 = T 1) ∧
    (∀ α : G ≃* G, ¬ (α '' S 0 = T 0 ∧ α '' S 1 = T 1)) ∧
    Fintype.card {α : G ≃* G // α '' S 0 = T 0} = 8 ∧
    Fintype.card {α : G ≃* G // α '' S 1 = T 1} = 4

end MathlibPlus.Open.GraphTheory

namespace MathlibPlus.GraphTheory.AlternatingFourTwoRelationSimultaneousDefect

theorem alternatingFourTwoRelationSimultaneousDefect_proof :
    MathlibPlus.Open.GraphTheory.alternatingFourTwoRelationSimultaneousDefect := by
  dsimp [MathlibPlus.Open.GraphTheory.alternatingFourTwoRelationSimultaneousDefect]
  obtain ⟨hdisjS, hdisjT⟩ := disjoint_relations
  obtain ⟨hs0, hs1, ht0, ht1⟩ := relation_sizes
  refine ⟨S, T, q, q_one, q_involutive, hdisjS, hdisjT, identity_free,
    hs0, hs1, ht0, ht1, relation_iso, q_image,
    ⟨conjMulEquiv c0, aut0_image⟩,
    ⟨conjMulEquiv c1, aut1_image⟩, ?_, transporter_card0, transporter_card1⟩
  intro α hα
  exact no_common α hα.1 hα.2

end MathlibPlus.GraphTheory.AlternatingFourTwoRelationSimultaneousDefect
