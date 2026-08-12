import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim31263

private lemma union_inter_union_eq_of_cross_disjoint
    {α : Type*} [DecidableEq α]
    (s t u v : Finset α)
    (hsv : Disjoint s v) (htu : Disjoint t u) (htv : Disjoint t v) :
    (s ∪ t) ∩ (u ∪ v) = s ∩ u := by
  rw [Finset.union_inter_distrib_right, Finset.inter_union_distrib_left,
    Finset.inter_union_distrib_left]
  rw [Finset.disjoint_iff_inter_eq_empty.mp hsv,
    Finset.disjoint_iff_inter_eq_empty.mp htu,
    Finset.disjoint_iff_inter_eq_empty.mp htv]
  simp

private lemma union_diff_union_eq_of_cross_disjoint
    {α : Type*} [DecidableEq α]
    (s t u v : Finset α)
    (hsv : Disjoint s v) (htu : Disjoint t u) (htv : Disjoint t v) :
    (s ∪ t) \ (u ∪ v) = (s \ u) ∪ t := by
  ext y
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨(hsy | hty), hnot⟩
    · exact Or.inl ⟨hsy, fun hyu => hnot (Or.inl hyu)⟩
    · exact Or.inr hty
  · rintro (⟨hsy, hsnot⟩ | hty)
    · refine ⟨Or.inl hsy, ?_⟩
      intro hy
      rcases hy with hyu | hyv
      · exact hsnot hyu
      · exact (Finset.disjoint_left.mp hsv hsy hyv).elim
    · refine ⟨Or.inr hty, ?_⟩
      intro hy
      rcases hy with hyu | hyv
      · exact (Finset.disjoint_left.mp htu hty hyu).elim
      · exact (Finset.disjoint_left.mp htv hty hyv).elim

/-- The concrete three-uniform trace-pooling obstruction, including the
second two-uniform distinctness witness. -/
theorem tracePoolingWitness :
    let sunflower : Finset (Fin 8) → Finset (Fin 8) → Finset (Fin 8) → Prop :=
      fun E₁ E₂ E₃ => E₁ ∩ E₂ = E₁ ∩ E₃ ∧ E₁ ∩ E₂ = E₂ ∩ E₃
    let a : Fin 8 := 0
    let b : Fin 8 := 1
    let z : Fin 8 := 2
    let x : Fin 8 := 3
    let p : Fin 8 := 4
    let q : Fin 8 := 5
    let r : Fin 8 := 6
    let A : Finset (Fin 8) := {a, b, z}
    let B₁ : Finset (Fin 8) := {a, x, p}
    let B₂ : Finset (Fin 8) := {a, x, q}
    let C : Finset (Fin 8) := {b, x, r}
    A.card = 3 ∧ B₁.card = 3 ∧ B₂.card = 3 ∧ C.card = 3 ∧
      A ∩ B₁ = {a} ∧ A ∩ B₂ = {a} ∧ A ∩ C = {b} ∧
      B₁ ∩ B₂ = {a, x} ∧ B₁ ∩ C = {x} ∧ B₂ ∩ C = {x} ∧
      ¬ sunflower A B₁ B₂ ∧ ¬ sunflower A B₁ C ∧
      ¬ sunflower A B₂ C ∧ ¬ sunflower B₁ B₂ C ∧
      B₁ ∩ A = {a} ∧ C ∩ A = {b} ∧
      ({a} : Finset (Fin 8)) ∩ {b} = ∅ ∧
      B₁ \ A = {x, p} ∧ B₂ \ A = {x, q} ∧ C \ A = {x, r} ∧
      sunflower (B₁ \ A) (B₂ \ A) (C \ A) ∧
      let D : Finset (Fin 8) := {a, b}
      let E : Finset (Fin 8) := {a, x}
      let G : Finset (Fin 8) := {b, x}
      E ∩ D = {a} ∧ G ∩ D = {b} ∧ E \ D = {x} ∧ G \ D = {x} := by
  dsimp
  decide

/-- Mutually disjoint private padding preserves the displayed obstruction at
 every uniformity `n ≥ 3`. -/
theorem privatePaddingExtension
    (n : ℕ) (PA PB₁ PB₂ PC : Finset ℕ)
    (hn : 3 ≤ n)
    (hPAcard : PA.card = n - 3) (hPB₁card : PB₁.card = n - 3)
    (hPB₂card : PB₂.card = n - 3) (hPCcard : PC.card = n - 3)
    (hprivate : Disjoint (PA ∪ PB₁ ∪ PB₂ ∪ PC)
      ({0, 1, 2, 3, 4, 5, 6} : Finset ℕ))
    (hpads : Disjoint PA PB₁ ∧ Disjoint PA PB₂ ∧ Disjoint PA PC ∧
      Disjoint PB₁ PB₂ ∧ Disjoint PB₁ PC ∧ Disjoint PB₂ PC) :
    let sunflower : Finset ℕ → Finset ℕ → Finset ℕ → Prop :=
      fun E₁ E₂ E₃ => E₁ ∩ E₂ = E₁ ∩ E₃ ∧ E₁ ∩ E₂ = E₂ ∩ E₃
    let A₀ : Finset ℕ := {0, 1, 2}
    let B₁₀ : Finset ℕ := {0, 3, 4}
    let B₂₀ : Finset ℕ := {0, 3, 5}
    let C₀ : Finset ℕ := {1, 3, 6}
    let A : Finset ℕ := A₀ ∪ PA
    let B₁ : Finset ℕ := B₁₀ ∪ PB₁
    let B₂ : Finset ℕ := B₂₀ ∪ PB₂
    let C : Finset ℕ := C₀ ∪ PC
    A.card = n ∧ B₁.card = n ∧ B₂.card = n ∧ C.card = n ∧
      A ∩ B₁ = {0} ∧ A ∩ B₂ = {0} ∧ A ∩ C = {1} ∧
      B₁ ∩ B₂ = {0, 3} ∧ B₁ ∩ C = {3} ∧ B₂ ∩ C = {3} ∧
      ¬ sunflower A B₁ B₂ ∧ ¬ sunflower A B₁ C ∧
      ¬ sunflower A B₂ C ∧ ¬ sunflower B₁ B₂ C ∧
      sunflower (B₁ \ A) (B₂ \ A) (C \ A) := by
  dsimp
  rcases (Finset.disjoint_union_left.mp hprivate) with ⟨hpadABC, hPCbase⟩
  rcases (Finset.disjoint_union_left.mp hpadABC) with ⟨hpadAB, hPB₂base⟩
  rcases (Finset.disjoint_union_left.mp hpadAB) with ⟨hPAbase, hPB1base⟩
  rcases hpads with ⟨hPAPB1, hPAPB2, hPAPC, hPB1PB2, hPB1PC, hPB2PC⟩
  have hA0base : ({0, 1, 2} : Finset ℕ) ⊆ {0, 1, 2, 3, 4, 5, 6} := by decide
  have hB10base : ({0, 3, 4} : Finset ℕ) ⊆ {0, 1, 2, 3, 4, 5, 6} := by decide
  have hB20base : ({0, 3, 5} : Finset ℕ) ⊆ {0, 1, 2, 3, 4, 5, 6} := by decide
  have hC0base : ({1, 3, 6} : Finset ℕ) ⊆ {0, 1, 2, 3, 4, 5, 6} := by decide
  have hPA_A0 : Disjoint PA ({0, 1, 2} : Finset ℕ) :=
    Finset.disjoint_of_subset_right hA0base hPAbase
  have hPA_B10 : Disjoint PA ({0, 3, 4} : Finset ℕ) :=
    Finset.disjoint_of_subset_right hB10base hPAbase
  have hPA_B20 : Disjoint PA ({0, 3, 5} : Finset ℕ) :=
    Finset.disjoint_of_subset_right hB20base hPAbase
  have hPA_C0 : Disjoint PA ({1, 3, 6} : Finset ℕ) :=
    Finset.disjoint_of_subset_right hC0base hPAbase
  have hPB1_A0 : Disjoint PB₁ ({0, 1, 2} : Finset ℕ) :=
    Finset.disjoint_of_subset_right hA0base hPB1base
  have hPB1_B20 : Disjoint PB₁ ({0, 3, 5} : Finset ℕ) :=
    Finset.disjoint_of_subset_right hB20base hPB1base
  have hPB1_C0 : Disjoint PB₁ ({1, 3, 6} : Finset ℕ) :=
    Finset.disjoint_of_subset_right hC0base hPB1base
  have hPB2_A0 : Disjoint PB₂ ({0, 1, 2} : Finset ℕ) :=
    Finset.disjoint_of_subset_right hA0base hPB₂base
  have hPB2_B10 : Disjoint PB₂ ({0, 3, 4} : Finset ℕ) :=
    Finset.disjoint_of_subset_right hB10base hPB₂base
  have hPB2_C0 : Disjoint PB₂ ({1, 3, 6} : Finset ℕ) :=
    Finset.disjoint_of_subset_right hC0base hPB₂base
  have hPC_A0 : Disjoint PC ({0, 1, 2} : Finset ℕ) :=
    Finset.disjoint_of_subset_right hA0base hPCbase
  have hPC_B10 : Disjoint PC ({0, 3, 4} : Finset ℕ) :=
    Finset.disjoint_of_subset_right hB10base hPCbase
  have hPC_B20 : Disjoint PC ({0, 3, 5} : Finset ℕ) :=
    Finset.disjoint_of_subset_right hB20base hPCbase
  have hA : (({0, 1, 2} : Finset ℕ) ∪ PA).card = n := by
    calc
      _ = ({0, 1, 2} : Finset ℕ).card + PA.card :=
        Finset.card_union_of_disjoint hPA_A0.symm
      _ = n := by norm_num [hPAcard]; omega
  have hB1 : (({0, 3, 4} : Finset ℕ) ∪ PB₁).card = n := by
    calc
      _ = ({0, 3, 4} : Finset ℕ).card + PB₁.card :=
        Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right hB10base hPB1base).symm
      _ = n := by norm_num [hPB₁card]; omega
  have hB2 : (({0, 3, 5} : Finset ℕ) ∪ PB₂).card = n := by
    calc
      _ = ({0, 3, 5} : Finset ℕ).card + PB₂.card :=
        Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right hB20base hPB₂base).symm
      _ = n := by norm_num [hPB₂card]; omega
  have hC : (({1, 3, 6} : Finset ℕ) ∪ PC).card = n := by
    calc
      _ = ({1, 3, 6} : Finset ℕ).card + PC.card :=
        Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right hC0base hPCbase).symm
      _ = n := by norm_num [hPCcard]; omega
  have hAB : (({0, 1, 2} : Finset ℕ) ∪ PA) ∩ ({0, 3, 4} ∪ PB₁) = {0} := by
    calc
      _ = ({0, 1, 2} : Finset ℕ) ∩ {0, 3, 4} :=
        union_inter_union_eq_of_cross_disjoint _ _ _ _ hPB1_A0.symm hPA_B10 hPAPB1
      _ = {0} := by decide
  have hAB2 : (({0, 1, 2} : Finset ℕ) ∪ PA) ∩ ({0, 3, 5} ∪ PB₂) = {0} := by
    calc
      _ = ({0, 1, 2} : Finset ℕ) ∩ {0, 3, 5} :=
        union_inter_union_eq_of_cross_disjoint _ _ _ _ hPB2_A0.symm hPA_B20 hPAPB2
      _ = {0} := by decide
  have hAC : (({0, 1, 2} : Finset ℕ) ∪ PA) ∩ ({1, 3, 6} ∪ PC) = {1} := by
    calc
      _ = ({0, 1, 2} : Finset ℕ) ∩ {1, 3, 6} :=
        union_inter_union_eq_of_cross_disjoint _ _ _ _ hPC_A0.symm hPA_C0 hPAPC
      _ = {1} := by decide
  have hB1B2 : (({0, 3, 4} : Finset ℕ) ∪ PB₁) ∩ ({0, 3, 5} ∪ PB₂) = {0, 3} := by
    calc
      _ = ({0, 3, 4} : Finset ℕ) ∩ {0, 3, 5} :=
        union_inter_union_eq_of_cross_disjoint _ _ _ _ hPB2_B10.symm hPB1_B20 hPB1PB2
      _ = {0, 3} := by decide
  have hB1C : (({0, 3, 4} : Finset ℕ) ∪ PB₁) ∩ ({1, 3, 6} ∪ PC) = {3} := by
    calc
      _ = ({0, 3, 4} : Finset ℕ) ∩ {1, 3, 6} :=
        union_inter_union_eq_of_cross_disjoint _ _ _ _ hPC_B10.symm hPB1_C0 hPB1PC
      _ = {3} := by decide
  have hB2C : (({0, 3, 5} : Finset ℕ) ∪ PB₂) ∩ ({1, 3, 6} ∪ PC) = {3} := by
    calc
      _ = ({0, 3, 5} : Finset ℕ) ∩ {1, 3, 6} :=
        union_inter_union_eq_of_cross_disjoint _ _ _ _ hPC_B20.symm hPB2_C0 hPB2PC
      _ = {3} := by decide
  have hresB1 : (({0, 3, 4} : Finset ℕ) ∪ PB₁) \ (({0, 1, 2} : Finset ℕ) ∪ PA) =
      ({0, 3, 4} \ ({0, 1, 2} : Finset ℕ)) ∪ PB₁ :=
    union_diff_union_eq_of_cross_disjoint _ _ _ _ hPA_B10.symm hPB1_A0 hPAPB1.symm
  have hresB2 : (({0, 3, 5} : Finset ℕ) ∪ PB₂) \ (({0, 1, 2} : Finset ℕ) ∪ PA) =
      ({0, 3, 5} \ ({0, 1, 2} : Finset ℕ)) ∪ PB₂ :=
    union_diff_union_eq_of_cross_disjoint _ _ _ _ hPA_B20.symm hPB2_A0 hPAPB2.symm
  have hresC : (({1, 3, 6} : Finset ℕ) ∪ PC) \ (({0, 1, 2} : Finset ℕ) ∪ PA) =
      ({1, 3, 6} \ ({0, 1, 2} : Finset ℕ)) ∪ PC :=
    union_diff_union_eq_of_cross_disjoint _ _ _ _ hPA_C0.symm hPC_A0 hPAPC.symm
  have hres12 :
      (({0, 3, 4} \ ({0, 1, 2} : Finset ℕ)) ∪ PB₁) ∩
        (({0, 3, 5} \ ({0, 1, 2} : Finset ℕ)) ∪ PB₂) = {3} := by
    calc
      _ = ({0, 3, 4} \ ({0, 1, 2} : Finset ℕ)) ∩
          ({0, 3, 5} \ ({0, 1, 2} : Finset ℕ)) :=
        union_inter_union_eq_of_cross_disjoint _ _ _ _
          (Finset.disjoint_of_subset_left Finset.sdiff_subset hPB2_B10.symm)
          (Finset.disjoint_of_subset_right Finset.sdiff_subset hPB1_B20)
          hPB1PB2
      _ = {3} := by decide
  have hres13 :
      (({0, 3, 4} \ ({0, 1, 2} : Finset ℕ)) ∪ PB₁) ∩
        (({1, 3, 6} \ ({0, 1, 2} : Finset ℕ)) ∪ PC) = {3} := by
    calc
      _ = ({0, 3, 4} \ ({0, 1, 2} : Finset ℕ)) ∩
          ({1, 3, 6} \ ({0, 1, 2} : Finset ℕ)) :=
        union_inter_union_eq_of_cross_disjoint _ _ _ _
          (Finset.disjoint_of_subset_left Finset.sdiff_subset hPC_B10.symm)
          (Finset.disjoint_of_subset_right Finset.sdiff_subset hPB1_C0)
          hPB1PC
      _ = {3} := by decide
  have hres23 :
      (({0, 3, 5} \ ({0, 1, 2} : Finset ℕ)) ∪ PB₂) ∩
        (({1, 3, 6} \ ({0, 1, 2} : Finset ℕ)) ∪ PC) = {3} := by
    calc
      _ = ({0, 3, 5} \ ({0, 1, 2} : Finset ℕ)) ∩
          ({1, 3, 6} \ ({0, 1, 2} : Finset ℕ)) :=
        union_inter_union_eq_of_cross_disjoint _ _ _ _
          (Finset.disjoint_of_subset_left Finset.sdiff_subset hPC_B20.symm)
          (Finset.disjoint_of_subset_right Finset.sdiff_subset hPB2_C0)
          hPB2PC
      _ = {3} := by decide
  refine ⟨hA, hB1, hB2, hC, hAB, hAB2, hAC, hB1B2, hB1C, hB2C, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [hAB, hAB2, hB1B2] at h
    have hc := congrArg Finset.card h.2
    norm_num at hc
  · intro h
    rw [hAB, hAC, hB1C] at h
    have hm : (0 : ℕ) ∈ ({1} : Finset ℕ) := by rw [← h.1]; simp
    norm_num at hm
  · intro h
    rw [hAB2, hAC, hB2C] at h
    have hm : (0 : ℕ) ∈ ({1} : Finset ℕ) := by rw [← h.1]; simp
    norm_num at hm
  · intro h
    rw [hB1B2, hB1C, hB2C] at h
    have hc := congrArg Finset.card h.1
    norm_num at hc
  · rw [hresB1, hresB2, hresC]
    exact ⟨hres12.trans hres13.symm, hres12.trans hres23.symm⟩

/-- There are such mutually disjoint private paddings for every uniformity
`n ≥ 3`; the blocks are placed in the natural numbers starting at `7`. -/
theorem privatePadding_exists (n : ℕ) (_hn : 3 ≤ n) :
    ∃ (PA PB₁ PB₂ PC : Finset ℕ),
      PA.card = n - 3 ∧ PB₁.card = n - 3 ∧ PB₂.card = n - 3 ∧ PC.card = n - 3 ∧
      Disjoint (PA ∪ PB₁ ∪ PB₂ ∪ PC)
        ({0, 1, 2, 3, 4, 5, 6} : Finset ℕ) ∧
      Disjoint PA PB₁ ∧ Disjoint PA PB₂ ∧ Disjoint PA PC ∧
      Disjoint PB₁ PB₂ ∧ Disjoint PB₁ PC ∧ Disjoint PB₂ PC := by
  let k := n - 3
  let block : ℕ → Finset ℕ := fun o =>
    (Finset.range k).map
      ⟨fun i => 7 + o * k + i, by
        intro i j hij
        simpa [Nat.add_assoc] using hij⟩
  have hcard (o : ℕ) : (block o).card = k := by
    dsimp [block]
    simp
  have hdisj (o o' : ℕ) (hoo : o ≠ o') (ho : o ≤ 3) (ho' : o' ≤ 3) :
      Disjoint (block o) (block o') := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    simp only [block, Finset.mem_map, Finset.mem_range] at hy hy'
    rcases hy with ⟨i, hi, hiy⟩
    rcases hy' with ⟨j, hj, hjy⟩
    change 7 + o * k + i = y at hiy
    change 7 + o' * k + j = y at hjy
    interval_cases o <;> interval_cases o' <;> omega
  have hbase (o : ℕ) (ho : o ≤ 3) :
      Disjoint (block o) ({0, 1, 2, 3, 4, 5, 6} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro y hy hybase
    simp only [block, Finset.mem_map, Finset.mem_range] at hy
    rcases hy with ⟨i, hi, hiy⟩
    change 7 + o * k + i = y at hiy
    simp at hybase
    have hprod : 0 ≤ o * k := Nat.zero_le _
    omega
  refine ⟨block 0, block 1, block 2, block 3, ?_⟩
  have h01 := hdisj 0 1 (by omega) (by omega) (by omega)
  have h02 := hdisj 0 2 (by omega) (by omega) (by omega)
  have h03 := hdisj 0 3 (by omega) (by omega) (by omega)
  have h12 := hdisj 1 2 (by omega) (by omega) (by omega)
  have h13 := hdisj 1 3 (by omega) (by omega) (by omega)
  have h23 := hdisj 2 3 (by omega) (by omega) (by omega)
  have hb0 := hbase 0 (by omega)
  have hb1 := hbase 1 (by omega)
  have hb2 := hbase 2 (by omega)
  have hb3 := hbase 3 (by omega)
  have hpriv :
      Disjoint (block 0 ∪ block 1 ∪ block 2 ∪ block 3)
        ({0, 1, 2, 3, 4, 5, 6} : Finset ℕ) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left,
      Finset.disjoint_union_left]
    exact ⟨⟨⟨hb0, hb1⟩, hb2⟩, hb3⟩
  have hk : k = n - 3 := rfl
  simp only [hcard]
  exact ⟨hk, hk, hk, hk, hpriv, h01, h02, h03, h12, h13, h23⟩

end MathlibPlus.Combinatorics.Claim31263
