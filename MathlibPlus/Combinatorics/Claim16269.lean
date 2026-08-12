import Mathlib

namespace MathlibPlus.Combinatorics.Claim16269

/-- Two explicit triples have the same singleton and pair-intersection cardinality,
while one is a sunflower and the other is not; their triple intersections and
unions distinguish them. -/
theorem equalIntersectionSizesDoNotCharacterizeSunflowers
    {α : Type*} [DecidableEq α]
    (n : ℕ) (hn : 2 ≤ n) (C : Finset α) (a b c d : α)
    (hC : C.card = n - 2)
    (ha : a ∉ C) (hb : b ∉ C) (hc : c ∉ C) (hd : d ∉ C)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (C ∪ {a, b}).card = n ∧
      (C ∪ {a, c}).card = n ∧
      (C ∪ {a, d}).card = n ∧
      (C ∪ {b, c}).card = n ∧
      (C ∪ {a, b}) ∩ (C ∪ {a, c}) = C ∪ {a} ∧
      (C ∪ {a, b}) ∩ (C ∪ {a, d}) = C ∪ {a} ∧
      (C ∪ {a, c}) ∩ (C ∪ {a, d}) = C ∪ {a} ∧
      (C ∪ {a, b}) ∩ (C ∪ {a, c}) = C ∪ {a} ∧
      (C ∪ {a, b}) ∩ (C ∪ {b, c}) = C ∪ {b} ∧
      (C ∪ {a, c}) ∩ (C ∪ {b, c}) = C ∪ {c} ∧
      (C ∪ {a} ≠ C ∪ {b}) ∧
      (C ∪ {a}) ≠ C ∪ {c} ∧
      (∃ core : Finset α,
        (C ∪ {a, b}) ∩ (C ∪ {a, c}) = core ∧
        (C ∪ {a, b}) ∩ (C ∪ {a, d}) = core ∧
        (C ∪ {a, c}) ∩ (C ∪ {a, d}) = core) ∧
      (¬ ∃ core : Finset α,
        (C ∪ {a, b}) ∩ (C ∪ {a, c}) = core ∧
        (C ∪ {a, b}) ∩ (C ∪ {b, c}) = core ∧
        (C ∪ {a, c}) ∩ (C ∪ {b, c}) = core) ∧
      ((C ∪ {a, b}) ∩ (C ∪ {a, c}) ∩ (C ∪ {a, d})).card = n - 1 ∧
      ((C ∪ {a, b}) ∩ (C ∪ {b, c}) ∩ (C ∪ {a, c})).card = n - 2 ∧
      ((C ∪ {a, b}) ∪ (C ∪ {a, c}) ∪ (C ∪ {a, d})).card = n + 2 ∧
      ((C ∪ {a, b}) ∪ (C ∪ {b, c}) ∪ (C ∪ {a, c})).card = n + 1 := by
  classical
  have hcard1 (x : α) (hx : x ∉ C) : (C ∪ {x}).card = n - 1 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hx)]
    simp [hC]
    omega
  have hcard2 (x y : α) (hx : x ∉ C) (hy : y ∉ C) (hxy : x ≠ y) :
      (C ∪ {x, y}).card = n := by
    have hdis : Disjoint C ({x, y} : Finset α) := by
      refine Finset.disjoint_left.2 ?_
      intro z hzC hzxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzxy
      rcases hzxy with rfl | rfl
      · exact hx hzC
      · exact hy hzC
    rw [Finset.card_union_of_disjoint hdis]
    simp [hxy, hC]
    omega
  have hcard3 (x y z : α) (hx : x ∉ C) (hy : y ∉ C) (hz : z ∉ C)
      (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
      (C ∪ {x, y, z}).card = n + 1 := by
    have hdis : Disjoint C ({x, y, z} : Finset α) := by
      refine Finset.disjoint_left.2 ?_
      intro w hwC hwxyz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwxyz
      rcases hwxyz with rfl | rfl | rfl
      · exact hx hwC
      · exact hy hwC
      · exact hz hwC
    rw [Finset.card_union_of_disjoint hdis]
    simp [hxy, hxz, hyz, hC]
    omega
  have hcard4 (x y z w : α) (hx : x ∉ C) (hy : y ∉ C) (hz : z ∉ C)
      (hw : w ∉ C) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
      (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
      (C ∪ {x, y, z, w}).card = n + 2 := by
    have hdis : Disjoint C ({x, y, z, w} : Finset α) := by
      refine Finset.disjoint_left.2 ?_
      intro v hvC hvxyzw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvxyzw
      rcases hvxyzw with rfl | rfl | rfl | rfl
      · exact hx hvC
      · exact hy hvC
      · exact hz hvC
      · exact hw hvC
    rw [Finset.card_union_of_disjoint hdis]
    simp [hxy, hxz, hxw, hyz, hyw, hzw, hC]
    omega
  have hinter (x y z : α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
      (C ∪ {x, y}) ∩ (C ∪ {x, z}) = C ∪ {x} := by
    calc
      (C ∪ {x, y}) ∩ (C ∪ {x, z}) = C ∪ ({x, y} ∩ {x, z}) := by
        symm
        exact Finset.union_inter_distrib_left C {x, y} {x, z}
      _ = C ∪ {x} := by
        congr 1
        ext v
        simp [hxy, hxz, hyz]
  have hinter' (x y z : α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
      (C ∪ {x, y}) ∩ (C ∪ {y, z}) = C ∪ {y} := by
    calc
      (C ∪ {x, y}) ∩ (C ∪ {y, z}) = C ∪ ({x, y} ∩ {y, z}) := by
        symm
        exact Finset.union_inter_distrib_left C {x, y} {y, z}
      _ = C ∪ {y} := by
        congr 1
        ext v
        simp [hxy, hxz, hyz]
  have hneq (x y : α) (hx : x ∉ C) (hy : y ∉ C) (hxy : x ≠ y) :
      C ∪ {x} ≠ C ∪ {y} := by
    intro h
    have hxin : x ∈ C ∪ {x} := by simp
    have hxout : x ∉ C ∪ {y} := by simp [hx, hxy]
    exact hxout (h ▸ hxin)
  have hunionA :
      (C ∪ {a, b}) ∪ (C ∪ {a, c}) ∪ (C ∪ {a, d}) = C ∪ {a, b, c, d} := by
    ext v
    simp [or_assoc, or_left_comm, or_comm]
  have hunionB :
      (C ∪ {a, b}) ∪ (C ∪ {b, c}) ∪ (C ∪ {a, c}) = C ∪ {a, b, c} := by
    ext v
    simp [or_assoc, or_left_comm, or_comm]
  have htripleA :
      (C ∪ {a, b}) ∩ (C ∪ {a, c}) ∩ (C ∪ {a, d}) = C ∪ {a} := by
    rw [hinter a b c hab hac hbc]
    apply Finset.inter_eq_left.mpr
    intro v hv
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
    rcases hv with hvC | rfl
    · exact Or.inl hvC
    · exact Or.inr (Or.inl rfl)
  have htripleB :
      (C ∪ {a, b}) ∩ (C ∪ {b, c}) ∩ (C ∪ {a, c}) = C := by
    rw [hinter' a b c hab hac hbc]
    ext v
    by_cases hv : v ∈ C
    · simp [hv]
    · simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, hv, false_or]
      constructor
      · rintro ⟨rfl, rfl | rfl⟩
        · exact False.elim (hab rfl)
        · exact False.elim (hbc rfl)
      · intro hvfalse
        exact False.elim hvfalse
  have hpabac := hinter a b c hab hac hbc
  have hpabad := hinter a b d hab had hbd
  have hpacad := hinter a c d hac had hcd
  have hpbabc := hinter' a b c hab hac hbc
  have hpbcac :
      (C ∪ {a, c}) ∩ (C ∪ {b, c}) = C ∪ {c} := by
    simpa [Finset.insert_comm] using hinter' a c b hac hab hbc.symm
  have hneab := hneq a b ha hb hab
  have hneac := hneq a c ha hc hac
  refine ⟨hcard2 a b ha hb hab, hcard2 a c ha hc hac, hcard2 a d ha hd had,
    hcard2 b c hb hc hbc, hpabac, hpabad, hpacad, hpabac, hpbabc, hpbcac,
    hneab, hneac, ⟨C ∪ {a}, hpabac, hpabad, hpacad⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨core, h1, h2, h3⟩
    exact hneab (hpabac.symm.trans (h1.trans (h2.symm.trans hpbabc)))
  · rw [htripleA, hcard1 a ha]
  · rw [htripleB]
    exact hC
  · rw [hunionA, hcard4 a b c d ha hb hc hd hab hac had hbc hbd hcd]
  · rw [hunionB, hcard3 a b c ha hb hc hab hac hbc]

end MathlibPlus.Combinatorics.Claim16269
