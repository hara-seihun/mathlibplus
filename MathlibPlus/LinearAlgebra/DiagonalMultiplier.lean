import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.DiagonalMultiplier

/-- The image of a diagonal two-coordinate multiplier minus the identity.

The map `x ↦ ((a - 1) * x.1, (d - 1) * x.2)` is the coordinate form of
`diag a d - I`.  This proposition records the complete zero/axis/plane image
trichotomy without introducing a public matrix definition. -/
theorem diagonalRange_trichotomy {K : Type*} [Field K] (a d : K) :
    let f : K × K → K × K := fun x =>
      ((a - 1) * x.1, (d - 1) * x.2)
    ((a = 1 ∧ d = 1) ∧ Set.range f = {(0, 0)}) ∨
      ((a ≠ 1 ∧ d = 1) ∧ Set.range f = {y | y.2 = 0}) ∨
      ((a = 1 ∧ d ≠ 1) ∧ Set.range f = {y | y.1 = 0}) ∨
      ((a ≠ 1 ∧ d ≠ 1) ∧ Set.range f = Set.univ) := by
  dsimp
  by_cases ha : a = 1
  · by_cases hd : d = 1
    · left
      refine ⟨⟨ha, hd⟩, ?_⟩
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        simp [ha, hd]
      · intro hy
        simp only [Set.mem_singleton_iff] at hy
        rcases hy with rfl
        exact ⟨(0, 0), by simp [ha, hd]⟩
    · right
      right
      left
      refine ⟨⟨ha, hd⟩, ?_⟩
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        simp [ha]
      · intro hy
        rcases y with ⟨y1, y2⟩
        refine ⟨(0, (d - 1)⁻¹ * y2), ?_⟩
        simp_all [sub_ne_zero.mpr hd]
  · by_cases hd : d = 1
    · right
      left
      refine ⟨⟨ha, hd⟩, ?_⟩
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        simp [hd]
      · intro hy
        rcases y with ⟨y1, y2⟩
        refine ⟨((a - 1)⁻¹ * y1, 0), ?_⟩
        simp_all [sub_ne_zero.mpr ha]
    · right
      right
      right
      refine ⟨⟨ha, hd⟩, ?_⟩
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        simp
      · intro hy
        refine ⟨((a - 1)⁻¹ * y.1, (d - 1)⁻¹ * y.2), ?_⟩
        simp [sub_ne_zero.mpr ha, sub_ne_zero.mpr hd]

/-- A diagonal multiplier whose image after subtracting the identity lies in a
non-coordinate line must be the identity.  The range inclusion is unfolded as
an inclusion between the displayed coordinate image and the scalar multiples
of a line generator `v`; `v.1 ≠ 0` and `v.2 ≠ 0` are exactly the
non-coordinate condition. -/
theorem diagonalRange_le_noncoordinateLine {K : Type*} [Field K]
    (a d : K) (v : K × K) (hv1 : v.1 ≠ 0) (hv2 : v.2 ≠ 0)
    (h : Set.range (fun x : K × K =>
      ((a - 1) * x.1, (d - 1) * x.2)) ⊆
      Set.range (fun c : K => (c * v.1, c * v.2))) :
    a = 1 ∧ d = 1 := by
  have hx := h (Set.mem_range_self (1, 0))
  rcases hx with ⟨c, hc⟩
  have hc1 := congrArg Prod.fst hc
  have hc2 := congrArg Prod.snd hc
  have hc0 : c = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right hv2
    simpa using hc2
  have ha : a = 1 := by
    have : a - 1 = c * v.1 := by simpa using hc1.symm
    rw [hc0] at this
    exact sub_eq_zero.mp (by simpa using this)
  have hy := h (Set.mem_range_self (0, 1))
  rcases hy with ⟨c', hc'⟩
  have hc'1 := congrArg Prod.fst hc'
  have hc'2 := congrArg Prod.snd hc'
  have hc'0 : c' = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right hv1
    simpa using hc'1
  have hd : d = 1 := by
    have : d - 1 = c' * v.2 := by simpa using hc'2.symm
    rw [hc'0] at this
    exact sub_eq_zero.mp (by simpa using this)
  exact ⟨ha, hd⟩

end MathlibPlus.LinearAlgebra.DiagonalMultiplier
