import MathlibPlus.Analysis.ShiftPacket

namespace MathlibPlus.Analysis.ShiftPacket

/-- The existing finite integer-packet moment expands to the admitted sum. -/
theorem packetShiftMoment_formula_claim4604 (p : IntegerShiftPacket) (d : ℕ) :
    packetShiftMoment p d =
      p.sum (fun alpha c => (c : ℝ) * alpha ^ d) := rfl

/-- Translate a finite signed shift measure by translating each real atom. -/
noncomputable def translateFiniteSignedAtoms
    (mu : FiniteSignedShiftMeasure) (a : ℝ) : FiniteSignedShiftMeasure :=
  Finsupp.mapDomain (fun alpha : ℝ => alpha + a) mu

/-- Translation preserves the signed mass at each translated atom. -/
theorem translateFiniteSignedAtoms_apply
    (mu : FiniteSignedShiftMeasure) (a alpha : ℝ) :
    translateFiniteSignedAtoms mu a (alpha + a) = mu alpha := by
  apply Finsupp.mapDomain_apply
  intro x y hxy
  linarith

/-- Translation preserves the total signed mass of a finite signed shift measure. -/
theorem translateFiniteSignedAtoms_totalMass
    (mu : FiniteSignedShiftMeasure) (a : ℝ) :
    (translateFiniteSignedAtoms mu a).sum (fun _ mass => mass) =
      mu.sum (fun _ mass => mass) := by
  simp [translateFiniteSignedAtoms, Finsupp.sum_mapDomain_index]

/-- The lower active shift is absent for an empty packet and is the minimum
of the finite support otherwise. -/
noncomputable def lowerActiveShift (p : IntegerShiftPacket) : Option ℝ :=
  dite p.support.Nonempty
    (fun h => some (p.support.min' h))
    (fun _ => none)

/-- The lower active shift has the support-minimum property. -/
theorem lowerActiveShift_spec_claim4618
    (p : IntegerShiftPacket) (astar : ℝ)
    (h : lowerActiveShift p = some astar) :
    astar ∈ p.support ∧ ∀ beta ∈ p.support, astar ≤ beta := by
  classical
  rw [lowerActiveShift] at h
  split at h
  · rename_i hp
    have h_eq : p.support.min' hp = astar := Option.some.inj h
    subst astar
    exact ⟨Finset.min'_mem p.support hp, fun beta hbeta =>
      Finset.min'_le p.support beta hbeta⟩
  · simp at h

end MathlibPlus.Analysis.ShiftPacket
