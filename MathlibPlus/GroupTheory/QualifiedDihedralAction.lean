import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Basic

namespace MathlibPlus.GroupTheory

/-- Claim 7094: the row reflection, column reflection, and factor swap on the
bounded index square satisfy the qualified dihedral relations, are faithful
in positive size, and act on the diagonal/anti-diagonal supports as stated.
The named identification with `W(C₂)` is represented by these eight distinct
transformations rather than by a separate Weyl-group object. -/
theorem qualifiedDihedralAction_claim7094 (k : ℕ) (hk : 0 < k) :
    let I := Fin (k + 1) × Fin (k + 1)
    let diag : Set I := {p | p.1 = p.2}
    let anti : Set I := {p | p.2 = Fin.rev p.1}
    ∃ S Rh Rc : I ≃ I,
      S = Equiv.prodComm _ _ ∧
      Rh = Equiv.prodCongr Fin.revPerm (Equiv.refl _) ∧
      Rc = Equiv.prodCongr (Equiv.refl _) Fin.revPerm ∧
      S.trans S = Equiv.refl _ ∧
      Rh.trans Rh = Equiv.refl _ ∧
      Rc.trans Rc = Equiv.refl _ ∧
      S.trans (Rh.trans S) = Rc ∧
      (S.trans Rh).trans ((S.trans Rh).trans ((S.trans Rh).trans (S.trans Rh))) =
        Equiv.refl _ ∧
      (S.trans Rh).trans (S.trans Rh) = Rh.trans Rc ∧
      ([Equiv.refl _, Rh, Rc, Rh.trans Rc, S, S.trans Rh, S.trans Rc,
        S.trans (Rh.trans Rc)] : List (I ≃ I)).Pairwise (· ≠ ·) ∧
      (∀ p, p ∈ diag ↔ Rh p ∈ anti) ∧
      (∀ p, p ∈ anti ↔ Rh p ∈ diag) ∧
      (∀ p, p ∈ diag ↔ Rc p ∈ anti) ∧
      (∀ p, p ∈ anti ↔ Rc p ∈ diag) ∧
      (∀ p, p ∈ diag ↔ S p ∈ diag) ∧
      (∀ p, p ∈ anti ↔ S p ∈ anti) ∧
      (∀ p, p ∈ diag ↔ (Rh.trans Rc) p ∈ diag) ∧
      (∀ p, p ∈ anti ↔ (Rh.trans Rc) p ∈ anti) := by
  dsimp
  let s : (Fin (k + 1) × Fin (k + 1)) ≃ (Fin (k + 1) × Fin (k + 1)) :=
    Equiv.prodComm _ _
  let h : (Fin (k + 1) × Fin (k + 1)) ≃ (Fin (k + 1) × Fin (k + 1)) :=
    Equiv.prodCongr Fin.revPerm (Equiv.refl _)
  let c : (Fin (k + 1) × Fin (k + 1)) ≃ (Fin (k + 1) × Fin (k + 1)) :=
    Equiv.prodCongr (Equiv.refl _) Fin.revPerm
  refine ⟨s, h, c, rfl, rfl, rfl, ?_⟩
  dsimp [s, h, c]
  constructor
  · ext x <;> simp [Equiv.prodComm]
  constructor
  · ext x <;> simp [Equiv.prodCongr]
  constructor
  · ext x <;> simp [Equiv.prodCongr]
  constructor
  · ext x <;> simp [Equiv.prodComm, Equiv.prodCongr]
  constructor
  · ext x <;> simp [Equiv.prodComm, Equiv.prodCongr]
  constructor
  · ext x <;> simp [Equiv.prodComm, Equiv.prodCongr]
  constructor
  · have hzero : (0 : Fin (k + 1)) ≠ Fin.last k := by
      intro heq
      have hv := congrArg Fin.val heq
      simp at hv
      omega
    have hkne : k ≠ 0 := Nat.ne_of_gt hk
    have hrevzero : Fin.rev (0 : Fin (k + 1)) = Fin.last k := by
      apply Fin.ext
      simp [Fin.rev]
    have hrevlast : Fin.rev (Fin.last k) = 0 := by
      apply Fin.ext
      simp [Fin.rev]
    let tag (e : (Fin (k + 1) × Fin (k + 1)) ≃ (Fin (k + 1) × Fin (k + 1))) :
        (Fin (k + 1) × Fin (k + 1)) × (Fin (k + 1) × Fin (k + 1)) :=
      (e (0, 0), e (Fin.last k, 0))
    have htags :
        (List.map tag
          ([Equiv.refl _,
            Equiv.prodCongr Fin.revPerm (Equiv.refl _),
            Equiv.prodCongr (Equiv.refl _) Fin.revPerm,
            (Equiv.prodCongr Fin.revPerm (Equiv.refl _)).trans
              (Equiv.prodCongr (Equiv.refl _) Fin.revPerm),
            Equiv.prodComm _ _,
            (Equiv.prodComm _ _).trans (Equiv.prodCongr Fin.revPerm (Equiv.refl _)),
            (Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) Fin.revPerm),
            (Equiv.prodComm _ _).trans
              ((Equiv.prodCongr Fin.revPerm (Equiv.refl _)).trans
                (Equiv.prodCongr (Equiv.refl _) Fin.revPerm))] :
            List ((Fin (k + 1) × Fin (k + 1)) ≃ _))).Nodup := by
      simp [tag, hrevzero, hrevlast, hzero, hkne]
    exact List.Pairwise.of_map tag (by
      intro a b hab heq
      exact hab (congrArg tag heq)) htags
  constructor
  · intro p
    rcases p with ⟨r, s⟩
    simp [Equiv.prodCongr, eq_comm, Fin.rev_eq_iff]
  constructor
  · intro p
    rcases p with ⟨r, s⟩
    simp [Equiv.prodCongr, eq_comm, Fin.rev_eq_iff]
  constructor
  · intro p
    rcases p with ⟨r, s⟩
    simp [Equiv.prodCongr, eq_comm, Fin.rev_eq_iff]
  constructor
  · intro p
    rcases p with ⟨r, s⟩
    simpa [Equiv.prodCongr] using (show s = Fin.rev r ↔ r = Fin.rev s from by
      constructor
      · intro heq
        rw [heq, Fin.rev_rev]
      · intro heq
        rw [heq, Fin.rev_rev])
  constructor
  · intro p
    rcases p with ⟨r, s⟩
    simp [Equiv.prodComm, eq_comm, Fin.rev_eq_iff]
  constructor
  · intro p
    rcases p with ⟨r, s⟩
    simpa [Equiv.prodComm] using (show s = Fin.rev r ↔ r = Fin.rev s from by
      constructor
      · intro heq
        rw [heq, Fin.rev_rev]
      · intro heq
        rw [heq, Fin.rev_rev])
  constructor
  · intro p
    rcases p with ⟨r, s⟩
    simp [Equiv.prodComm, Equiv.prodCongr, eq_comm, Fin.rev_eq_iff]
  · intro p
    rcases p with ⟨r, s⟩
    simpa [Equiv.prodComm, Equiv.prodCongr, eq_comm] using
      (show s = Fin.rev r ↔ r = Fin.rev s from by
        constructor
        · intro heq
          rw [heq, Fin.rev_rev]
        · intro heq
          rw [heq, Fin.rev_rev])

end MathlibPlus.GroupTheory
