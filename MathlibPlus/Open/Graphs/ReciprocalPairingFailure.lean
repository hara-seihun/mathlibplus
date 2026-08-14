import MathlibPlus.Open.Graphs.AutomorphismPairing

namespace MathlibPlus.Open.Graphs

noncomputable section

private def k13 : FiniteSimpleGraph 4 where
  adjacent u v :=
    (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)
  symmetric := by
    intro u v h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  loopless := by
    intro u h
    fin_cases u <;> simp_all

private def p3 : FiniteSimpleGraph 3 where
  adjacent u v :=
    (u = 0 ∧ v = 1) ∨
      (u = 1 ∧ v = 0) ∨
      (u = 1 ∧ v = 2) ∨
      (u = 2 ∧ v = 1)
  symmetric := by
    intro u v h
    simpa [and_comm, or_comm, or_left_comm, or_assoc] using h
  loopless := by
    intro u h
    fin_cases u <;> simp_all

private def graphClassOf {n : ℕ} (G : FiniteSimpleGraph n) : GraphClass n :=
  Quotient.mk (finiteSimpleGraphSetoid n) G

private def k13Class : GraphClass 4 := graphClassOf k13
private def p3Class : GraphClass 3 := graphClassOf p3

private noncomputable def leaf (G : FiniteSimpleGraph n) (v : Fin n) : Prop := by
  classical
  exact (Finset.univ.filter (fun w => G.adjacent v w)).card = 1

private def deleteIndex {n : ℕ} (v : Fin (n + 1)) (u : Fin n) : Fin (n + 1) :=
  if u.castSucc < v then u.castSucc else u.succ

private def deleteVertex {n : ℕ} (G : FiniteSimpleGraph (n + 1)) (v : Fin (n + 1)) :
    FiniteSimpleGraph n where
  adjacent u w := G.adjacent (deleteIndex v u) (deleteIndex v w)
  symmetric := by
    intro u w h
    exact G.symmetric h
  loopless := by
    intro u
    exact G.loopless _

private def graftPendant {n : ℕ} (G : FiniteSimpleGraph n) (v : Fin n) :
    FiniteSimpleGraph (n + 1) where
  adjacent u w :=
    if hu : u.val < n then
      if hw : w.val < n then
        G.adjacent ⟨u.val, hu⟩ ⟨w.val, hw⟩
      else
        u = Fin.castSucc v ∧ w = Fin.last n
    else
      u = Fin.last n ∧ w = Fin.castSucc v
  symmetric := by
    intro u w h
    by_cases hu : u.val < n
    · by_cases hw : w.val < n
      · simp only [dif_pos hu, dif_pos hw] at h ⊢
        exact G.symmetric h
      · simp only [dif_pos hu, dif_neg hw] at h ⊢
        exact ⟨h.2, h.1⟩
    · by_cases hw : w.val < n
      · simp only [dif_neg hu, dif_pos hw] at h ⊢
        exact ⟨h.2, h.1⟩
      · simp only [dif_neg hu, dif_neg hw] at h ⊢
        exfalso
        have hlt : w.val < n := by
          rw [h.2]
          exact v.isLt
        exact hw hlt
  loopless := by
    intro u h
    by_cases hu : u.val < n
    · simp [hu] at h
      exact G.loopless _ h
    · simp only [dif_neg hu] at h
      have hlast : u.val = n := by
        simpa using congrArg Fin.val h.1
      have hcast : u.val = v.val := by
        simpa using congrArg Fin.val h.2
      omega

private noncomputable def deletionMultiplicity {n : ℕ} (G : FiniteSimpleGraph (n + 1))
    (H : GraphClass n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v =>
    leaf G v ∧ graphClassOf (deleteVertex G v) = H)).card

private noncomputable def graftingMultiplicity {n : ℕ} (H : FiniteSimpleGraph n)
    (G : GraphClass (n + 1)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v => graphClassOf (graftPendant H v) = G)).card

private def dK13P3 : ℕ := deletionMultiplicity k13 p3Class
private def uP3K13 : ℕ := graftingMultiplicity p3 k13Class

private def weightedDeletionSide : ℚ :=
  (dK13P3 : ℚ) * (graphAutCard p3Class : ℚ)

private def weightedGraftingSide : ℚ :=
  (uP3K13 : ℚ) * (graphAutCard k13Class : ℚ)

private def reciprocalDeletionSide : ℚ :=
  (dK13P3 : ℚ) / (graphAutCard p3Class : ℚ)

private def reciprocalGraftingSide : ℚ :=
  (uP3K13 : ℚ) / (graphAutCard k13Class : ℚ)

/-- Reciprocal and unit weights fail the leaf-deletion/pendant-grafting adjointness. -/
def reciprocalAndUnweightedPairingsFailClaim : Prop :=
  weightedDeletionSide = weightedGraftingSide ∧
    ((reciprocalDeletionSide / reciprocalGraftingSide) =
      (weightedDeletionSide / weightedGraftingSide) *
        ((graphAutCard k13Class : ℚ) ^ 2 /
          (graphAutCard p3Class : ℚ) ^ 2)) ∧
    reciprocalDeletionSide ≠ reciprocalGraftingSide ∧
    (dK13P3 : ℚ) ≠ (uP3K13 : ℚ)

end

end MathlibPlus.Open.Graphs
