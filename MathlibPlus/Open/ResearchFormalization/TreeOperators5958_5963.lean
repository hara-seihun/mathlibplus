import MathlibPlus.Open.TreeSpectral

namespace MathlibPlus.Open.ResearchFormalization.TreeOperators5958_5963

open MathlibPlus.Open.TreeSpectral

noncomputable section

/-- The degree grading operator on the rational span of unrooted tree types. -/
def gradingN (n : ℕ) : Module.End ℚ (TreeSpace n) :=
  (n : ℚ) • LinearMap.id

/-- The stable commutator of leaf deletion and grafting at degree `n`.
The transports only identify the adjacent natural-number presentations of the
same graded tree space. -/
def treeUpDownCommutator (n : ℕ) (hn : 0 < n) : Module.End ℚ (TreeSpace n) :=
  (transportTreeSpace (by omega)).comp
      ((leafDeletion (n + 1)).comp (graft n)) -
    (transportTreeSpace (by omega)).comp
      ((graft (n - 1)).comp (leafDeletion n))

/-- Claim 5958: every primitive vector at a stable bottom degree has the
stated eigenvalue under the concrete `GL` operator on its graft tower. -/
def stableGLEigenvalueFormula_claim5958 : Prop :=
  ∀ (m : ℕ) (hm : 2 ≤ m),
    ∀ (v : TreeSpace m)
      (hv : v ∈ LinearMap.ker (leafDeletion m)),
        ∀ k : ℕ,
          glOperator (m + k) (by omega) (graftPow m k v) =
            ((k * m + Nat.choose k 2 : ℕ) : ℚ) • graftPow m k v

/-- Claim 5963: the concrete tree pair has the grading-dependent commutator,
not a fixed-`r` differential-poset commutator, and the relevant same-degree
operator is the grading `N`. -/
def notFixedRDifferentialPoset_claim5963 : Prop :=
  (∀ (n : ℕ) (hn : 2 ≤ n),
    treeUpDownCommutator n (by omega) = gradingN n) ∧
  (¬ ∃ r : ℚ, ∀ (n : ℕ) (hn : 2 ≤ n),
    treeUpDownCommutator n (by omega) =
      r • (LinearMap.id : Module.End ℚ (TreeSpace n)))

end

end MathlibPlus.Open.ResearchFormalization.TreeOperators5958_5963
