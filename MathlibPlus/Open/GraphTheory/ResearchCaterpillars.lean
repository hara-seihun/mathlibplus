import Mathlib

namespace MathlibPlus.Open.ResearchCaterpillars

open scoped BigOperators

noncomputable section

/-- The two spine load words in R-5063. -/
def caterpillarLoadA : Fin 9 → ℕ := ![1, 0, 0, 0, 0, 1, 0, 0, 1]
def caterpillarLoadB : Fin 9 → ℕ := ![1, 0, 0, 0, 1, 0, 0, 0, 1]

private def spineEdge (v w : Fin 12) : Prop :=
  v.val < 9 ∧ w.val < 9 ∧
    (v.val + 1 = w.val ∨ w.val + 1 = v.val)

private def caterpillarAAttachment (v w : Fin 12) : Prop :=
  (v.val = 9 ∧ w.val = 0) ∨
  (v.val = 10 ∧ w.val = 5) ∨
  (v.val = 11 ∧ w.val = 8)

private def caterpillarBAttachment (v w : Fin 12) : Prop :=
  (v.val = 9 ∧ w.val = 0) ∨
  (v.val = 10 ∧ w.val = 4) ∨
  (v.val = 11 ∧ w.val = 8)

/-- The labelled realizations of the two caterpillars.  `fromRel` makes the
listed spine and leaf incidences undirected. -/
def caterpillarA : SimpleGraph (Fin 12) :=
  SimpleGraph.fromRel (fun v w => spineEdge v w ∨ caterpillarAAttachment v w)

def caterpillarB : SimpleGraph (Fin 12) :=
  SimpleGraph.fromRel (fun v w => spineEdge v w ∨ caterpillarBAttachment v w)

/-- R-5063.2: the two displayed load words give nonisomorphic order-twelve
caterpillar trees. -/
def claim54979 : Prop :=
  caterpillarLoadA = ![1, 0, 0, 0, 0, 1, 0, 0, 1] ∧
  caterpillarLoadB = ![1, 0, 0, 0, 1, 0, 0, 0, 1] ∧
  Fintype.card (Fin 12) = 12 ∧
  caterpillarA.IsTree ∧
  caterpillarB.IsTree ∧
  ¬ Nonempty (caterpillarA ≃g caterpillarB)

/-- Number of independent sets of a specified size and specified sum of host
vertex degrees. -/
noncomputable def independentDegreeSumCount
    (G : SimpleGraph (Fin 12)) (k s : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset (Fin 12))).filter
    (fun S : Finset (Fin 12) =>
      S.card = k ∧
      G.IsIndepSet (S : Set (Fin 12)) ∧
      S.sum (fun v => G.degree v) = s)).card

/-- R-5063.3: equality of the independent degree-sum profiles through size
four. -/
def claim54980 : Prop :=
  ∀ k : ℕ, k ≤ 4 → ∀ s : ℕ,
    independentDegreeSumCount caterpillarA k s =
      independentDegreeSumCount caterpillarB k s

end
end MathlibPlus.Open.ResearchCaterpillars
