import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1900.Claim31268

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1900Claim31264

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1900.Claim31268

abbrev Family (α : Type*) := Finset (Finset α)

def uniformFamily {α : Type*} [DecidableEq α]
    (F : Family α) (n : ℕ) : Prop :=
  ∀ B ∈ F, B.card = n

def pairwiseIntersecting {α : Type*} [DecidableEq α]
    (F : Family α) : Prop :=
  ∀ ⦃B⦄, B ∈ F → ∀ ⦃C⦄, C ∈ F → B ≠ C → ¬ Disjoint B C

def threeSunflowerFree {α : Type*} [DecidableEq α]
    (F : Family α) : Prop :=
  kSunflowerFree 3 F

def exactTraceClass {α : Type*} [DecidableEq α]
    (A : Finset α) (F : Family α) (T : Finset α) : Family α :=
  (F.erase A).filter (fun B => A ∩ B = T)

def traceWeight {α : Type*} [DecidableEq α]
    (A : Finset α) (F : Family α) (T : Finset α) : ℕ :=
  (exactTraceClass A F T).card

def totalTraceWeight {α : Type*} [DecidableEq α]
    (A : Finset α) (F : Family α) (t : ℕ) : ℕ :=
  ∑ T ∈ A.powerset.filter (fun T => T.card = t), traceWeight A F T

def traceMatchingFamily {α : Type*} [DecidableEq α]
    (A : Finset α) (F M : Family α) : Family α :=
  (F.erase A).filter (fun B => A ∩ B ∈ M)

def pairwiseDisjointFamily {α : Type*} [DecidableEq α]
    (M : Family α) : Prop :=
  ∀ ⦃T⦄, T ∈ M → ∀ ⦃U⦄, U ∈ M → T ≠ U → Disjoint T U

def matchingOfTSubsets {α : Type*} [DecidableEq α]
    (A : Finset α) (t : ℕ) (M : Family α) : Prop :=
  (∀ T ∈ M, T.card = t) ∧
    (∀ T ∈ M, T ⊆ A) ∧
      pairwiseDisjointFamily M

def freshLabel {α : Type*} (T : Finset α) : Sum α (Finset α) :=
  Sum.inr T

def repairedMember {α : Type*} [DecidableEq α]
    (A B : Finset α) : Finset (Sum α (Finset α)) :=
  insert (freshLabel (A ∩ B))
    ((B \ A).image (fun x : α => Sum.inl x))

def repairedFamily {α : Type*} [DecidableEq α]
    (A : Finset α) (F M : Family α) : Finset (Finset (Sum α (Finset α))) :=
  (traceMatchingFamily A F M).image (repairedMember A)

def repairedMemberInjective {α : Type*} [DecidableEq α]
    (A : Finset α) (F M : Family α) : Prop :=
  ∀ ⦃B C : Finset α⦄,
    B ∈ traceMatchingFamily A F M →
      C ∈ traceMatchingFamily A F M →
        repairedMember A B = repairedMember A C → B = C

noncomputable def intersectingSunflowerMaximum (n : ℕ) : ℕ :=
  sSup {m : ℕ |
    ∃ N : ℕ, ∃ F : Finset (Finset (Fin N)),
      F.card = m ∧
        uniformFamily (α := Fin N) F n ∧
          threeSunflowerFree (α := Fin N) F ∧
            pairwiseIntersecting (α := Fin N) F}

/-- Claim 31264: one fresh label per matched trace turns the selected residuals
into a distinct intersecting three-sunflower-free uniform family, with the
trace-weight sum retained as its cardinality. -/
def claim31264 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (n t : ℕ) (A : Finset α) (F M : Family α),
    1 ≤ t →
      t ≤ n →
        A ∈ F →
          uniformFamily F n →
            threeSunflowerFree F →
              pairwiseIntersecting F →
                matchingOfTSubsets A t M →
                  (∀ T ∈ M, ∀ U ∈ M,
                    freshLabel T = freshLabel U ↔ T = U) ∧
                  repairedMemberInjective A F M ∧
                  uniformFamily (repairedFamily A F M) (n - t + 1) ∧
                  pairwiseIntersecting (repairedFamily A F M) ∧
                  threeSunflowerFree (repairedFamily A F M) ∧
                  (repairedFamily A F M).card =
                    (traceMatchingFamily A F M).card ∧
                  (traceMatchingFamily A F M).card =
                    ∑ T ∈ M, traceWeight A F T ∧
                  (repairedFamily A F M).card ≤
                    intersectingSunflowerMaximum (n - t + 1)

end

end MathlibPlus.Open.ResearchFormalization.R1900Claim31264
