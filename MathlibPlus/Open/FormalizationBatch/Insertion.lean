import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

section InsertionPrefixes

variable {G : Type*} [AddCommGroup G]

def firstIndex (r : Nat) : Fin (Nat.succ r) :=
  ⟨0, Nat.zero_lt_succ r⟩

def lastIndex (r : Nat) : Fin (Nat.succ r) :=
  ⟨r, Nat.lt_succ_self r⟩

def collisionInterval (P : Fin (Nat.succ r) → G) (w : G)
    (j i : Fin (Nat.succ r)) : Prop :=
  j.1 < i.1 ∧ P j - P i = w

def coversCut (j i k : Fin (Nat.succ r)) : Prop :=
  j.1 ≤ k.1 ∧ k.1 ≤ i.1

def allCutsCovered (P : Fin (Nat.succ r) → G) (w : G) : Prop :=
  ∀ k : Fin (Nat.succ r),
    ∃ j i : Fin (Nat.succ r),
      collisionInterval P w j i ∧ coversCut j i k

def endpointPrefixCondition (P : Fin (Nat.succ r) → G) (Unused : Set G)
    (T u v : G) : Prop :=
  u ∈ Unused ∧
    v ∈ Unused ∧
    u ≠ v ∧
    u + v = -T ∧
    (∃ a, P a = -u) ∧
    (∃ a, P a = T + u) ∧
    (∃ b, P b = -v) ∧
    (∃ b, P b = T + v)

/-- Claim 48224: the complementary endpoint prefixes are uniquely located and
can be ordered after relabelling the two unused labels. -/
def claim48224 (r : Nat) (P : Fin (Nat.succ r) → G) (T : G)
    (Unused : Set G) : Prop :=
  Function.Injective P →
    P (firstIndex r) = 0 →
      P (lastIndex r) = T →
        ∀ u v : G,
          endpointPrefixCondition P Unused T u v →
            T + u = -v ∧
              T + v = -u ∧
                (∃! a, P a = -u) ∧
                  (∃! b, P b = -v) ∧
                    (∃ a b,
                      a.1 < b.1 ∧
                        ((P a = -u ∧ P b = -v) ∨
                          (P a = -v ∧ P b = -u)))

/-- Claim 48228: the four endpoint occurrences give the stated collision
intervals and their exact cut coverage. -/
def claim48228 (r : Nat) (P : Fin (Nat.succ r) → G) (T : G)
    (Unused : Set G) : Prop :=
  Function.Injective P →
    P (firstIndex r) = 0 →
      P (lastIndex r) = T →
        ∀ u v : G,
          u ∈ Unused →
            v ∈ Unused →
              u ≠ v →
                u ≠ 0 →
                  u + v = -T →
                    ∀ a b : Fin (Nat.succ r),
                      a.1 < b.1 →
                        P a = -u →
                          P b = -v →
                            collisionInterval P u (firstIndex r) a ∧
                              collisionInterval P u b (lastIndex r) ∧
                                collisionInterval P v (firstIndex r) b ∧
                                  collisionInterval P v a (lastIndex r) ∧
                                    (∀ k : Fin (Nat.succ r),
                                      coversCut (firstIndex r) b k ∨
                                        coversCut a (lastIndex r) k) ∧
                                      (∀ k : Fin (Nat.succ r),
                                        (coversCut (firstIndex r) a k ∨
                                            coversCut b (lastIndex r) k) ↔
                                          ¬(a.1 < k.1 ∧ k.1 < b.1))

/-- Claim 48232: the all-cuts criterion forces every missed cut to have an
interior collision interval for the outer label. -/
def claim48232 (r : Nat) (P : Fin (Nat.succ r) → G) (T : G) : Prop :=
  Function.Injective P →
    P (firstIndex r) = 0 →
      P (lastIndex r) = T →
        ∀ u v : G,
          u ≠ v →
            u ≠ 0 →
              u + v = -T →
                ∀ a b k : Fin (Nat.succ r),
                  a.1 < k.1 →
                    k.1 < b.1 →
                      P a = -u →
                        P b = -v →
                          allCutsCovered P u →
                            ∃ j i : Fin (Nat.succ r),
                              0 < j.1 ∧
                                j.1 < i.1 ∧
                                  i.1 < r ∧
                                    collisionInterval P u j i ∧
                                      coversCut j i k

end InsertionPrefixes

end MathlibPlus.Open.FormalizationBatch
