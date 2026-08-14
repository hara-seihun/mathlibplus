import Mathlib

namespace MathlibPlus.Open.Combinatorics.AdmittedBatchR2666

/-- Claim 42260: every exchanged demand in H₁ \ A is retained by R₁ when
H₁ is retained by R₁. -/
def claim42260 : Prop :=
  ∀ (α : Type*) [DecidableEq α]
    (H₁ A R₁ S : Finset α),
    S = H₁ \ A → H₁ ⊆ R₁ → S ⊆ R₁ ∧
      (∀ x ∈ S, x ∈ R₁)

/-- Claim 42261: the retained root and any removable member containing the two
pivot coordinates cover the enlarged tight set. -/
def claim42261 : Prop :=
  ∀ (α : Type*) [DecidableEq α]
    (R₁ S T M : Finset α) (p₀ p₂ : α),
    S ⊆ R₁ → T ⊆ S → {p₀, p₂} ⊆ M →
    T ⊆ R₁ ∪ M

/-- Claim 42262: the complementary trace prohibition is quantified over an
arbitrary uncovered demand set; no singleton-cardinality hypothesis occurs. -/
def claim42262 : Prop :=
  ∀ (α : Type*) [DecidableEq α]
    (U R₁ T : Finset α),
    T ⊆ U → U ⊆ R₁ → T ⊆ R₁

end MathlibPlus.Open.Combinatorics.AdmittedBatchR2666
