import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CyclicSquarefreeQ8

/-- The exact group `C_n × Q_8`, with the cyclic factor represented by
`Multiplicative (ZMod n)` and `Q_8` by `QuaternionGroup 2`. -/
abbrev CyclicSquarefreeQ8Group (n : ℕ) :=
  Multiplicative (ZMod n) × QuaternionGroup 2

/-- The identity-free condition for a connection set on the exact carrier. -/
def identityFree {n : ℕ} (S : Set (CyclicSquarefreeQ8Group n)) : Prop :=
  (1 : CyclicSquarefreeQ8Group n) ∉ S

/-- Inverse closure of a connection set on the exact carrier. -/
def inverseClosed {n : ℕ} (S : Set (CyclicSquarefreeQ8Group n)) : Prop :=
  ∀ g : CyclicSquarefreeQ8Group n, g ∈ S ↔ g⁻¹ ∈ S

/-- The binary Cayley relation determined by a connection set. -/
def cayleyRelation {n : ℕ}
    (S : Set (CyclicSquarefreeQ8Group n))
    (x y : CyclicSquarefreeQ8Group n) : Prop :=
  x⁻¹ * y ∈ S

/-- One vertex bijection is an isomorphism for every relation in a labelled
family. -/
def simultaneousCayleyIsomorphism {n : ℕ} {I : Type}
    (S T : I → Set (CyclicSquarefreeQ8Group n))
    (e : CyclicSquarefreeQ8Group n ≃ CyclicSquarefreeQ8Group n) : Prop :=
  ∀ i x y,
    cayleyRelation (S i) x y ↔
      cayleyRelation (T i) (e x) (e y)

/-- The ordinary one-label undirected CI property on `C_n × Q_8`. -/
def ordinaryUndirectedCI (n : ℕ) : Prop :=
  ∀ S T : Set (CyclicSquarefreeQ8Group n),
    identityFree S →
    inverseClosed S →
    identityFree T →
    inverseClosed T →
    (∃ e : CyclicSquarefreeQ8Group n ≃ CyclicSquarefreeQ8Group n,
      ∀ x y,
        cayleyRelation S x y ↔ cayleyRelation T (e x) (e y)) →
    ∃ α : CyclicSquarefreeQ8Group n ≃* CyclicSquarefreeQ8Group n,
      Set.image α S = T

/-- The simultaneous labelled CI property on `C_n × Q_8`. -/
def simultaneousCI (n : ℕ) : Prop :=
  ∀ (I : Type) [Fintype I]
    (S T : I → Set (CyclicSquarefreeQ8Group n)),
    (∀ i, identityFree (S i)) →
    (∀ i, inverseClosed (S i)) →
    (∀ i, identityFree (T i)) →
    (∀ i, inverseClosed (T i)) →
    (∃ e : CyclicSquarefreeQ8Group n ≃ CyclicSquarefreeQ8Group n,
      simultaneousCayleyIsomorphism S T e) →
    ∃ α : CyclicSquarefreeQ8Group n ≃* CyclicSquarefreeQ8Group n,
      ∀ i, Set.image α (S i) = T i

/-- Claim 61163: every odd square-free positive cyclic parameter in the
`Q_8` chamber has simultaneous labelled symmetric-binary CI, and hence the
ordinary undirected CI property, with no exclusion of `3 ∣ n`. -/
def claim61163 : Prop :=
  ∀ n : ℕ,
    0 < n →
    Odd n →
    Squarefree n →
    simultaneousCI n ∧ ordinaryUndirectedCI n

end MathlibPlus.Open.ResearchFormalization.CyclicSquarefreeQ8
