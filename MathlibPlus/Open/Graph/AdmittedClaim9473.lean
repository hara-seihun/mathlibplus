import Mathlib

noncomputable section

namespace MathlibPlus.Open.Graph.AdmittedClaim9473

/-- Exact pendant contamination of all star layers at minimum degree one. -/
def pendantContamination {V : Type} [Fintype V] (Y : SimpleGraph V) : Prop :=
  let degree : V → ℕ := fun v =>
    letI : Finite (Y.neighborSet v) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    letI := Fintype.ofFinite (Y.neighborSet v)
    Y.degree v
  let δ : ℕ :=
    letI : DecidableRel Y.Adj := Classical.decRel _
    Y.minDegree
  let star : V → Set (Sym2 V) :=
    fun c => {e | e ∈ Y.edgeSet ∧ ∃ w : V, e = s(c, w)}
  let misses : Set (Sym2 V) → V → Prop :=
    fun A v => ∀ w : V, s(v, w) ∉ A
  let valid : Set (Sym2 V) → Prop :=
    fun A =>
      A ⊆ Y.edgeSet ∧
        (∃ v : V, misses A v) ∧
          ∃ v : V, ∀ w : V, s(v, w) ∉ (Y.edgeSet \ A)
  let starFirst : Set (Sym2 V) → Prop :=
    fun A => ∃ c : V, A ⊆ star c
  let card : Set (Sym2 V) → Prop :=
    fun A => ∃ v : V, A = star v
  let pendant : V → Prop :=
    fun v => degree v = 1
  δ = 1 →
    (∀ {d : ℕ} {A : Set (Sym2 V)},
      d = A.ncard →
        valid A →
          starFirst A →
            ¬ card A →
              ∃ c : V,
                A ⊂ star c ∧
                  (∃ p : V, pendant p ∧ s(c, p) ∈ A) ∧
                    2 ≤ d) ∧
      (∀ {A : Set (Sym2 V)},
        valid A →
          starFirst A →
            A.ncard = 1 →
              ∃ p : V, pendant p ∧ A = star p)

end MathlibPlus.Open.Graph.AdmittedClaim9473
