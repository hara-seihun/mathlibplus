import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CIExtremeValency61151

/-- The additive carrier `F_p^r` used for the elementary-abelian claim. -/
abbrev elementaryAbelian (p r : ℕ) := Fin r → ZMod p

/-- Identity-free connection sets in an additive Cayley graph. -/
def identityFree {p r : ℕ} (S : Set (elementaryAbelian p r)) : Prop :=
  S ⊆ (Set.univ \ ({0} : Set (elementaryAbelian p r)))

/-- Inverse-closure for additive connection sets. -/
def inverseClosed {p r : ℕ} (S : Set (elementaryAbelian p r)) : Prop :=
  ∀ ⦃x : elementaryAbelian p r⦄, x ∈ S → -x ∈ S

/-- The four connection-set cardinalities in the claim. -/
def extremeValency (p r k : ℕ) : Prop :=
  k ∈ ({0, 2, p ^ r - 3, p ^ r - 1} : Set ℕ)

/-- CI at one cardinality for ordinary undirected Cayley graphs on `F_p^r`. -/
def ciAtCard (p r k : ℕ) [NeZero p] : Prop :=
  ∀ (S T : Set (elementaryAbelian p r)),
    identityFree S →
    inverseClosed S →
    identityFree T →
    inverseClosed T →
    S.ncard = k →
    T.ncard = k →
    Nonempty (SimpleGraph.addCayley S ≃g SimpleGraph.addCayley T) →
    ∃ A : elementaryAbelian p r ≃ₗ[ZMod p] elementaryAbelian p r,
      A '' S = T

/-- Claim 61151: the four extreme valencies are CI for every odd prime and
positive rank, together with the stated exact A4-range consequence. -/
def claim61151 : Prop :=
  (∀ (p r : ℕ),
      (hp : Nat.Prime p) →
      p % 2 = 1 →
      1 ≤ r →
      letI : Fact (Nat.Prime p) := ⟨hp⟩
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ (S T : Set (elementaryAbelian p r)),
        identityFree S →
        inverseClosed S →
        identityFree T →
        inverseClosed T →
        Nonempty (SimpleGraph.addCayley S ≃g SimpleGraph.addCayley T) →
        extremeValency p r S.ncard →
        ∃ A : elementaryAbelian p r ≃ₗ[ZMod p] elementaryAbelian p r,
          A '' S = T) ∧
    (∀ (p r : ℕ),
      (hp : Nat.Prime p) →
      5 ≤ p →
      6 ≤ r →
      r ≤ 2 * p + 2 →
      letI : Fact (Nat.Prime p) := ⟨hp⟩
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ k : ℕ,
        extremeValency p r k →
        ciAtCard p r k)

end MathlibPlus.Open.ResearchFormalization.CIExtremeValency61151
