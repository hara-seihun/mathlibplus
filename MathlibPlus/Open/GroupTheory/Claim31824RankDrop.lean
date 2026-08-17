import Mathlib

namespace MathlibPlus.Open.GroupTheory

/-- Claim 31824: a common central order-p block line lowers regular
 elementary-abelian rank by one, while retaining regularity of both induced
quotient copies. -/
def elementaryAbelianQuotientRankDrop_claim31824 : Prop := by
  classical
  exact ∀ (Ω : Type) [Fintype Ω]
    (p n : ℕ)
    (R T P D Tx X : Subgroup (Equiv.Perm Ω))
    (x : Equiv.Perm Ω),
    Nat.Prime p → 1 ≤ n →
    IsPGroup p P →
    R ≤ P → Tx ≤ P → P ≤ X → D ≤ P → D ≤ R → D ≤ Tx →
    Nat.card D = p →
    (∀ d : D, ∀ q : P, (d : Equiv.Perm Ω) * (q : Equiv.Perm Ω) =
      (q : Equiv.Perm Ω) * (d : Equiv.Perm Ω)) →
    (∀ a b : Ω, ∃! r : R, (r : Equiv.Perm Ω) a = b) →
    (∀ a b : Ω, ∃! t : T, (t : Equiv.Perm Ω) a = b) →
    (∀ r s : R, r * s = s * r) →
    (∀ t u : T, t * u = u * t) →
    R ≤ X → T ≤ X → x ∈ X →
    (∀ g : Equiv.Perm Ω, g ∈ Tx ↔
      ∃ t : Equiv.Perm Ω, t ∈ T ∧ g = x⁻¹ * t * x) →
    X = Subgroup.closure ((R : Set (Equiv.Perm Ω)) ∪ (T : Set (Equiv.Perm Ω))) →
    (eR : R ≃* Multiplicative (Fin n → ZMod p)) →
    (eTx : Tx ≃* Multiplicative (Fin n → ZMod p)) →
    ∀ (DR : Subgroup R) [hDR : DR.Normal]
      (DTx : Subgroup Tx) [hDTx : DTx.Normal],
    (∀ r : R, r ∈ DR ↔ (r : Equiv.Perm Ω) ∈ D) →
    (∀ t : Tx, t ∈ DTx ↔ (t : Equiv.Perm Ω) ∈ D) →
    let B := MulAction.orbitRel.Quotient D Ω
    (∃ ρR : (R ⧸ DR) →* Equiv.Perm B,
        ∃ ρTx : (Tx ⧸ DTx) →* Equiv.Perm B,
          (∀ r : R, ∀ ω : Ω,
            ρR (QuotientGroup.mk' DR r)
                (Quotient.mk (MulAction.orbitRel D Ω) ω) =
              Quotient.mk (MulAction.orbitRel D Ω)
                ((r : Equiv.Perm Ω) ω)) ∧
          (∀ t : Tx, ∀ ω : Ω,
            ρTx (QuotientGroup.mk' DTx t)
                (Quotient.mk (MulAction.orbitRel D Ω) ω) =
              Quotient.mk (MulAction.orbitRel D Ω)
                ((t : Equiv.Perm Ω) ω)) ∧
          (∀ a b : B, ∃! q : Subgroup.map ρR ⊤, q.val a = b) ∧
          (∀ a b : B, ∃! q : Subgroup.map ρTx ⊤, q.val a = b) ∧
          Nonempty ((R ⧸ DR) ≃*
              Multiplicative (Fin (n - 1) → ZMod p)) ∧
          Nonempty ((Tx ⧸ DTx) ≃*
              Multiplicative (Fin (n - 1) → ZMod p)))

end MathlibPlus.Open.GroupTheory
