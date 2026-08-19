import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1405Degree300

noncomputable section

abbrev A4 := alternatingGroup (Fin 4)
abbrev C5SquaredTimesA4 :=
  (Multiplicative (ZMod 5) × Multiplicative (ZMod 5)) × A4

/-- Claim 38683: in the exact degree-300 regular action of
`C₅² × A₄`, the `C₅²` factor is characteristic and central, so its
regular-copy centralizer contains the whole copy. -/
def degree300DirectProductTarget_claim38683 : Prop :=
  let G := C5SquaredTimesA4
  let C : Subgroup G :=
    Subgroup.prod
      (Subgroup.prod (⊤ : Subgroup (Multiplicative (ZMod 5)))
        (⊤ : Subgroup (Multiplicative (ZMod 5))))
      (⊥ : Subgroup A4)
  Nat.card G = 300 ∧
    Nat.card C = 25 ∧
    C.Characteristic ∧
    ∀ (R : Subgroup (Equiv.Perm G)),
      (∀ x y : G, ∃! r : R, r.1 x = y) →
        ∀ e : G ≃* R,
          let C_R : Subgroup R := Subgroup.map e.toMonoidHom C
          let Z_R : Subgroup R := Subgroup.centralizer (C_R : Set R)
          Nat.card R = 300 ∧
            C_R.Characteristic ∧
            (∀ c : C_R, c.1 ≠ 1 →
              ∀ x : G, c.1.1 x ≠ x) ∧
            (⊤ : Subgroup R) ≤ Z_R ∧
            Nat.card Z_R ≥ 300

end

end MathlibPlus.Open.ResearchFormalization.R1405Degree300
