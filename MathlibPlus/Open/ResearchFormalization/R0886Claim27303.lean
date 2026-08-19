import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0886Claim27303

noncomputable section

/-- Record 13's normalized map for the `p = 1 (mod 3)` case. -/
def phiOneFin : Fin 9 → Fin 9 :=
  ![0, 1, 2, 6, 7, 8, 3, 4, 5]

/-- Record 13's normalized map for the `p = 2 (mod 3)` case. -/
def phiTwoFin : Fin 9 → Fin 9 :=
  ![0, 1, 5, 6, 7, 2, 3, 4, 8]

def phiOne (x : ZMod 9) : ZMod 9 :=
  (phiOneFin ⟨x.val, x.isLt⟩).val

def phiTwo (x : ZMod 9) : ZMod 9 :=
  (phiTwoFin ⟨x.val, x.isLt⟩).val

/-- The independently specified R-0761 mixed cyclic map. It moves a
residue class modulo nine by the displayed source displacement, using a
multiple of `3*p`, and therefore keeps the residue modulo `p`. -/
def mixedCyclicMap (p : ℕ) (x : ZMod (9 * p)) : ZMod (9 * p) :=
  let residue := x.val % 9
  let shift : ℕ :=
    if p % 3 = 1 then residue / 3
    else 2 * ((residue + 1) / 3) % 3
  ((x.val + 3 * p * shift : ℕ) : ZMod (9 * p))

/-- Claim 27303: the independently specified mixed cyclic map is, under the
standard CRT equivalence, the appropriate Record 13 map on `C₉` times the
identity on `C_p`. -/
def claim27303 : Prop :=
  ∀ (p : ℕ),
    Nat.Prime p →
      5 ≤ p →
        ¬ p ∣ 9 →
          ∃ hcop : Nat.Coprime 9 p,
            let crt : ZMod (9 * p) ≃+* ZMod 9 × ZMod p :=
              ZMod.chineseRemainder hcop
            let φ : ZMod 9 → ZMod 9 :=
              if p % 3 = 1 then phiOne else phiTwo
            ∀ x : ZMod (9 * p),
              crt (mixedCyclicMap p x) = (φ ((crt x).1), (crt x).2)

end
end MathlibPlus.Open.ResearchFormalization.R0886Claim27303
