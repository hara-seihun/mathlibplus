import MathlibPlus.Open.ResearchFormalization.R1182.Claim31941
import MathlibPlus.Open.ResearchFormalization.R1182.Claim31942

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim41707

open _root_.MathlibPlus.Open.ResearchFormalization.R1182.Claim31941
open _root_.MathlibPlus.Open.ResearchFormalization.R1182.Claim31942

abbrev Q12 :=
  _root_.MathlibPlus.Open.ResearchFormalization.R1182.Claim31941.Q12
abbrev Axis :=
  _root_.MathlibPlus.Open.ResearchFormalization.R1182.Claim31942.Axis
abbrev C4Axis :=
  _root_.MathlibPlus.Open.ResearchFormalization.R1182.Claim31942.C4Axis

private def c4Subgroup : Set Q12 :=
  {h | h.1 = 0}

private def oddParityCoboundary (p : ℕ) (c : ZMod p) (h : Q12) : ZMod p :=
  c * (1 - q12Sign p h)

/-- The exact integer axis voltage system, reduced modulo the prime. -/
private def axisVoltageSystem (p : ℕ) (tau : Q12 → ZMod p) : Prop :=
  ∀ row : Unit ⊕ (Axis × C4Axis),
    ∑ col : Q12,
      (axisVoltageMatrix row col : ZMod p) * tau col = 0

/-- Claim 41707: the `C₄` scalar stabilizer leaves only the axis atom quiet,
and the exact axis cocycle/voltage equations force one odd-parity coboundary. -/
def c4QuietPatternForcesCoboundary_claim41707 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p),
      normalizedAffineFunctions lam tau →
        scalarStabilizer p lam = c4Subgroup →
          (∀ S : Set Q12,
            quietProjectedFamily p lam S ↔
              S = axisAtom) ∧
            (axisVoltageSystem p tau →
              ∃ c : ZMod p, ∀ h : Q12,
                tau h = oddParityCoboundary p c h)

end MathlibPlus.Open.ResearchFormalization.R1182.Claim41707
