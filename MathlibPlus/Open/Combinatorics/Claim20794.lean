import Mathlib

namespace MathlibPlus.Open.Combinatorics.Claim20794

/-- Claim 20794: the binary-cube parity trades have the displayed values on
 even and odd parity.  The cube and trade arrays remain local to the claim,
so this statement introduces no separate unreviewed reusable carrier. -/
def claim20794 : Prop :=
  let tau : Fin 2 → Fin 2 → Fin 2 → ℤ :=
    fun p q r => (-1 : ℤ) ^ (p.1 + q.1 + r.1)
  let tPlus : Fin 2 → Fin 2 → Fin 2 → ℤ :=
    fun p q r => 1 + tau p q r
  let tMinus : Fin 2 → Fin 2 → Fin 2 → ℤ :=
    fun p q r => 1 - tau p q r
  (∀ p q r : Fin 2,
    tPlus p q r =
      if Even (p.1 + q.1 + r.1) then 2 else 0) ∧
  (∀ p q r : Fin 2,
    tMinus p q r =
      if Even (p.1 + q.1 + r.1) then 0 else 2)

end MathlibPlus.Open.Combinatorics.Claim20794
