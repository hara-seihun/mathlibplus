import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch019ffede1003704cbb69a8fa6946cea1

/-- The source coordinates `(q,p,b)` from the unique dihedral vertex
parametrization in Claim 24082. -/
abbrev BitShearSource (k : ℕ) := ZMod (2 * k) × Bool × Bool

/-- The target rotation/reflection coordinates `(m,b)` used for the image
`r^m s^b`. -/
abbrev BitShearTarget (k : ℕ) := ZMod (4 * k) × Bool

/-- Reduce the signed `q` coordinate modulo `2k` before the target lift. -/
def reducedSignedQ (k : ℕ) (q : ZMod (2 * k)) (p : Bool) : ZMod (2 * k) :=
  if p then -q else q

def bitShear (k : ℕ) : BitShearSource k → BitShearTarget k
  | ⟨q, p, b⟩ =>
      ( ((reducedSignedQ k q p).val : ZMod (4 * k)) +
          (if b then (2 * k : ZMod (4 * k)) else 0),
        Bool.xor p b )

/-- Claim 24082: the explicit bit-shear map is bijective for every `k ≥ 2`. -/
def claim_24082 : Prop :=
  ∀ k : ℕ, 2 ≤ k → Function.Bijective (bitShear k)

end MathlibPlus.Open.ResearchFormalization.Batch019ffede1003704cbb69a8fa6946cea1
