import Mathlib

namespace MathlibPlus.Open

abbrev F7_59516 := ZMod 7

/-- The sign coordinate is `true = 1` and `false = -1`. -/
def dihSign59516 (a : Bool) : F7_59516 := if a then 1 else -1

def dihSignMul59516 (a b : Bool) : Bool := decide (a = b)

abbrev DihF7_59516 := Bool × (F7_59516 × F7_59516)

def dihMul59516 (g h : DihF7_59516) : DihF7_59516 :=
  (dihSignMul59516 g.1 h.1,
    (g.2.1 + dihSign59516 g.1 * h.2.1,
      g.2.2 + dihSign59516 g.1 * h.2.2))

def dihOne59516 : DihF7_59516 := (true, (0, 0))

def dihInv59516 (g : DihF7_59516) : DihF7_59516 :=
  (g.1, (-(dihSign59516 g.1 * g.2.1), -(dihSign59516 g.1 * g.2.2)))

def p59516 (t : F7_59516) : Finset DihF7_59516 :=
  Finset.univ.image (fun z : F7_59516 => (false, (t + z ^ 2, (2 : F7_59516) * z)))

def t59516 : Finset DihF7_59516 := p59516 0 ∪ p59516 1 ∪ p59516 3

def tPrime59516 : Finset DihF7_59516 :=
  p59516 0 ∪ p59516 (-1) ∪ p59516 (-3)

def inverseClosed59516 (S : Finset DihF7_59516) : Prop :=
  ∀ g, g ∈ S → dihInv59516 g ∈ S

def identityFree59516 (S : Finset DihF7_59516) : Prop := dihOne59516 ∉ S

def cayAdj59516 (S : Finset DihF7_59516) (g h : DihF7_59516) : Prop :=
  g ≠ h ∧ dihMul59516 (dihInv59516 g) h ∈ S

def cayleyGraphIso59516 (S U : Finset DihF7_59516) (f : DihF7_59516 → DihF7_59516) : Prop :=
  Function.Bijective f ∧ ∀ g h, cayAdj59516 S g h ↔ cayAdj59516 U (f g) (f h)

def dihMap59516 (g : DihF7_59516) : DihF7_59516 :=
  (g.1,
    ((2 : F7_59516)⁻¹ * g.2.2 ^ 2 - g.2.1,
      dihSign59516 g.1 * g.2.2))

def dihAutomorphism59516 (f : DihF7_59516 → DihF7_59516) : Prop :=
  Function.Bijective f ∧
    f dihOne59516 = dihOne59516 ∧
      ∀ g h, f (dihMul59516 g h) = dihMul59516 (f g) (f h)

/-- The undirected CI property for the displayed dihedral group. -/
def undirectedCI59516 : Prop :=
  ∀ S U : Finset DihF7_59516,
    (inverseClosed59516 S ∧ identityFree59516 S ∧
        inverseClosed59516 U ∧ identityFree59516 U) →
      (∃ f, cayleyGraphIso59516 S U f) →
        ∃ f, dihAutomorphism59516 f ∧ Finset.image f S = U

/-- Claim 59516: the two displayed connection sets give the stated obstruction. -/
def claim59516 : Prop :=
  inverseClosed59516 t59516 ∧
    inverseClosed59516 tPrime59516 ∧
      identityFree59516 t59516 ∧
        identityFree59516 tPrime59516 ∧
          t59516.card = 21 ∧
            tPrime59516.card = 21 ∧
              cayleyGraphIso59516 t59516 tPrime59516 dihMap59516 ∧
                (∀ f, dihAutomorphism59516 f → Finset.image f t59516 ≠ tPrime59516) ∧
                  ¬ undirectedCI59516

/-- Claim 59522: the two singleton intersections are disjoint. -/
def claim59522 : Prop :=
  ∃ R S T : Bool → Prop,
    (∃! b : Bool, R b ∧ T b) ∧
      (∃! b : Bool, S b ∧ T b) ∧
        ∀ b : Bool, ¬ (R b ∧ S b ∧ T b)

end MathlibPlus.Open
