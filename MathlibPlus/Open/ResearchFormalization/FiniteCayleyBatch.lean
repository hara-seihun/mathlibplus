import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization

/-! A concrete generalized dihedral group model for Claim 59796. -/

abbrev F11 := ZMod 11

abbrev DihF11Sq :=
  {z : F11 × (F11 × F11) // z.1 = 1 ∨ z.1 = -1}

def dihMul (x y : DihF11Sq) : DihF11Sq :=
  ⟨(x.1.1 * y.1.1,
      (x.1.2.1 + x.1.1 * y.1.2.1,
       x.1.2.2 + x.1.1 * y.1.2.2)), by
    rcases x.2 with hx | hx <;> rcases y.2 with hy | hy <;>
      simp [hx, hy]⟩

def dihInv (x : DihF11Sq) : DihF11Sq :=
  ⟨(x.1.1, (-x.1.1 * x.1.2.1, -x.1.1 * x.1.2.2)), by
    rcases x.2 with hx | hx <;> simp [hx]⟩

def dihOne : DihF11Sq :=
  ⟨(1, (0, 0)), Or.inl rfl⟩

def quadraticForm11 (x y : F11) : F11 :=
  x - y ^ 2 * (4 : F11)⁻¹

def setA11 : Set F11 := {0, 1, 3}

def setB11 : Set F11 := {1, -1}

def cayleyS : Set DihF11Sq :=
  {h | (h.1.1 = -1 ∧ quadraticForm11 h.1.2.1 h.1.2.2 ∈ setA11) ∨
    (h.1.1 = 1 ∧ h.1.2.2 ∈ setB11)}

def theta : DihF11Sq → DihF11Sq := fun h =>
  ⟨(h.1.1,
      (h.1.2.1 ^ 2 * (2 : F11)⁻¹ - h.1.2.2, h.1.1 * h.1.2.1)), h.2⟩

def cayleyT : Set DihF11Sq := theta ⁻¹' cayleyS

def cayleyAdj (U : Set DihF11Sq) (x y : DihF11Sq) : Prop :=
  dihMul x (dihInv y) ∈ U

def inverseClosed (U : Set DihF11Sq) : Prop :=
  ∀ x : DihF11Sq, x ∈ U → dihInv x ∈ U

def identityFree (U : Set DihF11Sq) : Prop :=
  dihOne ∉ U

def hasCard55 (U : Set DihF11Sq) : Prop :=
  Nat.card {x : DihF11Sq // x ∈ U} = 55

def cayleyIsomorphism (U V : Set DihF11Sq) (f : DihF11Sq → DihF11Sq) : Prop :=
  Function.Bijective f ∧
    ∀ x y : DihF11Sq, cayleyAdj U x y ↔ cayleyAdj V (f x) (f y)

def dihAutomorphism (e : DihF11Sq ≃ DihF11Sq) : Prop :=
  e dihOne = dihOne ∧
    ∀ x y : DihF11Sq, e (dihMul x y) = dihMul (e x) (e y)

def undirectedCIGroup : Prop :=
  ∀ U V : Set DihF11Sq,
    identityFree U → inverseClosed U → identityFree V → inverseClosed V →
    (∃ f : DihF11Sq → DihF11Sq, cayleyIsomorphism U V f) →
    ∃ e : DihF11Sq ≃ DihF11Sq, dihAutomorphism e ∧ e '' U = V

/-- Claim 59796: the displayed finite witness is a non-CI witness. -/
def admittedClaim59796 : Prop :=
  identityFree cayleyS ∧ identityFree cayleyT ∧
  inverseClosed cayleyS ∧ inverseClosed cayleyT ∧
  hasCard55 cayleyS ∧ hasCard55 cayleyT ∧
  cayleyIsomorphism cayleyT cayleyS theta ∧
  (¬ ∃ e : DihF11Sq ≃ DihF11Sq,
    dihAutomorphism e ∧ e '' cayleyT = cayleyS) ∧
  ¬ undirectedCIGroup

end MathlibPlus.Open.ResearchFormalization
