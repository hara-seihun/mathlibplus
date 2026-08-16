import Mathlib

noncomputable section

namespace MathlibPlus.Open

namespace Reconcile5355

abbrev SourceVariable := Option Nat
abbrev SourceRing := MvPolynomial SourceVariable Int
abbrev AtomVariable (k : Nat) := Option (Fin k × Bool)
abbrev AtomRing (k : Nat) := MvPolynomial (AtomVariable k) Int

def zVar : SourceVariable := none

def xVar (n : Nat) : SourceVariable := some n

def zAtom {k : Nat} : AtomVariable k := none

def aAtom {k : Nat} (i : Fin k) : AtomVariable k := some (i, false)

def rAtom {k : Nat} (i : Fin k) : AtomVariable k := some (i, true)

def z : SourceRing := MvPolynomial.X zVar

def x (n : Nat) : SourceRing := MvPolynomial.X (xVar n)

def atomZ {k : Nat} : AtomRing k := MvPolynomial.X zAtom

def atomA {k : Nat} (i : Fin k) : AtomRing k := MvPolynomial.X (aAtom i)

def atomR {k : Nat} (i : Fin k) : AtomRing k := MvPolynomial.X (rAtom i)

def variableWeight : SourceVariable → Nat
  | none => 1
  | some n => n + 1

def monomialWeight (m : SourceVariable →₀ Nat) : Nat :=
  m.sum (fun v e => e * variableWeight v)

def mu (k : Nat) (j : Nat) : AtomRing k :=
  ∑ i : Fin k, atomA i * atomR i ^ j

def sourceToAtoms (k : Nat) : SourceVariable → AtomRing k
  | none => atomZ
  | some n => mu k n

def M (k : Nat) : SourceRing →+* AtomRing k :=
  MvPolynomial.eval₂Hom (Int.castRingHom (AtomRing k)) (sourceToAtoms k)

def specializeAt (k : Nat) (i : Fin k) : SourceVariable → AtomRing k
  | none => atomR i
  | some n => mu k n

def HAt (k : Nat) (i : Fin k) : SourceRing →+* AtomRing k :=
  MvPolynomial.eval₂Hom (Int.castRingHom (AtomRing k)) (specializeAt k i)

def shiftMonomial (s : Nat) (m : SourceVariable →₀ Nat) : SourceVariable →₀ Nat :=
  m.erase zVar + Finsupp.single (xVar (m zVar + s - 1)) 1

def Phi (s : Nat) : SourceRing → SourceRing :=
  fun H => H.support.sum
    (fun m => MvPolynomial.monomial (shiftMonomial s m) (MvPolynomial.coeff m H))

def formalShiftIdentity (k s : Nat) (H : SourceRing) : Prop :=
  M k (Phi s H) = ∑ i : Fin k, atomA i * atomR i ^ (s - 1) * HAt k i H

def claim60518 : Prop :=
  ∀ (k s : Nat) (H : SourceRing),
    0 < k → 0 < s → formalShiftIdentity k s H

end Reconcile5355

namespace Reconcile5650

variable (L M : Type*) [Fintype L] [Group L] [Fintype M] [AddCommGroup M]
  [DistribMulAction L M]

def cocycle (d : L → M) : Prop :=
  ∀ g h : L, d (g * h) = d g + g • d h

def cocycleSum (d : L → M) : M := ∑ h : L, d h

def coprimeCocycleConclusion : Prop :=
  Nat.Coprime (Fintype.card L) (Fintype.card M) →
    Function.Bijective (fun m : M => (Fintype.card L) • m) ∧
    ∀ (d : L → M), cocycle L M d →
      ∃ a : M, (Fintype.card L) • a = cocycleSum L M d ∧
        ∀ g : L, d g = a - g • a

def claim60769 : Prop :=
  coprimeCocycleConclusion L M

end Reconcile5650

end MathlibPlus.Open
