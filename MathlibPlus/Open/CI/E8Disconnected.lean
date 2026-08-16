import Mathlib

namespace MathlibPlus.Open.CI

abbrev E8Carrier (p : Nat) := Fin 8 × ZMod p

def e8One (p : Nat) : E8Carrier p := (0, 0)

def e8Mul (p : Nat) (g h : E8Carrier p) : E8Carrier p :=
  (g.1 + h.1, g.2 + ((-1 : ZMod p) ^ g.1.val) * h.2)

def e8IdentityFree (p : Nat) (S : Set (E8Carrier p)) : Prop :=
  e8One p ∉ S

def e8InverseClosed (p : Nat) (S : Set (E8Carrier p)) : Prop :=
  ∀ ⦃g h : E8Carrier p⦄,
    g ∈ S → e8Mul p g h = e8One p → e8Mul p h g = e8One p → h ∈ S

def e8Adj (p : Nat) (S : Set (E8Carrier p))
    (g h : E8Carrier p) : Prop :=
  ∃ s, s ∈ S ∧ e8Mul p g s = h

def e8GraphIso (p : Nat) (S T : Set (E8Carrier p)) : Prop :=
  ∃ φ : E8Carrier p → E8Carrier p,
    Function.Bijective φ ∧
      ∀ g h, e8Adj p S g h ↔ e8Adj p T (φ g) (φ h)

def e8AutMaps (p : Nat) (α : E8Carrier p → E8Carrier p) : Prop :=
  Function.Bijective α ∧
    ∀ g h, α (e8Mul p g h) = e8Mul p (α g) (α h)

def e8MapsSet (p : Nat) (α : E8Carrier p → E8Carrier p)
    (S T : Set (E8Carrier p)) : Prop :=
  ∀ g, g ∈ S ↔ α g ∈ T

def e8CI (p : Nat) : Prop :=
  ∀ S T : Set (E8Carrier p),
    e8IdentityFree p S →
    e8InverseClosed p S →
    e8IdentityFree p T →
    e8InverseClosed p T →
    e8GraphIso p S T →
    ∃ α : E8Carrier p → E8Carrier p,
      e8AutMaps p α ∧ e8MapsSet p α S T

def E8_CI_5_7 : Prop := e8CI 5 ∧ e8CI 7

def e8ComplementConnection (p : Nat) (S : Set (E8Carrier p)) : Set (E8Carrier p) :=
  {g | g ≠ e8One p ∧ g ∉ S}

def e8Connected (p : Nat) (S : Set (E8Carrier p)) : Prop :=
  ∀ g h : E8Carrier p, Relation.ReflTransGen (e8Adj p S) g h

def e8Disconnected (p : Nat) (S : Set (E8Carrier p)) : Prop :=
  ¬ e8Connected p S

def E8_35_DisconnectedOrCoDisconnected_CI : Prop :=
  ∀ S T : Set (E8Carrier 35),
    e8IdentityFree 35 S →
    e8InverseClosed 35 S →
    e8IdentityFree 35 T →
    e8InverseClosed 35 T →
    e8GraphIso 35 S T →
    (e8Disconnected 35 S ∨
      e8Disconnected 35 (e8ComplementConnection 35 S)) →
    ∃ α : E8Carrier 35 → E8Carrier 35,
      e8AutMaps 35 α ∧ e8MapsSet 35 α S T

end MathlibPlus.Open.CI
