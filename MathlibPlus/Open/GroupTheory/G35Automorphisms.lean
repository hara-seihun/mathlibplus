import Mathlib

namespace MathlibPlus.Open.GroupTheory

def G35Omega : Type := ZMod 8 × ZMod 35

def G35Odd (j : ZMod 8) : Prop :=
  j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7

noncomputable def G35OddIndicator (j : ZMod 8) : ZMod 35 := by
  classical
  exact if G35Odd j then 1 else 0

noncomputable def G35Mul (p q : G35Omega) : G35Omega := by
  classical
  exact (p.1 + q.1, p.2 + if G35Odd p.1 then -q.2 else q.2)

def G35Automorphism (f : G35Omega ≃ G35Omega) : Prop :=
  ∀ p q, f (G35Mul p q) = G35Mul (f p) (f q)

noncomputable def G35Alpha (u : Units (ZMod 35)) (v : ZMod 35) (r : Units (ZMod 8))
    (p : G35Omega) : G35Omega :=
  ((r : ZMod 8) * p.1,
    (u : ZMod 35) * p.2 + v * G35OddIndicator p.1)

def G35AllowedR (r : Units (ZMod 8)) : Prop :=
  (r : ZMod 8) = 1 ∨ (r : ZMod 8) = 3 ∨
    (r : ZMod 8) = 5 ∨ (r : ZMod 8) = 7

def G35AutomorphismClassification : Prop :=
  (∀ (f : G35Omega ≃ G35Omega),
    G35Automorphism f →
      ∃ (u : Units (ZMod 35)) (v : ZMod 35) (r : Units (ZMod 8)),
        G35AllowedR r ∧
          ∀ (j : ZMod 8) (x : ZMod 35),
            f (j, x) = G35Alpha u v r (j, x)) ∧
  Nat.card {f : G35Omega ≃ G35Omega // G35Automorphism f} = 24 * 35 * 4

end MathlibPlus.Open.GroupTheory
