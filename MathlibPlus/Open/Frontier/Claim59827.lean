import Mathlib

namespace MathlibPlus.Open.Frontier

abbrev F3Vec (r : ℕ) := Fin r → ZMod 3

def connectionSetNonzero {r : ℕ} (S : Finset (F3Vec r)) : Prop :=
  ∀ s ∈ S, s ≠ 0

def connectionSetInverseClosed {r : ℕ} (S : Finset (F3Vec r)) : Prop :=
  ∀ s ∈ S, -s ∈ S

def connectionSetSpans {r : ℕ} (S : Finset (F3Vec r)) : Prop :=
  Submodule.span (ZMod 3) (S : Set (F3Vec r)) = ⊤

def cayleyGraph {r : ℕ} (S : Finset (F3Vec r))
    (hS : connectionSetNonzero S)
    (hInv : connectionSetInverseClosed S) : SimpleGraph (F3Vec r) :=
  { Adj := fun v w => w - v ∈ S
    symm := Std.Symm.mk (fun v w h => by
      simpa using hInv (w - v) h)
    loopless := Std.Irrefl.mk (fun v h => by
      exact (hS 0 (by simpa using h)) rfl) }

def cayleyGraphIso {r : ℕ}
    (S T : Finset (F3Vec r))
    (hS : connectionSetNonzero S)
    (hInvS : connectionSetInverseClosed S)
    (hT : connectionSetNonzero T)
    (hInvT : connectionSetInverseClosed T) : Prop :=
  Nonempty (SimpleGraph.Iso (cayleyGraph S hS hInvS) (cayleyGraph T hT hInvT))

def linearImage {r : ℕ} (A : F3Vec r ≃ₗ[ZMod 3] F3Vec r)
    (S : Finset (F3Vec r)) : Set (F3Vec r) :=
  A '' (S : Set (F3Vec r))

def ciCayleyGraph {r : ℕ} (S : Finset (F3Vec r))
    (hS : connectionSetNonzero S)
    (hInvS : connectionSetInverseClosed S) : Prop :=
  ∀ (T : Finset (F3Vec r))
    (hT : connectionSetNonzero T)
    (hInvT : connectionSetInverseClosed T),
    cayleyGraphIso S T hS hInvS hT hInvT →
    ∃ A : F3Vec r ≃ₗ[ZMod 3] F3Vec r,
      linearImage A S = (T : Set (F3Vec r))

def claim59827Main : Prop :=
  ∀ (r : ℕ) (_ : 2 ≤ r)
    (S : Finset (F3Vec r))
    (hS : connectionSetNonzero S)
    (hInvS : connectionSetInverseClosed S)
    (_ : connectionSetSpans S),
    S.card = 2 * (r + 2) →
    ciCayleyGraph S hS hInvS

def claim59827InParticular : Prop :=
  (∀ (S : Finset (F3Vec 6))
      (hS : connectionSetNonzero S)
      (hInvS : connectionSetInverseClosed S)
      (_ : connectionSetSpans S),
      S.card = 16 → ciCayleyGraph S hS hInvS) ∧
  (∀ (S : Finset (F3Vec 7))
      (hS : connectionSetNonzero S)
      (hInvS : connectionSetInverseClosed S)
      (_ : connectionSetSpans S),
      S.card = 18 → ciCayleyGraph S hS hInvS)

def claim59827 : Prop :=
  claim59827Main ∧ claim59827InParticular

end MathlibPlus.Open.Frontier
