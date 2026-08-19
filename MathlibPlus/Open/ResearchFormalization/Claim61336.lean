import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim61336

noncomputable section

abbrev D := ZMod 3
abbrev H := Fin 2 → D
abbrev V := D × H

/-- Adjacency in the simple additive Cayley graph on `V`. -/
def cayleyAdj (S : Set V) (x y : V) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- The hypotheses that a connection set is identity-free and inverse-closed. -/
def identityFree (S : Set V) : Prop :=
  (0 : V) ∉ S

def inverseClosed (S : Set V) : Prop :=
  ∀ x : V, x ∈ S ↔ -x ∈ S

/-- Automorphisms of the simple Cayley graph determined by `S`. -/
def graphAutomorphism (S : Set V) (f : Equiv.Perm V) : Prop :=
  ∀ x y : V, cayleyAdj S x y ↔ cayleyAdj S (f x) (f y)

def automorphismSet (S : Set V) : Set (Equiv.Perm V) :=
  {f | graphAutomorphism S f}

/-- Translation by the central ternary line `D × {0}`. -/
def dTranslation (d : D) : Equiv.Perm V :=
  Equiv.addRight (d, 0)

def dTranslationGroup : Subgroup (Equiv.Perm V) :=
  Subgroup.closure (Set.range dTranslation)

/-- The actual centralizer of the `D`-translation subgroup inside the graph
automorphism set. -/
def centralizerSet (S : Set V) : Set (Equiv.Perm V) :=
  {f | f ∈ automorphismSet S ∧
    ∀ t : dTranslationGroup,
      f * (t : Equiv.Perm V) = (t : Equiv.Perm V) * f}

/-- The permutation group induced on the nine `D`-translation orbits, with
those orbits identified with `H`. -/
def inducedImage (S : Set V) : Set (Equiv.Perm H) :=
  {sigma | ∃ f : Equiv.Perm V,
    f ∈ centralizerSet S ∧
      ∀ d : D, ∀ h : H, (f (d, h)).2 = sigma h}

/-- The stabilizer at the zero `D`-orbit in the induced image. -/
def inducedZeroStabilizer (S : Set V) : Set (Equiv.Perm H) :=
  {sigma | sigma ∈ inducedImage S ∧ sigma 0 = 0}

/-- The orbit of a quotient point under the pointed induced image. -/
def inducedStabilizerOrbit (S : Set V) (h : H) : Set H :=
  {u | ∃ sigma : Equiv.Perm H,
    sigma ∈ inducedZeroStabilizer S ∧ sigma h = u}

/-- The lift through the central ternary line associated with `n` and a carry
function `c`. -/
def centralLineLift (n : H ≃ₗ[D] H) (c : H → D) : V → V :=
  fun p => (p.1 + c p.2, n p.2)

/-- Existence of an actual graph automorphism having the displayed lift form. -/
def hasCentralLineLift (S : Set V) (n : H ≃ₗ[D] H) : Prop :=
  ∃ c : H → D, c 0 = 0 ∧
    ∃ y : Equiv.Perm V,
      y ∈ centralizerSet S ∧
        ∀ d : D, ∀ h : H,
          y (d, h) = centralLineLift n c (d, h)

/-- Membership in the binary two-closure of the induced image, expressed by
ordered-pair agreement. -/
def binaryTwoClosure (S : Set V) : Set (Equiv.Perm H) :=
  {q | ∀ x y : H, ∃ sigma : Equiv.Perm H,
    sigma ∈ inducedImage S ∧ sigma x = q x ∧ sigma y = q y}

/-- The linear pointed part of the binary two-closure is contained in the
actual pointed induced image. -/
def linearTwoClosureActualImage (S : Set V) : Prop :=
  ∀ n : H ≃ₗ[D] H,
    n.toEquiv ∈ binaryTwoClosure S →
      n.toEquiv 0 = 0 →
        n.toEquiv ∈ inducedZeroStabilizer S

/-- Claim 61336: at `V = F₃ ⊕ F₃²`, every linear quotient permutation whose
values lie in the pointed induced-image orbits has an actual central-line lift;
equivalently, the pointed linear part of the binary two-closure is already in
the actual induced image. -/
def claim61336 : Prop :=
  ∀ S : Set V,
    identityFree S →
      inverseClosed S →
        (∀ n : H ≃ₗ[D] H,
          (∀ h : H, n h ∈ inducedStabilizerOrbit S h) →
            n.toEquiv ∈ inducedImage S ∧
              hasCentralLineLift S n) ∧
        linearTwoClosureActualImage S

end

end MathlibPlus.Open.ResearchFormalization.Claim61336
