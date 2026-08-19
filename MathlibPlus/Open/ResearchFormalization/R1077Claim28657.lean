import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1077

noncomputable section
open scoped BigOperators

abbrev F3 := ZMod 3
abbrev W := Fin 3 → F3
abbrev V := Fin 5 → F3
abbrev G := W × V
abbrev ProjectiveNormal := Projectivization F3 W

/-- The five-dimensional polynomial correction in the fibre coordinates. -/
def correction (w : W) : V :=
  ![w 0 * (w 1) ^ 2,
    w 0 * (w 2) ^ 2,
    (w 1) ^ 2 * w 2,
    w 1 * (w 2) ^ 2,
    w 0 * w 1 * w 2]

/-- The rank-eight polynomial shear `ψ(w,v)=(w,v+c(w))`. -/
def psi : G → G :=
  fun p => (p.1, p.2 + correction p.1)

/-- The linear functional represented by a nonzero projective normal. -/
def normalFunctional (n : W) : W →ₗ[F3] F3 :=
  ∑ i : Fin 3, n i • LinearMap.proj i

def normalHyperplane (n : ProjectiveNormal) : Submodule F3 G :=
  (LinearMap.ker (normalFunctional n.rep)).prod (⊤ : Submodule F3 V)

def linearHyperplane (U : Submodule F3 G) : Prop :=
  Module.finrank F3 U = 7

def hyperplaneInvariant (U : Submodule F3 G) : Prop :=
  Set.image psi (U : Set G) = U

abbrev InvariantHyperplane :=
  {U : Submodule F3 G // linearHyperplane U ∧ hyperplaneInvariant U}

/-- Claim 28657: the invariant linear hyperplanes of the explicit rank-eight
polynomial shear are exactly the thirteen projective-normal hyperplanes, and
an invariant hyperplane's defining functional vanishes on the fibre. -/
def claim28657 : Prop :=
  Function.Bijective psi ∧
  (∀ n : ProjectiveNormal,
    linearHyperplane (normalHyperplane n) ∧
      hyperplaneInvariant (normalHyperplane n)) ∧
  (∀ U : Submodule F3 G,
    linearHyperplane U →
      hyperplaneInvariant U →
        (∃ ell : G →ₗ[F3] F3,
          ell ≠ 0 ∧
            LinearMap.ker ell = U ∧
              ∀ v : V, ell (0, v) = 0) ∧
          ∃! n : ProjectiveNormal, U = normalHyperplane n) ∧
  letI : Fintype ProjectiveNormal := Fintype.ofFinite _
  letI : Fintype InvariantHyperplane := Fintype.ofFinite _
  Fintype.card ProjectiveNormal = 13 ∧
    Fintype.card InvariantHyperplane = 13

end
end MathlibPlus.Open.ResearchFormalization.R1077
