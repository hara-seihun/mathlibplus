import MathlibPlus.Open.ResearchFormalization.C7AffineSectionTransporter

open Classical
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R1210SmallProfiles

open MathlibPlus.Open.ResearchFormalization.C7AffineSectionTransporter

/-- Translation of a subset of the C₇² kernel. -/
def translateKernelSet (B : Finset C7Vector) (v : C7Vector) :
    Finset C7Vector :=
  B.image (fun b => b + v)

def tripleKernelSet (B : Finset C7Vector) : Finset C7Vector :=
  B.image (fun b => 3 • b)

def profileConnectionSet (K B : Finset C7Vector) : Finset EPoint :=
  K.image (fun a => (a, (0 : Fin 3))) ∪
    B.image (fun a => (a, (1 : Fin 3))) ∪
      (tripleKernelSet B).image (fun a => (a, (2 : Fin 3)))

def profileSection (S : Finset EPoint) (i : Fin 3) : Finset C7Vector :=
  S.filter (fun p => p.2 = i) |>.image Prod.fst

def profileMap (ψ : Fin 3 → C7Vector → C7Vector) : EPoint → EPoint :=
  fun p => (ψ p.2 p.1, p.2)

def profileImage (ψ : Fin 3 → C7Vector → C7Vector)
    (S : Finset EPoint) : Finset EPoint :=
  S.image (profileMap ψ)

def kernelMapImage (ψ : Fin 3 → C7Vector → C7Vector)
    (i : Fin 3) (S : Finset C7Vector) : Finset C7Vector :=
  S.image (ψ i)

def extensionInverse (x : EPoint) : EPoint :=
  (-((2 : ZMod 7) ^ x.2.val)⁻¹ • x.1, -x.2)

def inverseClosedProfileSet (S : Finset EPoint) : Prop :=
  ∀ x ∈ S, extensionInverse x ∈ S

/-- The exact normalized, quotient-identity, kernel-coset profile carrier.
The two displayed equations are the side-colored translation-development
interface for its first nonidentity section. -/
def normalizedProfile (K B C : Finset C7Vector)
    (ψ : Fin 3 → C7Vector → C7Vector) : Prop :=
  (∀ i : Fin 3, Function.Bijective (ψ i)) ∧
    (K = ∅ ∨ K = Finset.univ) ∧
    inverseClosedProfileSet (profileConnectionSet K B) ∧
    inverseClosedProfileSet (profileConnectionSet K C) ∧
    profileImage ψ (profileConnectionSet K B) =
      profileConnectionSet K C ∧
    (∀ y : C7Vector,
      kernelMapImage ψ 1 (translateKernelSet B (2 • y)) =
        translateKernelSet C (2 • ψ 0 y))

/-- Claim 32279: every exact small/co-small empty- or complete-kernel profile
with arbitrary 49-point coset permutations has an affine E(C₇²,3)
automorphism carrying the entire inverse-closed connection set to its image. -/
def smallAndCosmallProfilesCIHarmless_claim32279 : Prop :=
  ∀ (K B C : Finset C7Vector)
    (ψ : Fin 3 → C7Vector → C7Vector),
    normalizedProfile K B C ψ →
      (B.card ≤ 13 ∨ 36 ≤ B.card) →
        ∃ (L : C7Vector ≃ₗ[ZMod 7] C7Vector) (c : C7Vector),
          C = affineImage L c B ∧
            extensionAutomorphism (sectionTransport L c) ∧
            (profileConnectionSet K B).image (sectionTransport L c) =
              profileConnectionSet K C

end MathlibPlus.Open.ResearchFormalization.R1210SmallProfiles
