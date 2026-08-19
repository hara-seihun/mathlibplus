import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim61258

noncomputable section

/-- Ordinary additive Cayley adjacency on the exact vector-space carrier. -/
def cayleyAdj {V : Type*} [AddGroup V]
    (S : Set V) (x y : V) : Prop :=
  y - x ∈ S

def identityFree {V : Type*} [Zero V] (S : Set V) : Prop :=
  (0 : V) ∉ S

def inverseClosed {V : Type*} [Neg V] (S : Set V) : Prop :=
  ∀ x : V, x ∈ S ↔ -x ∈ S

def cayleyGraphIsomorphism {V : Type*} [AddGroup V]
    (S T : Set V) (f : V ≃ V) : Prop :=
  ∀ x y : V,
    cayleyAdj S x y ↔ cayleyAdj T (f x) (f y)

/-- Claim 61258: an even perturbation of an invertible linear map has the
linear image as the exact transporter for every identity-free inverse-closed
ordinary undirected Cayley connection set that it transports. -/
def evenPerturbationMidpointShadow : Prop :=
  ∀ (F V : Type*) [Field F] [Fintype F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V],
    Odd (Fintype.card F) →
      ∀ (A : V ≃ₗ[F] V) (E : V → V) (f : V ≃ V)
        (S T : Set V),
        (∀ x : V, E (-x) = E x) →
          (∀ x : V, f x = A x + E x) →
            identityFree S →
              identityFree T →
                inverseClosed S →
                  inverseClosed T →
                    cayleyGraphIsomorphism S T f →
                      Set.image (A : V → V) S = T

end

end MathlibPlus.Open.ResearchFormalization.Claim61258
