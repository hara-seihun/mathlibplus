import MathlibPlus.Open.Research.BlockAxisDirectionRigidity60202

namespace MathlibPlus.Open.ResearchFormalization.AffineFibreTransporter

noncomputable section

open MathlibPlus.Open.Research

/-- Inverse-closedness for an additive connection set. -/
def inverseClosed {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  ∀ x, x ∈ S → -x ∈ S

/-- The product automorphism using one fixed fibre automorphism. -/
def productTransporter {V A : Type*} [AddCommGroup V] [AddCommGroup A]
    (L : V ≃+ V) (φ : A ≃+ A) : (V × A) ≃+ (V × A) :=
  AddEquiv.prodCongr L φ

/-- Claim 61039: every fibrewise affine isomorphism of inverse-closed
ordinary Cayley graphs transports the connection set by the one fixed
product automorphism `(L, φ 0)`. -/
def affineFibreTransporterTheorem_claim61039 : Prop :=
  ∀ (V A : Type*) [Fintype V] [AddCommGroup V]
    [Fintype A] [AddCommGroup A],
    (∀ v : V, v + v = 0) →
    Odd (Fintype.card A) →
    ∀ S T : Set (V × A),
      S ⊆ ({(0, 0)} : Set (V × A))ᶜ →
      T ⊆ ({(0, 0)} : Set (V × A))ᶜ →
      inverseClosed S →
      inverseClosed T →
      ∀ F : SimpleGraph.Iso
          (additiveCayleyGraph S) (additiveCayleyGraph T),
        ∀ a : V, ∀ L : V ≃+ V,
          ∀ b : V → A, ∀ φ : V → (A ≃+ A),
            (∀ v : V, ∀ z : A,
              F.toEquiv (v, z) =
                (a + L v, b v + φ v z)) →
            Set.image (productTransporter L (φ 0)) S = T

end

end MathlibPlus.Open.ResearchFormalization.AffineFibreTransporter
