import MathlibPlus.Open.FibreTranslationBatch

namespace MathlibPlus.Open.ResearchFormalization.R1929Claim36260

noncomputable section

open MathlibPlus.Open.FibreTranslation

/-- Setwise fixation of every orbit of the fibre-translation subgroup. -/
def affineOrbitSetwiseFixation
    {A B : Type*} [AddCommGroup A]
    (K : FibreTranslationSubgroup A B) (q : Equiv.Perm (A × B)) : Prop :=
  ∀ x : A × B,
    Set.image q (fibreOrbit K x) = fibreOrbit K x

/-- The four conditions on one projected component, written directly on the
chosen holonomy and potential data. -/
def componentAffineFixationConditions
    {A B : Type*} [AddCommGroup A]
    {K : FibreTranslationSubgroup A B}
    (C : FibreComponentData A B K) (u : A ≃+ A)
    (s : B → A) (qbar : B ≃ B) : Prop :=
  qbar '' C.carrier = C.carrier ∧
    u '' (C.holonomy : Set A) = (C.holonomy : Set A) ∧
      (∀ a : A, u a - a ∈ C.holonomy) ∧
        (∀ b : B, b ∈ C.carrier →
          s b + u (C.potential b) - C.potential (qbar b) ∈ C.holonomy)

/-- The representative-change calculation in the criterion.  The two
representatives may differ independently by holonomy elements at every base
point. -/
def componentRepresentativeIndependence
    {A B : Type*} [AddCommGroup A]
    {K : FibreTranslationSubgroup A B}
    (C : FibreComponentData A B K) (u : A ≃+ A)
    (s : B → A) (qbar : B ≃ B) : Prop :=
  ∀ (t t' : B → A),
    (∀ b : B, b ∈ C.carrier → t' b - t b ∈ C.holonomy) →
      qbar '' C.carrier = C.carrier →
        u '' (C.holonomy : Set A) = (C.holonomy : Set A) →
          (∀ a : A, u a - a ∈ C.holonomy) →
            ∀ b : B, b ∈ C.carrier →
              ((s b + u (t' b) - t' (qbar b)) -
                  (s b + u (t b) - t (qbar b)) =
                    u (t' b - t b) - (t' (qbar b) - t (qbar b))) ∧
                (s b + u (t' b) - t' (qbar b)) -
                    (s b + u (t b) - t (qbar b)) ∈ C.holonomy

/-- Claim 36260: an affine map of the stated form fixes every K-orbit
setwise exactly when all projected components satisfy all four conditions;
the congruence is independent of the chosen representatives. -/
def claim36260 : Prop :=
  ∀ (A B : Type*) [AddCommGroup A] [Fintype A] [Fintype B]
    (K : FibreTranslationSubgroup A B)
    (q : Equiv.Perm (A × B)) (u : A ≃+ A)
    (s : B → A) (qbar : B ≃ B),
    (∀ a : A, ∀ b : B,
      q (a, b) = (u a + s b, qbar b)) →
      (affineOrbitSetwiseFixation K q ↔
        ∀ C : FibreComponentData A B K,
          componentAffineFixationConditions C u s qbar) ∧
        (∀ C : FibreComponentData A B K,
          componentRepresentativeIndependence C u s qbar)

end

end MathlibPlus.Open.ResearchFormalization.R1929Claim36260
