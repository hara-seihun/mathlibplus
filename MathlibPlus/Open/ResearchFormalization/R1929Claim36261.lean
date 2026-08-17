import MathlibPlus.Open.FibreTranslationBatch

namespace MathlibPlus.Open.ResearchFormalization.R1929Claim36261

noncomputable section

open MathlibPlus.Open.FibreTranslation

/-- The voltage cocycle identity for composition in the fibre semidirect
product. -/
def fibreCocycleIdentity
    {A B : Type*} [AddCommGroup A]
    (K : FibreTranslationSubgroup A B) : Prop :=
  ∀ (γ δ : FibreTranslationElement A B),
    γ ∈ K.carrier → δ ∈ K.carrier →
      ∀ b : B,
        (FibreTranslationElement.mul γ δ).shift b =
          δ.shift b + γ.shift (δ.base b)

/-- Closed voltages at the chosen component root are exactly its holonomy. -/
def closedVoltagesAreHolonomy
    {A B : Type*} [AddCommGroup A]
    {K : FibreTranslationSubgroup A B}
    (C : FibreComponentData A B K) : Prop :=
  ∀ h : A,
    h ∈ C.holonomy ↔
      ∃ γ : FibreTranslationElement A B,
        γ ∈ K.carrier ∧ γ.base C.basepoint = C.basepoint ∧
          γ.shift C.basepoint = h

/-- Two transports to one endpoint differ by a closed voltage. -/
def pathsDifferByHolonomy
    {A B : Type*} [AddCommGroup A]
    {K : FibreTranslationSubgroup A B}
    (C : FibreComponentData A B K) : Prop :=
  ∀ b : B, b ∈ C.carrier →
    ∀ γ δ : FibreTranslationElement A B,
      γ ∈ K.carrier → δ ∈ K.carrier →
        γ.base C.basepoint = b → δ.base C.basepoint = b →
          γ.shift C.basepoint - δ.shift C.basepoint ∈ C.holonomy

/-- Appending closed paths realizes every holonomy difference. -/
def everyHolonomyVoltageIsClosed
    {A B : Type*} [AddCommGroup A]
    {K : FibreTranslationSubgroup A B}
    (C : FibreComponentData A B K) : Prop :=
  ∀ h : A, h ∈ C.holonomy →
    ∃ γ : FibreTranslationElement A B,
      γ ∈ K.carrier ∧ γ.base C.basepoint = C.basepoint ∧
        γ.shift C.basepoint = h

/-- The orbit formula obtained from the cocycle and the two path assertions. -/
def holonomyOrbitFormula
    {A B : Type*} [AddCommGroup A]
    {K : FibreTranslationSubgroup A B}
    (C : FibreComponentData A B K) : Prop :=
  ∀ r : A,
    fibreOrbit K (r, C.basepoint) =
      {x : A × B | ∃ b : B, ∃ h : A,
        b ∈ C.carrier ∧ h ∈ C.holonomy ∧
          x = (r + C.potential b + h, b)}

/-- Applying an affine map to a displayed orbit point gives the displayed
fibre and base coordinates. -/
def affinePointActionFormula
    {A B : Type*} [AddCommGroup A]
    {K : FibreTranslationSubgroup A B}
    (C : FibreComponentData A B K) (u : A ≃+ A)
    (s : B → A) (qbar : B ≃ B) : Prop :=
  ∀ (r : A) (b : B) (h : A),
    b ∈ C.carrier → h ∈ C.holonomy →
      affineFibreAct u s qbar
          (r + C.potential b + h, b) =
        (u r + u (C.potential b) + u h + s b, qbar b)

/-- The complete necessary-and-sufficient criterion obtained by applying the
point formula to every holonomy orbit. -/
def criterionFromOrbitAction
    {A B : Type*} [AddCommGroup A] [Fintype A] [Fintype B]
    (K : FibreTranslationSubgroup A B)
    (q : Equiv.Perm (A × B)) (u : A ≃+ A)
    (s : B → A) (qbar : B ≃ B) : Prop :=
  (∀ a : A, ∀ b : B,
      q (a, b) = (u a + s b, qbar b)) →
    ((∀ x : A × B,
        Set.image q (fibreOrbit K x) = fibreOrbit K x) ↔
      ∀ C : FibreComponentData A B K,
        qbar '' C.carrier = C.carrier ∧
          u '' (C.holonomy : Set A) = (C.holonomy : Set A) ∧
            (∀ a : A, u a - a ∈ C.holonomy) ∧
              (∀ b : B, b ∈ C.carrier →
                s b + u (C.potential b) - C.potential (qbar b) ∈ C.holonomy))

/-- Claim 36261: the cocycle/closed-word mechanism, the exact holonomy orbit
formula, the affine point computation, and the resulting equivalence rather
than a one-way parity sufficiency test. -/
def claim36261 : Prop :=
  ∀ (A B : Type*) [AddCommGroup A] [Fintype A] [Fintype B]
    (K : FibreTranslationSubgroup A B),
    (∀ C : FibreComponentData A B K,
      fibreCocycleIdentity K ∧
        closedVoltagesAreHolonomy C ∧
          pathsDifferByHolonomy C ∧
            everyHolonomyVoltageIsClosed C ∧
              holonomyOrbitFormula C) ∧
      (∀ C : FibreComponentData A B K,
        ∀ (u : A ≃+ A) (s : B → A) (qbar : B ≃ B),
          affinePointActionFormula C u s qbar) ∧
        ∀ (q : Equiv.Perm (A × B)) (u : A ≃+ A)
          (s : B → A) (qbar : B ≃ B),
          criterionFromOrbitAction K q u s qbar

end

end MathlibPlus.Open.ResearchFormalization.R1929Claim36261
