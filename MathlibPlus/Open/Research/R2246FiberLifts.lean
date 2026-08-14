import Mathlib

namespace MathlibPlus.Open.Research.R2246

/-- A chart with a common model fibre. -/
def chartPoint {B F Ω : Type*} (ι : B × F ≃ Ω)
    (b : B) (u : F) : Ω := ι (b, u)

def graphAutomorphism {Ω : Type*} (Γ : SimpleGraph Ω) (f : Ω → Ω) : Prop :=
  Function.Bijective f ∧ ∀ x y, Γ.Adj x y ↔ Γ.Adj (f x) (f y)

def inducesBlock {B F Ω : Type*} (ι : B × F ≃ Ω)
    (f : Ω → Ω) (q : B ≃ B) : Prop :=
  ∀ b u, (ι.symm (f (chartPoint ι b u))).1 = q b

def fiberLift {B F Ω : Type*} (ι : B × F ≃ Ω)
    (q : B ≃ B) (φ : B → F ≃ F) : Ω → Ω :=
  fun x =>
    let y := ι.symm x
    ι (q y.1, φ y.1 y.2)

def LiftGamma {B F Ω : Type*} (Γ : SimpleGraph Ω)
    (ι : B × F ≃ Ω) (q : B ≃ B) : Set (B → F ≃ F) :=
  {φ | graphAutomorphism Γ (fiberLift ι q φ)}

def actualFiber {B F Ω : Type*} (Γ : SimpleGraph Ω)
    (ι : B × F ≃ Ω) (q : B ≃ B) : Set (Ω → Ω) :=
  {f | graphAutomorphism Γ f ∧ inducesBlock ι f q}

def BlockImage {B F Ω : Type*} (Γ : SimpleGraph Ω)
    (ι : B × F ≃ Ω) (q : B ≃ B) : Prop :=
  ∃ f, f ∈ actualFiber Γ ι q

def LiftMembershipIsActual : Prop :=
  ∀ {B F Ω : Type*} [Fintype B] [Fintype F] [Fintype Ω]
    (Γ : SimpleGraph Ω) (ι : B × F ≃ Ω) (q : B ≃ B)
    (φ : B → F ≃ F),
    φ ∈ LiftGamma Γ ι q ↔
      graphAutomorphism Γ (fiberLift ι q φ)

def LiftFamilyBijection : Prop :=
  ∀ {B F Ω : Type*} [Fintype B] [Fintype F] [Fintype Ω]
    (Γ : SimpleGraph Ω) (ι : B × F ≃ Ω) (q : B ≃ B),
    (∀ φ, φ ∈ LiftGamma Γ ι q →
      fiberLift ι q φ ∈ actualFiber Γ ι q) ∧
    (∀ f, f ∈ actualFiber Γ ι q →
      ∃! φ, φ ∈ LiftGamma Γ ι q ∧ fiberLift ι q φ = f) ∧
    ((∃ φ, φ ∈ LiftGamma Γ ι q) ↔ BlockImage Γ ι q)

def complementAdj {Ω : Type*} (Γ : SimpleGraph Ω) (x y : Ω) : Prop :=
  x ≠ y ∧ ¬ Γ.Adj x y

def complementAutomorphism {Ω : Type*} (Γ : SimpleGraph Ω) (f : Ω → Ω) : Prop :=
  Function.Bijective f ∧ ∀ x y,
    complementAdj Γ x y ↔ complementAdj Γ (f x) (f y)

def complementLift {B F Ω : Type*} (Γ : SimpleGraph Ω)
    (ι : B × F ≃ Ω) (q : B ≃ B) : Set (B → F ≃ F) :=
  {φ | complementAutomorphism Γ (fiberLift ι q φ)}

def ComplementationInvariance : Prop :=
  ∀ {B F Ω : Type*} [Fintype B] [Fintype F] [Fintype Ω]
    (Γ : SimpleGraph Ω) (ι : B × F ≃ Ω) (q : B ≃ B),
    (∀ f : Ω → Ω,
      graphAutomorphism Γ f ↔ complementAutomorphism Γ f) ∧
    (∀ φ : B → F ≃ F,
      φ ∈ LiftGamma Γ ι q ↔ φ ∈ complementLift Γ ι q) ∧
    (∀ f : Ω → Ω,
      f ∈ actualFiber Γ ι q ↔
        (complementAutomorphism Γ f ∧ inducesBlock ι f q))

end MathlibPlus.Open.Research.R2246
