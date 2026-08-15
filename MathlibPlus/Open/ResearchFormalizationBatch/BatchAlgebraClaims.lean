import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch

private abbrev TernaryProfileA := Fin 3 → ZMod 2
private abbrev TernaryProfileC := ZMod 3

/-- A normalized C₂³-by-C₃ translation profile and its triangular action. -/
def claim_29784 (f : TernaryProfileA × TernaryProfileC →
    TernaryProfileA × TernaryProfileC) : Prop :=
  ∃ (σ : TernaryProfileA ≃ TernaryProfileA)
    (s : TernaryProfileA → TernaryProfileC),
    σ 0 = 0 ∧ s 0 = 0 ∧ Function.Bijective f ∧
      ∀ a z, f (a, z) = (σ a, z + s a)

private abbrev PlaneDomain (n : ℕ) := Fin n → ZMod 3
private abbrev PlaneCodomain := Fin 2 → ZMod 3

/-- The mixed-second-difference span E_x over the ternary plane. -/
def claim_31440 (n : ℕ)
    (f : PlaneDomain n → PlaneCodomain)
    (E : PlaneDomain n → Submodule (ZMod 3) PlaneCodomain) : Prop :=
  f 0 = 0 ∧
    ∀ x : PlaneDomain n,
      E x = Submodule.span (ZMod 3)
        (Set.range (fun ac : PlaneDomain n × PlaneDomain n =>
          f (x + ac.1 + ac.2) - f (x + ac.1) - f (ac.1 + ac.2) + f ac.2))

private abbrev TranslationOmega (H : Type*) := (ZMod 3 × ZMod 3) × H

/-- A zero-top triangular chart has unchanged top coordinate. -/
def claim_39343 {H : Type*} [Fintype H] [AddCommGroup H]
    (_elementaryThree : ∀ h : H, 3 • h = 0)
    (q : TranslationOmega H ≃ TranslationOmega H) : Prop :=
  ∃ (m : H → ZMod 3) (g : H ≃ H),
    ∀ z w h, q ((z, w), h) = ((z, w + m h), g h)

private abbrev CayleyGroup := (Fin 3 → ZMod 2) × ZMod 9

private def cayleyUniverse : Finset CayleyGroup := Finset.univ.erase 0

private def inverseClosed (S : Finset CayleyGroup) : Prop :=
  ∀ x ∈ S, -x ∈ S

private def validConnectionSet (v : ℕ) (S : Finset CayleyGroup) : Prop :=
  S ⊆ cayleyUniverse ∧ inverseClosed S ∧ S.card = v

private def cayleyGraphIso (S T : Finset CayleyGroup)
    (f : CayleyGroup ≃ CayleyGroup) : Prop :=
  ∀ x y, (x - y ∈ S ↔ f x - f y ∈ T)

private def cayleyCI (S : Finset CayleyGroup) : Prop :=
  ∀ T : Finset CayleyGroup,
    T ⊆ cayleyUniverse →
    inverseClosed T →
    (∃ f : CayleyGroup ≃ CayleyGroup, cayleyGraphIso S T f) →
    ∃ α : CayleyGroup ≃+ CayleyGroup,
      ∀ x, x ∈ S ↔ α x ∈ T

/-- The exact valency-18 inverse-closed subset census. -/
def claim_37366 : Prop := by
  classical
  exact Fintype.card {S : Finset CayleyGroup // validConnectionSet 18 S} = 373081404

/-- Every valency-18 Cayley connection set is CI. -/
def claim_37370 : Prop :=
  ∀ S : Finset CayleyGroup,
    validConnectionSet 18 S → cayleyCI S

/-- Complementation on the 71 nonidentity elements preserves CI and exchanges 18 and 53. -/
def claim_37371 : Prop :=
  (∀ S : Finset CayleyGroup,
    validConnectionSet 18 S →
      validConnectionSet 53 (cayleyUniverse \ S) ∧
      (cayleyCI S ↔ cayleyCI (cayleyUniverse \ S))) ∧
  (∀ T : Finset CayleyGroup,
    validConnectionSet 53 T →
      ∃ S : Finset CayleyGroup,
        validConnectionSet 18 S ∧ T = cayleyUniverse \ S) ∧
  (∀ T : Finset CayleyGroup,
    validConnectionSet 53 T → cayleyCI T)

private def displacementSubgroup (q : (Fin 2 → ZMod 3) ≃ (Fin 2 → ZMod 3)) :
    AddSubgroup (Fin 2 → ZMod 3) :=
  AddSubgroup.closure (Set.range (fun t => t - q t + q 0))

/-- The displacement subgroup is full exactly when it is all of C₃², and proper otherwise. -/
def claim_31999
    (q : (Fin 2 → ZMod 3) ≃ (Fin 2 → ZMod 3))
    (W : AddSubgroup (Fin 2 → ZMod 3)) : Prop :=
  W = displacementSubgroup q ∧ (W = ⊤ ∨ W ≠ ⊤)

/-- Duplicate admitted locator for the individual displacement subgroup definition. -/
def claim_41769
    (q : (Fin 2 → ZMod 3) ≃ (Fin 2 → ZMod 3))
    (W : AddSubgroup (Fin 2 → ZMod 3)) : Prop :=
  W = displacementSubgroup q ∧ (W = ⊤ ∨ W ≠ ⊤)

private abbrev OrbitOmega := Fin 3 × ZMod 7

private def sectionSet (i : Fin 3) : Set OrbitOmega := {x | x.1 = i}

private def sectionTranslation (a : Fin 3 → ZMod 7) : OrbitOmega → OrbitOmega :=
  fun x => (x.1, x.2 + a x.1)

private def generatedFunctionSet (p : OrbitOmega → OrbitOmega) :
    Set (OrbitOmega → OrbitOmega) :=
  {q | ∃ n : ℕ, q = p^[n]}

private def functionOrbit (p : OrbitOmega → OrbitOmega) (x : OrbitOmega) : Set OrbitOmega :=
  Set.range (fun n : ℕ => (p^[n]) x)

/-- The diagonal and twisted order-seven translations have equal section orbits but differ as subgroups. -/
def claim_40202 : Prop :=
  let diagonal : Fin 3 → ZMod 7 := fun _ => 1
  let twisted : Fin 3 → ZMod 7 :=
    fun i => if i = 0 then 1 else if i = 1 then 2 else 3
  let p := sectionTranslation diagonal
  let q := sectionTranslation twisted
  Function.Bijective p ∧ Function.Bijective q ∧
    p^[7] = id ∧ q^[7] = id ∧ p ≠ id ∧ q ≠ id ∧
    generatedFunctionSet p ≠ generatedFunctionSet q ∧
    (∀ (i : Fin 3) (x : ZMod 7),
      functionOrbit p (i, x) = sectionSet i ∧
      functionOrbit q (i, x) = sectionSet i)

private def orbital {α : Type*} (G : Subgroup (Equiv α α))
    (p : α × α) : Set (α × α) :=
  {q | ∃ g : G, ((g : Equiv α α) p.1, (g : Equiv α α) p.2) = q}

private def twoClosure {α : Type*} (G : Subgroup (Equiv α α)) :
    Set (Equiv α α) :=
  {f | ∀ p : α × α, orbital G (f p.1, f p.2) = orbital G p}

/-- Finer H-orbitals imply the inclusion of 2-closures H² ≤ X². -/
def claim_40284 : Prop :=
  ∀ {α : Type*} (H X : Subgroup (Equiv α α)),
    H ≤ X →
    ∀ f : Equiv α α, f ∈ twoClosure H → f ∈ twoClosure X

end MathlibPlus.Open.ResearchFormalizationBatch
