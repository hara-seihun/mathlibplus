import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Claim 27603: the displacement span attached to a permutation of an
    elementary abelian two-group. -/
def predecessorDisplacementSpan
    (V : Type*) [Fintype V] [AddCommGroup V]
    (hV : ∀ v : V, v + v = 0) (ψ : Equiv.Perm V) : AddSubgroup V :=
  AddSubgroup.closure (Set.range fun u : V => u + ψ u + ψ 0)

/-- The fibre-preserving map used in claim 27604. -/
def fibreMap
    (V B : Type*) [Fintype V] [AddCommGroup V]
    (hV : ∀ v : V, v + v = 0) [Group B]
    (φ : B → Equiv.Perm V) : V × B → V × B :=
  fun p => (φ p.2 p.1, p.2)

/-- Claim 27604: the relative derivative on the fixed fibre, written with
    the displayed data from the admitted statement. -/
def relativeDerivativeOnOneFibre
    (V B : Type*) [Fintype V] [AddCommGroup V]
    (hV : ∀ v : V, v + v = 0) [Group B]
    (φ : B → Equiv.Perm V) (hφ : φ 1 = 1)
    (b a : B) (u : V) : V → V :=
  fun v => (φ b)⁻¹ (φ (b * a) (v + u) + φ a u)

/-- Claim 27605: the inverse-predecessor derivatives and their generated
    conjugated translations, expressed as one open proposition. -/
def inversePredecessorDerivativesYieldConjugatedTranslations
    (V B : Type*) [Fintype V] [AddCommGroup V]
    (hV : ∀ v : V, v + v = 0) [Group B]
    (φ : B → Equiv.Perm V) (hφ : φ 1 = 1) (b : B) : Prop :=
  let p := φ b
  let q := φ b⁻¹
  let τ : V → Equiv.Perm V := fun w => Equiv.addRight w
  let R : V → Equiv.Perm V :=
    fun u => p⁻¹ * Equiv.addRight (q u) * φ 1 * Equiv.addRight u
  let W := predecessorDisplacementSpan V hV q
  let C : V → Equiv.Perm V := fun w => p⁻¹ * τ w * p
  (∀ u, R u = p⁻¹ * τ (u + q u)) ∧
    (∀ u, R u * (R 0)⁻¹ = p⁻¹ * τ (u + q u + q 0) * p) ∧
    (∀ w, w ∈ W →
      C w ∈ Subgroup.closure (Set.range fun u => R u * (R 0)⁻¹))

/-- One generator from the first family in claim 28644. -/
def crossDerivativeFirstGenerator
    (B : Type*) [AddGroup B] (q r : Equiv.Perm B) (t : B) : Equiv.Perm B :=
  Equiv.addRight (-(q t)) * r * Equiv.addRight t

/-- One generator from the second family in claim 28644. -/
def crossDerivativeSecondGenerator
    (B : Type*) [AddGroup B] (q r : Equiv.Perm B) (t : B) : Equiv.Perm B :=
  Equiv.addRight (-(r t)) * q * Equiv.addRight t

/-- The subgroup X(q,r) in claim 28644. -/
def crossDerivativeAction
    (B : Type*) [AddGroup B] (q r : Equiv.Perm B) :
    Subgroup (Equiv.Perm B) :=
  Subgroup.closure
    (Set.range (crossDerivativeFirstGenerator B q r) ∪
      Set.range (crossDerivativeSecondGenerator B q r))

/-- The subgroup Γ(q,r;L) in claim 28644. -/
def translatedCollisionAction
    (B : Type*) [AddGroup B] (q r : Equiv.Perm B) (L : AddSubgroup B) :
    Subgroup (Equiv.Perm B) :=
  Subgroup.closure
    ((crossDerivativeAction B q r : Set (Equiv.Perm B)) ∪
      Set.range (fun ell : L => Equiv.addRight (ell : B)))

end MathlibPlus.Open.ResearchFormalization
