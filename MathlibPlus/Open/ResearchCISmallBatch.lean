import Mathlib

namespace MathlibPlus.Open

/-!
The common graph predicates below spell out the ordinary undirected right-Cayley
adjacency relation and its abstract graph isomorphism relation.  They avoid
requiring a proof that an arbitrary relation is a `SimpleGraph`; the claims
supply identity-freeness and inverse-closure as their hypotheses (or
conclusions), exactly as in the admitted statements.
-/

def identityFreeMul {G : Type*} [MulOneClass G] (S : Set G) : Prop :=
  (1 : G) ∉ S

def inverseClosedMul {G : Type*} [Inv G] (S : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ S → x⁻¹ ∈ S

def rightCayleyAdjacentMul {G : Type*} [Group G] (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ x⁻¹ * y ∈ S

def rightCayleyGraphIsoMul {G : Type*} [Group G] (S T : Set G) : Prop :=
  ∃ e : G ≃ G, ∀ x y : G,
    rightCayleyAdjacentMul S x y ↔ rightCayleyAdjacentMul T (e x) (e y)

def identityFreeAdd {G : Type*} [Zero G] (S : Set G) : Prop :=
  (0 : G) ∉ S

def inverseClosedAdd {G : Type*} [Neg G] (S : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ S → -x ∈ S

def negSet {G : Type*} [AddGroup G] (S : Set G) : Set G :=
  (fun x : G => -x) '' S

def rightCayleyAdjacentAdd {G : Type*} [AddGroup G] (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ -x + y ∈ S

def rightCayleyGraphIsoAdd {G : Type*} [AddGroup G] (S T : Set G) : Prop :=
  ∃ e : G ≃ G, ∀ x y : G,
    rightCayleyAdjacentAdd S x y ↔ rightCayleyAdjacentAdd T (e x) (e y)

/-- The dicyclic/generalised quaternion group of order twelve, with the
presentation `⟨a,b | a^6 = 1, b^2 = a^3, b⁻¹ab = a⁻¹⟩`. -/
abbrev Q12 := QuaternionGroup 3

abbrev C7TimesQ12 := Multiplicative (ZMod 7) × Q12

/-- Claim 60171: `C₇ × Q₁₂` is undirected CI in valency six. -/
def claim60171 : Prop :=
  ∀ S T : Set C7TimesQ12,
    identityFreeMul S ∧ inverseClosedMul S ∧
      identityFreeMul T ∧ inverseClosedMul T ∧
      S.ncard = 6 ∧ T.ncard = 6 →
    rightCayleyGraphIsoMul S T →
      ∃ α : C7TimesQ12 ≃* C7TimesQ12, α '' S = T

abbrev F3Cube := Fin 3 → ZMod 3
abbrev G60172 := ZMod 4 × F3Cube

/-- Claim 60172: valency or covalency twelve on `(Z/4Z) × F₃³` is CI. -/
def claim60172 : Prop :=
  ∀ S T : Set G60172,
    S ⊆ (Set.univ : Set G60172) \ ({0} : Set G60172) ∧
      T ⊆ (Set.univ : Set G60172) \ ({0} : Set G60172) ∧
      S = negSet S ∧ T = negSet T ∧
      min S.ncard (107 - S.ncard) = 12 ∧
      min T.ncard (107 - T.ncard) = 12 →
    rightCayleyGraphIsoAdd S T →
      ∃ α : G60172 ≃+ G60172, α '' S = T

abbrev C2Pow (r : ℕ) := Fin r → ZMod 2
abbrev G60174 (r : ℕ) := C2Pow r × ZMod 9

/-- Claim 60174: the stated subgroup-complement shells in `C₂ʳ × C₉`
are undirected CI connection sets. -/
def claim60174 : Prop :=
  ∀ r : ℕ, ∀ K H : AddSubgroup (G60174 r), K < H →
    let S : Set (G60174 r) :=
      (Set.univ \ ({0} : Set (G60174 r))) \
        ((H : Set (G60174 r)) \ (K : Set (G60174 r)))
    identityFreeAdd S ∧ inverseClosedAdd S ∧
      ∀ T : Set (G60174 r),
        identityFreeAdd T → inverseClosedAdd T →
          rightCayleyGraphIsoAdd S T →
            ∃ α : G60174 r ≃+ G60174 r, α '' S = T

end MathlibPlus.Open
