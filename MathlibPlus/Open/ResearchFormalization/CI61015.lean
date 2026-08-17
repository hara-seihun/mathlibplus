import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CI61015

noncomputable section

/-- The cyclic group `C_r`, represented by the multiplicative wrapper on
`ZMod r`. -/
abbrev cyclicGroup (r : ℕ) := Multiplicative (ZMod r)

/-- The inversion automorphism of a cyclic group. -/
def inversionAutomorphism (r : ℕ) : MulAut (cyclicGroup r) :=
  AddEquiv.toMultiplicative (AddEquiv.neg (ZMod r))

/-- An exact action of `C_m` on `C_k` whose displayed generator acts by
inversion.  For `m=2` and `m=4` this is the action in `E(C_k,m)`. -/
structure InversionAction (k m : ℕ) where
  action : cyclicGroup m →* MulAut (cyclicGroup k)
  generatorActsByInversion :
    action (Multiplicative.ofAdd (1 : ZMod m)) = inversionAutomorphism k

/-- The semidirect product `E(C_k,m)=C_k ⋊ C_m` for an exact inversion
action. -/
abbrev semidirectGroup (k m : ℕ) (a : InversionAction k m) :=
  SemidirectProduct (cyclicGroup k) (cyclicGroup m) a.action

/-- Finiteness of an explicitly presented carrier, without hiding it in a
classical typeclass instance. -/
def finiteCarrier (G : Type*) : Prop :=
  ∃ r : ℕ, Nonempty (G ≃ Fin r)

/-- A directed binary Cayley relation determined by its connection set. -/
def directedBinaryCayleyRelation {G : Type*} [Group G]
    (S : Set G) (x y : G) : Prop :=
  x⁻¹ * y ∈ S

/-- A ternary Cayley relation determined by its two relative coordinates. -/
def ternaryCayleyRelation {G : Type*} [Group G]
    (S : Set (G × G)) (x y z : G) : Prop :=
  (x⁻¹ * y, x⁻¹ * z) ∈ S

/-- CI for every finite labelled tuple of ternary Cayley relations. -/
def ternaryRelationalCI (G : Type*) [Group G] : Prop :=
  ∀ r : ℕ, ∀ R T : Fin r → Set (G × G),
    ∀ e : Equiv.Perm G,
      (∀ i x y z,
        ternaryCayleyRelation (R i) x y z ↔
          ternaryCayleyRelation (T i) (e x) (e y) (e z)) →
        ∃ α : G ≃* G,
          ∀ i a b, (a, b) ∈ R i ↔ (α a, α b) ∈ T i

/-- CI for every finite labelled tuple of directed binary Cayley relations. -/
def directedBinaryRelationalCI (G : Type*) [Group G] : Prop :=
  ∀ r : ℕ, ∀ R T : Fin r → Set G,
    ∀ e : Equiv.Perm G,
      (∀ i x y,
        directedBinaryCayleyRelation (R i) x y ↔
          directedBinaryCayleyRelation (T i) (e x) (e y)) →
        ∃ α : G ≃* G,
          ∀ i a, a ∈ R i ↔ α a ∈ T i

/-- The ordinary undirected Cayley adjacency and its graph isomorphism
condition, with arbitrary target connection sets. -/
def undirectedCayleyRelation {G : Type*} [Group G]
    (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ x⁻¹ * y ∈ S

def inverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ ⦃s : G⦄, s ∈ S → s⁻¹ ∈ S

def ordinaryUndirectedCayleyIsomorphism {G : Type*} [Group G]
    (S T : Set G) (e : Equiv.Perm G) : Prop :=
  ∀ x y,
    undirectedCayleyRelation S x y ↔
      undirectedCayleyRelation T (e x) (e y)

/-- Ordinary undirected CI against arbitrary Cayley targets. -/
def ordinaryUndirectedCI (G : Type*) [Group G] : Prop :=
  ∀ S T : Set G,
    (1 : G) ∉ S →
      (1 : G) ∉ T →
        inverseClosed S →
          inverseClosed T →
            ∀ e : Equiv.Perm G,
              ordinaryUndirectedCayleyIsomorphism S T e →
                ∃ α : G ≃* G, ∀ a, a ∈ S ↔ α a ∈ T

/-- The finite versions of the three CI predicates used by the theorem. -/
def finiteTernaryRelationalCI (G : Type*) [Group G] : Prop :=
  finiteCarrier G ∧ ternaryRelationalCI G

def finiteDirectedBinaryRelationalCI (G : Type*) [Group G] : Prop :=
  finiteCarrier G ∧ directedBinaryRelationalCI G

def finiteOrdinaryUndirectedCI (G : Type*) [Group G] : Prop :=
  finiteCarrier G ∧ ordinaryUndirectedCI G

/-- Claim 61015: the coprime odd cyclic signed-shell products in the order-two
and order-four inversion chambers have the stated relational and ordinary CI
properties, including the `k=5` dihedral specialization. -/
def claim61015 : Prop :=
  (∀ (h k : ℕ),
    0 < h →
      0 < k →
        Nat.Coprime h k →
          Odd h →
            Odd k →
              Nat.gcd (h * k) (Nat.totient (h * k)) = 1 →
                Nonempty (InversionAction k 2) ∧
                  (∀ a2 : InversionAction k 2,
                    let G2 := cyclicGroup h × semidirectGroup k 2 a2
                    finiteTernaryRelationalCI G2 ∧
                      finiteDirectedBinaryRelationalCI G2 ∧
                        finiteOrdinaryUndirectedCI G2) ∧
                Nonempty (InversionAction k 4) ∧
                  (∀ a4 : InversionAction k 4,
                    ¬ 3 ∣ k →
                    let G4 := cyclicGroup h × semidirectGroup k 4 a4
                    finiteDirectedBinaryRelationalCI G4 ∧
                      finiteOrdinaryUndirectedCI G4)) ∧
  (∀ h : ℕ,
    0 < h →
      Odd h →
        ¬ 5 ∣ h →
          Nat.gcd (5 * h) (Nat.totient (5 * h)) = 1 →
            finiteOrdinaryUndirectedCI
              (cyclicGroup h × DihedralGroup 5))

end

end MathlibPlus.Open.ResearchFormalization.CI61015
