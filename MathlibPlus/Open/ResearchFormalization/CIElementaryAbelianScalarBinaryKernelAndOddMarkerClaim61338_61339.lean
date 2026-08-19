import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CIElementaryAbelianScalarBinaryKernelAndOddMarker

universe u v

/-- A connection set contains no identity element in an additive carrier. -/
def identityFree {G : Type*} [Zero G] (S : Set G) : Prop :=
  (0 : G) ∉ S

/-- An additive connection set is closed under taking inverses. -/
def inverseClosed {G : Type*} [Neg G] (S : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ S → -x ∈ S

/-- Ordinary simple undirected Cayley adjacency on an additive group. -/
def ordinaryCayleyAdjacency {G : Type*} [AddGroup G]
    (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- Directed Cayley adjacency on an additive group. -/
def directedCayleyAdjacency {G : Type*} [AddGroup G]
    (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- A bijective isomorphism of two ordinary additive Cayley graphs. -/
def ordinaryCayleyGraphIsomorphism {G H : Type*}
    [AddGroup G] [AddGroup H]
    (S : Set G) (T : Set H) (q : G → H) : Prop :=
  Function.Bijective q ∧
    ∀ x y,
      ordinaryCayleyAdjacency S x y ↔
        ordinaryCayleyAdjacency T (q x) (q y)

/-- A bijective isomorphism of two directed additive Cayley graphs. -/
def directedCayleyGraphIsomorphism {G H : Type*}
    [AddGroup G] [AddGroup H]
    (S : Set G) (T : Set H) (q : G → H) : Prop :=
  Function.Bijective q ∧
    ∀ x y,
      directedCayleyAdjacency S x y ↔
        directedCayleyAdjacency T (q x) (q y)

/-- A pointed directed Cayley-graph isomorphism. -/
def pointedDirectedCayleyGraphIsomorphism {G : Type*} [AddGroup G]
    (S T : Set G) (q : G → G) : Prop :=
  q 0 = 0 ∧ directedCayleyGraphIsomorphism S T q

/-- The binary closure condition for a set of functions. -/
def binaryClosedFunctionSet {F H : Type*}
    (M : Set (H → F)) : Prop :=
  M = {g : H → F |
    ∀ x y : H, ∃ f : H → F,
      f ∈ M ∧ f x = g x ∧ f y = g y}

/-- Every constant function belongs to a function set. -/
def containsAllConstants {F H : Type*} (M : Set (H → F)) : Prop :=
  ∀ c : F, (fun _ : H => c) ∈ M

/-- Translation invariance for a function set on an additive group. -/
def translationInvariantFunctionSet {F H : Type*} [Add H]
    (M : Set (H → F)) : Prop :=
  ∀ f : H → F, f ∈ M → ∀ h : H,
    (fun x : H => f (x + h)) ∈ M

/-- The common period set of a function set. -/
def commonPeriodSet {F H : Type*} [Add H]
    (M : Set (H → F)) : Set H :=
  {h : H |
    ∀ f : H → F, f ∈ M → ∀ x : H, f (x + h) = f x}

/-- Functions constant on the additive cosets of an additive subgroup. -/
def constantOnAddSubgroupCosets {F H : Type*} [AddGroup H]
    (P : AddSubgroup H) : Set (H → F) :=
  {g : H → F |
    ∀ x : H, ∀ h : H, h ∈ P → g (x + h) = g x}

/-- A set of functions is an F-linear function space. -/
def isLinearFunctionSpace {F H : Type*} [Field F]
    (M : Set (H → F)) : Prop :=
  ∃ U : Submodule F (H → F), (U : Set (H → F)) = M

/-- The scalar binary-kernel theorem in its general field/additive-group form. -/
def scalarBinaryKernelClassification : Prop :=
  ∀ (F H : Type*) [Field F] [AddCommGroup H]
    (M : Submodule F (H → F)),
    containsAllConstants (M : Set (H → F)) →
      translationInvariantFunctionSet (M : Set (H → F)) →
        binaryClosedFunctionSet (M : Set (H → F)) →
          ∃ P : AddSubgroup H,
            (P : Set H) = commonPeriodSet (M : Set (H → F)) ∧
              (M : Set (H → F)) = constantOnAddSubgroupCosets P

/-- The translations in the first coordinate of `F_p × H`. -/
def firstCoordinateTranslations (p : ℕ) [Fact p.Prime]
    {H : Type*} [AddCommGroup H] :
    Set (Equiv.Perm (ZMod p × H)) :=
  {δ : Equiv.Perm (ZMod p × H) |
    ∃ a : ZMod p, ∀ d : ZMod p, ∀ x : H,
      δ (d, x) = (d + a, x)}

/-- The centralizer of a set in a permutation group. -/
def permutationCentralizer {α : Type*} [Group α]
    (D : Set α) : Set α :=
  {σ : α | ∀ δ : α, δ ∈ D → σ * δ = δ * σ}

/-- The automorphism set of an ordinary additive Cayley graph. -/
def ordinaryCayleyAutomorphisms {G : Type*} [AddGroup G]
    (S : Set G) : Set (Equiv.Perm G) :=
  {σ : Equiv.Perm G |
    ∀ x y : G,
      ordinaryCayleyAdjacency S x y ↔
        ordinaryCayleyAdjacency S (σ x) (σ y)}

/-- The set `A ∩ C_Sym(V)(D)` used by the scalar central-line argument. -/
def scalarCayleyCentralizerImage (p : ℕ) [Fact p.Prime]
    {H : Type*} [AddCommGroup H]
    (S : Set (ZMod p × H)) : Set (Equiv.Perm (ZMod p × H)) :=
  ordinaryCayleyAutomorphisms S ∩
    permutationCentralizer (firstCoordinateTranslations (p := p) (H := H))

/-- Membership of the first-coordinate shear associated with a function. -/
def scalarShearMember (p : ℕ) [Fact p.Prime]
    {H : Type*} [AddCommGroup H]
    (Y : Set (Equiv.Perm (ZMod p × H))) (f : H → ZMod p) : Prop :=
  ∃ σ : Equiv.Perm (ZMod p × H),
    (∀ d : ZMod p, ∀ x : H,
      σ (d, x) = (d + f x, x)) ∧ σ ∈ Y

/-- The function set induced by the centralizer image. -/
def scalarCayleyFunctionSet (p : ℕ) [Fact p.Prime]
    {H : Type*} [AddCommGroup H]
    (S : Set (ZMod p × H)) : Set (H → ZMod p) :=
  {f : H → ZMod p |
    scalarShearMember p (scalarCayleyCentralizerImage p S) f}

/-- The full translation group of an additive carrier lies in a permutation set. -/
def containsAllAdditiveTranslations {G : Type*} [AddGroup G]
    (Y : Set (Equiv.Perm G)) : Prop :=
  ∀ w : G, ∃ σ : Equiv.Perm G,
    (∀ v : G, σ v = v + w) ∧ σ ∈ Y

/-- The first-coordinate section of a connection set. -/
def scalarSection (S : Set (ZMod p × H)) (h : H) : Set (ZMod p) :=
  {d : ZMod p | (d, h) ∈ S}

/-- The Cayley-section saturation consequence of the scalar binary-kernel theorem. -/
def scalarCayleySectionSaturation : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (H : Type*) [AddCommGroup H]
    (S : Set (ZMod p × H)),
    identityFree S → inverseClosed S →
      let Y := scalarCayleyCentralizerImage p S
      let M_Y := scalarCayleyFunctionSet p S
      containsAllAdditiveTranslations Y ∧
        isLinearFunctionSpace M_Y ∧
          translationInvariantFunctionSet M_Y ∧
            containsAllConstants M_Y ∧
              binaryClosedFunctionSet M_Y ∧
                ∃ P : AddSubgroup H,
                  (P : Set H) = commonPeriodSet M_Y ∧
                    M_Y = constantOnAddSubgroupCosets P ∧
                      (∀ h : H, h ∉ P →
                        scalarSection S h = (∅ : Set (ZMod p)) ∨
                          scalarSection S h = (Set.univ : Set (ZMod p)))

/-- Claim 61338: scalar binary-kernel classification together with its
Cayley-section saturation consequence. -/
def claim61338 : Prop :=
  scalarBinaryKernelClassification.{u, v} ∧ scalarCayleySectionSaturation.{u}

/-- The marked one-coordinate connection set used in the odd-prime transfer. -/
def markedConnectionSet (p : ℕ) [Fact p.Prime]
    {H : Type*} [AddCommGroup H]
    (A : Set H) : Set (ZMod p × H) :=
  {v : ZMod p × H |
    (v.1 = 0 ∧ v.2 ≠ 0) ∨
      (v.1 = 1 ∧ v.2 ∈ A) ∨
        (v.1 = -1 ∧ -v.2 ∈ A) ∨
          ((v.1 = 2 ∨ v.1 = -2) ∧ v.2 = 0)}

/-- The coordinate map `Q(t,h) = (t,q(h))`. -/
def markedCoordinateMap (p : ℕ) [Fact p.Prime]
    {H : Type*} [AddCommGroup H]
    (q : H → H) : ZMod p × H → ZMod p × H :=
  fun v => (v.1, q v.2)

/-- Linear transport of two connection sets over the prime field. -/
def linearConnectionTransport (p : ℕ) [Fact p.Prime]
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Module (ZMod p) G] [Module (ZMod p) H]
    (S : Set G) (T : Set H) : Prop :=
  ∃ e : G ≃ₗ[ZMod p] H, Set.image e S = T

/-- The marked transfer theorem for a pointed directed defect. -/
def markedOddPrimeTransfer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    5 ≤ p →
      ∀ (n : ℕ), 2 ≤ n →
        let H := Fin n → ZMod p
        ∀ A B : Set H,
          identityFree A → identityFree B →
            ∀ q : H → H,
              pointedDirectedCayleyGraphIsomorphism A B q →
                ¬ linearConnectionTransport p A B →
                  let V := ZMod p × H
                  let Ahat : Set V := markedConnectionSet p A
                  let Bhat : Set V := markedConnectionSet p B
                  let Q := markedCoordinateMap p q
                  (identityFree Ahat ∧ inverseClosed Ahat) ∧
                    (identityFree Bhat ∧ inverseClosed Bhat) ∧
                      ordinaryCayleyGraphIsomorphism Ahat Bhat Q ∧
                        ¬ linearConnectionTransport p Ahat Bhat

/-- Directed CI for the coordinate model of an elementary abelian group. -/
def elementaryDirectedCI (p n : ℕ) [Fact p.Prime] : Prop :=
  ∀ A B : Set (Fin n → ZMod p),
    identityFree A → identityFree B →
      ∀ q : (Fin n → ZMod p) → (Fin n → ZMod p),
        directedCayleyGraphIsomorphism A B q →
          ∃ e : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p),
            Set.image e A = B

/-- Ordinary undirected CI for a finite elementary-abelian coordinate model. -/
def elementaryOrdinaryUndirectedCI (p n : ℕ) [Fact p.Prime] : Prop :=
  ∀ A B : Set (Fin n → ZMod p),
    identityFree A → inverseClosed A →
      identityFree B → inverseClosed B →
        ∀ q : (Fin n → ZMod p) → (Fin n → ZMod p),
          ordinaryCayleyGraphIsomorphism A B q →
            ∃ e : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p),
              Set.image e A = B

/-- Ordinary undirected CI for an arbitrary finite vector-space carrier over
`F_p`, used for the direct-sum carrier in the transfer. -/
def linearOrdinaryUndirectedCI (p : ℕ) [Fact p.Prime]
    (G : Type*) [AddCommGroup G] [Module (ZMod p) G] [Finite G] : Prop :=
  ∀ A B : Set G,
    identityFree A → inverseClosed A →
      identityFree B → inverseClosed B →
        ∀ q : G → G,
          ordinaryCayleyGraphIsomorphism A B q →
            ∃ e : G ≃ₗ[ZMod p] G,
              Set.image e A = B

/-- Claim 61339: the explicit odd-prime marker transfer and its CI/DCI
consequence. -/
def claim61339 : Prop :=
  markedOddPrimeTransfer ∧
    (∀ (p : ℕ) [Fact p.Prime],
      5 ≤ p →
        ∀ n : ℕ, 2 ≤ n →
          ¬ elementaryDirectedCI p n →
            ¬ linearOrdinaryUndirectedCI p
              (ZMod p × (Fin n → ZMod p)))

end MathlibPlus.Open.ResearchFormalization.CIElementaryAbelianScalarBinaryKernelAndOddMarker
