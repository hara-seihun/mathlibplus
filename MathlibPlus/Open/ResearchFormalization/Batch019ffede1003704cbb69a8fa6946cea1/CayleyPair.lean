import MathlibPlus.Open.ResearchFormalization.Batch019ffede1003704cbb69a8fa6946cea1.BitShear

namespace MathlibPlus.Open.ResearchFormalization.Batch019ffede1003704cbb69a8fa6946cea1

noncomputable section

/-- The standard dihedral carrier for the presentation `D_{8k}`. -/
abbrev DihedralFamily (k : ℕ) := DihedralGroup (4 * k)

/-- The displayed rotation generator `r`. -/
def familyRotation (k : ℕ) : DihedralFamily k :=
  DihedralGroup.r 1

/-- The displayed reflection generator `s`. -/
def familyReflection (k : ℕ) : DihedralFamily k :=
  DihedralGroup.sr 0

/-- The central half-turn `c = r^(2k)`. -/
def familyHalfTurn (k : ℕ) : DihedralFamily k :=
  familyRotation k ^ (2 * k)

/-- The exact connection set `S_k` from Claim 24081. -/
def familyConnectionS (k : ℕ) : Finset (DihedralFamily k) :=
  {familyRotation k, (familyRotation k)⁻¹, familyHalfTurn k,
    familyReflection k, familyRotation k * familyReflection k,
    familyRotation k ^ 2 * familyReflection k,
    familyRotation k ^ (2 * k + 1) * familyReflection k}

/-- The exact connection set `T_k` from Claim 24081. -/
def familyConnectionT (k : ℕ) : Finset (DihedralFamily k) :=
  {familyRotation k ^ k, (familyRotation k ^ k)⁻¹, familyHalfTurn k,
    familyReflection k, familyRotation k * familyReflection k,
    familyHalfTurn k * familyReflection k,
    familyRotation k ^ (2 * k + 1) * familyReflection k}

/-- Boolean membership tests for the rotation/reflection summands. -/
def familyIsRotation {k : ℕ} (x : DihedralFamily k) : Bool :=
  match x with
  | DihedralGroup.r _ => true
  | DihedralGroup.sr _ => false

def familyIsReflection {k : ℕ} (x : DihedralFamily k) : Bool :=
  match x with
  | DihedralGroup.r _ => false
  | DihedralGroup.sr _ => true

def familyRotationCount {k : ℕ} (S : Finset (DihedralFamily k)) : ℕ :=
  (S.filter (fun x => familyIsRotation x = true)).card

def familyReflectionCount {k : ℕ} (S : Finset (DihedralFamily k)) : ℕ :=
  (S.filter (fun x => familyIsReflection x = true)).card

/-- The rotation/reflection stratum of a finite connection set. -/
def familyStratum {k : ℕ} (S : Finset (DihedralFamily k)) : ℕ × ℕ :=
  (familyRotationCount S, familyReflectionCount S)

def sameFamilyStratum {k : ℕ}
    (S T : Finset (DihedralFamily k)) : Prop :=
  familyStratum S = familyStratum T

/-- Inverse-closure of a finite dihedral connection set. -/
def familyInverseClosed {k : ℕ} (S : Finset (DihedralFamily k)) : Prop :=
  ∀ x, x ∈ S → x⁻¹ ∈ S

/-- Generation by a finite connection set in the displayed group. -/
def familyGenerates {k : ℕ} (S : Finset (DihedralFamily k)) : Prop :=
  Subgroup.closure (S : Set (DihedralFamily k)) = ⊤

/-- The undirected Cayley graph for the displayed left-connection convention. -/
def familyCayleyGraph {G : Type*} [Group G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun u v => ∃ x ∈ S, x * v = u)

def familyCayleyConnected {k : ℕ}
    (S : Finset (DihedralFamily k)) : Prop :=
  (familyCayleyGraph (S : Set (DihedralFamily k))).Connected

/-- Claim 24081: the two displayed seven-element sets are inverse-closed,
generating, connected, and in the same three-rotation/four-reflection stratum. -/
def claim_24081 : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    familyInverseClosed (familyConnectionS k) ∧
      familyInverseClosed (familyConnectionT k) ∧
      (familyConnectionS k).card = 7 ∧
      (familyConnectionT k).card = 7 ∧
      familyRotationCount (familyConnectionS k) = 3 ∧
      familyReflectionCount (familyConnectionS k) = 4 ∧
      familyRotationCount (familyConnectionT k) = 3 ∧
      familyReflectionCount (familyConnectionT k) = 4 ∧
      familyGenerates (familyConnectionS k) ∧
      familyGenerates (familyConnectionT k) ∧
      familyCayleyConnected (familyConnectionS k) ∧
      familyCayleyConnected (familyConnectionT k) ∧
      sameFamilyStratum (familyConnectionS k) (familyConnectionT k)

/-- Convert a group element `r^m` or `r^m s` to the target coordinates used by
Claim 24082.  Mathlib's reflection constructor is `s r^j`, hence its target
rotation coordinate is `-j`. -/
def familyTargetCoordinates (k : ℕ) :
    DihedralFamily k → BitShearTarget k
  | DihedralGroup.r m => (m, false)
  | DihedralGroup.sr m => (-m, true)

/-- The inverse coordinate conversion. -/
def familyOfTargetCoordinates (k : ℕ) :
    BitShearTarget k → DihedralFamily k
  | (m, false) => DihedralGroup.r m
  | (m, true) => DihedralGroup.sr (-m)

/-- The unique parity decomposition of a target rotation coordinate into
`2q+p`, with `q` reduced modulo `2k`. -/
def familySourceCoordinates (k : ℕ) (z : BitShearTarget k) : BitShearSource k :=
  let p : Bool := z.1.val % 2 == 1
  let qNat : ℕ := (z.1.val - (if p then 1 else 0)) / 2
  let q : ZMod (2 * k) := qNat
  (q, p, z.2)

/-- The source-coordinate form of a group element. -/
def familySourceOfGroup (k : ℕ) (g : DihedralFamily k) : BitShearSource k :=
  familySourceCoordinates k (familyTargetCoordinates k g)

/-- The explicit map `Phi_k` in Claims 24082--24084. -/
def familyPhi (k : ℕ) : DihedralFamily k → DihedralFamily k :=
  fun g =>
    familyOfTargetCoordinates k
      (bitShear k (familySourceOfGroup k g))

/-- The exact edge-derivative identity of Claim 24083. -/
def claim_24083 : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∀ g : DihedralFamily k,
      {y : DihedralFamily k |
          ∃ x ∈ (familyConnectionS k : Set (DihedralFamily k)),
            y = familyPhi k (x * g) * (familyPhi k g)⁻¹} =
        (familyConnectionT k : Set (DihedralFamily k))

/-- A concrete graph-isomorphism predicate for the displayed Cayley graphs. -/
def familyGraphIsomorphism {G : Type*} [Group G]
    (S T : Set G) (f : G → G) : Prop :=
  Function.Bijective f ∧
    ∀ u v, (familyCayleyGraph S).Adj u v ↔
      (familyCayleyGraph T).Adj (f u) (f v)

/-- Claim 24084: `Phi_k` is the explicit graph isomorphism between the two
ordinary undirected Cayley graphs. -/
def claim_24084 : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    familyGraphIsomorphism
      (familyConnectionS k : Set (DihedralFamily k))
      (familyConnectionT k : Set (DihedralFamily k))
      (familyPhi k)

/-- The rotation subgroup in the displayed dihedral presentation. -/
def familyRotationSubgroup (k : ℕ) : Subgroup (DihedralFamily k) :=
  Subgroup.closure ({familyRotation k} : Set (DihedralFamily k))

/-- Claim 24085: automorphisms preserve the rotation subgroup and element
orders, the two displayed noncentral rotation parts have the stated orders,
and no group automorphism sends `S_k` to `T_k`. -/
def claim_24085 : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    (∀ α : MulAut (DihedralFamily k), ∀ x,
      x ∈ familyRotationSubgroup k ↔
        α x ∈ familyRotationSubgroup k) ∧
      (∀ α : MulAut (DihedralFamily k), ∀ x,
        orderOf (α x) = orderOf x) ∧
      (∀ x, x ∈ familyConnectionS k →
        x ∈ familyRotationSubgroup k →
        x ∉ Subgroup.center (DihedralFamily k) →
        orderOf x = 4 * k) ∧
      (∀ x, x ∈ familyConnectionT k →
        x ∈ familyRotationSubgroup k →
        x ∉ Subgroup.center (DihedralFamily k) →
        orderOf x = 4) ∧
      ¬ ∃ α : MulAut (DihedralFamily k),
        ∀ x, x ∈ familyConnectionS k ↔
          α x ∈ familyConnectionT k

end

end MathlibPlus.Open.ResearchFormalization.Batch019ffede1003704cbb69a8fa6946cea1
