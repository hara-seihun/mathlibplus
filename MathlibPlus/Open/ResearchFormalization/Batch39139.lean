import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch39139

noncomputable section

abbrev F2 := ZMod 2
abbrev V5 := Fin 5 → F2

noncomputable instance : Fintype V5 := Fintype.ofFinite _
noncomputable instance : Fintype (Equiv.Perm V5) := Fintype.ofFinite _
noncomputable instance : Fintype (Subgroup (Equiv.Perm V5)) := Fintype.ofFinite _

/-- A permutation of the literal affine space is affine-linear. -/
def IsAffinePermutation (g : Equiv.Perm V5) : Prop :=
  ∃ A : V5 ≃ₗ[F2] V5, ∃ b : V5, ∀ x, g x = A x + b

/-- The literal regular elementary-abelian subgroups in the packet. -/
def IsLiteralRegularE32 (E : Subgroup (Equiv.Perm V5)) : Prop :=
  (∀ g, g ∈ E → IsAffinePermutation g) ∧
    Nat.card E = 32 ∧
    (∀ a b : E, a * b = b * a) ∧
    (∀ a : E, a * a = 1) ∧
    (∀ x y : V5, ∃! e : E, e.1 x = y)

abbrev LiteralE32 := {E : Subgroup (Equiv.Perm V5) // IsLiteralRegularE32 E}

noncomputable instance : Fintype LiteralE32 := Fintype.ofFinite _
noncomputable instance : Fintype (Sym2 LiteralE32) := Fintype.ofFinite _

def ConjugateSubgroup (g : Equiv.Perm V5)
    (E F : Subgroup (Equiv.Perm V5)) : Prop :=
  ∀ x, x ∈ F ↔ ∃ e, e ∈ E ∧ x = g * e * g⁻¹

abbrev UnorderedPair (α : Type*) := {s : Finset α // s.card = 2}

noncomputable instance : Fintype (UnorderedPair V5) := by
  classical
  exact Fintype.ofFinite _

def mapPair (g : Equiv.Perm V5) (p : UnorderedPair V5) : UnorderedPair V5 :=
  ⟨p.1.map g.toEmbedding, by simpa using p.2⟩

def orbital (H : Subgroup (Equiv.Perm V5)) (p : UnorderedPair V5) :
    Set (UnorderedPair V5) :=
  {q | ∃ h : Equiv.Perm V5, h ∈ H ∧ mapPair h p = q}

def OrbitalPreserverSet (H : Subgroup (Equiv.Perm V5)) :
    Set (Equiv.Perm V5) :=
  {g | ∀ p, mapPair g p ∈ orbital H p}

def unorderedOrbitalClosure (H : Subgroup (Equiv.Perm V5)) :
    Subgroup (Equiv.Perm V5) :=
  Subgroup.closure (OrbitalPreserverSet H)

def IsUndirectedOrbitalFusion (H : Subgroup (Equiv.Perm V5))
    (𝔉 : Set (Set (UnorderedPair V5))) : Prop :=
  (∀ p, ∃! R, R ∈ 𝔉 ∧ p ∈ R) ∧
    (∀ R, R ∈ 𝔉 → ∀ p, p ∈ R → orbital H p ⊆ R)

def FusionPreserverSet (𝔉 : Set (Set (UnorderedPair V5))) :
    Set (Equiv.Perm V5) :=
  {g | ∀ R, R ∈ 𝔉 → ∀ p, p ∈ R ↔ mapPair g p ∈ R}

def fusionAutomorphism (𝔉 : Set (Set (UnorderedPair V5))) :
    Subgroup (Equiv.Perm V5) :=
  Subgroup.closure (FusionPreserverSet 𝔉)

/-- The finest unordered orbital closure is exactly the setwise stabilizer of
all generated pair orbitals, and every coarser orbital fusion has a larger
automorphism group. -/
def claim39139 : Prop :=
  ∀ E F : Subgroup (Equiv.Perm V5),
    IsLiteralRegularE32 E → IsLiteralRegularE32 F →
      let H := Subgroup.closure ((E : Set (Equiv.Perm V5)) ∪ (F : Set (Equiv.Perm V5)))
      (∀ g, g ∈ unorderedOrbitalClosure H ↔ g ∈ OrbitalPreserverSet H) ∧
        (∀ 𝔉, IsUndirectedOrbitalFusion H 𝔉 →
          unorderedOrbitalClosure H ≤ fusionAutomorphism 𝔉)

def glOrbit (E : LiteralE32) : Finset LiteralE32 := by
  classical
  exact Finset.univ.filter (fun F => ∃ A : V5 ≃ₗ[F2] V5,
    ConjugateSubgroup A.toEquiv E.1 F.1)

def glOrbitSize (E : LiteralE32) : Nat := (glOrbit E).card

/-- The exact literal rank-five affine-subgroup census and its four
linear-conjugacy class sizes. -/
def claim39140 : Prop :=
  Fintype.card LiteralE32 = 8464 ∧
    (∀ E : LiteralE32,
      glOrbitSize E = 1 ∨ glOrbitSize E = 1085 ∨
        glOrbitSize E = 6510 ∨ glOrbitSize E = 868) ∧
    Fintype.card {E : LiteralE32 // glOrbitSize E = 1} = 1 ∧
    Fintype.card {E : LiteralE32 // glOrbitSize E = 1085} = 1085 ∧
    Fintype.card {E : LiteralE32 // glOrbitSize E = 6510} = 6510 ∧
    Fintype.card {E : LiteralE32 // glOrbitSize E = 868} = 868

def GLPairConjugate (p q : Sym2 LiteralE32) : Prop :=
  ∃ A : V5 ≃ₗ[F2] V5, ∃ E F E' F' : LiteralE32,
    p = Sym2.mk E F ∧ q = Sym2.mk E' F' ∧
      ((ConjugateSubgroup A.toEquiv E.1 E'.1 ∧
          ConjugateSubgroup A.toEquiv F.1 F'.1) ∨
        (ConjugateSubgroup A.toEquiv E.1 F'.1 ∧
          ConjugateSubgroup A.toEquiv F.1 E'.1))

def subgroupIntersection (E F : Subgroup (Equiv.Perm V5)) :
    Subgroup (Equiv.Perm V5) where
  carrier := fun g => g ∈ E ∧ g ∈ F
  one_mem' := ⟨E.one_mem, F.one_mem⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨E.mul_mem ha.1 hb.1, F.mul_mem ha.2 hb.2⟩
  inv_mem' := by
    intro a ha
    exact ⟨E.inv_mem ha.1, F.inv_mem ha.2⟩

def pairIntersectionCard : Sym2 LiteralE32 → Nat :=
  Sym2.lift ⟨(fun E F : LiteralE32 =>
    Nat.card (subgroupIntersection E.1 F.1)), by
    intro E F
    have h : subgroupIntersection E.1 F.1 = subgroupIntersection F.1 E.1 := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.2, hx.1⟩
      · intro hx
        exact ⟨hx.2, hx.1⟩
    change Nat.card (subgroupIntersection E.1 F.1) =
      Nat.card (subgroupIntersection F.1 E.1)
    rw [h]⟩

def IsPairOrbitRepresentativeSet (S : Finset (Sym2 LiteralE32)) : Prop :=
  ∀ p, ∃! r, r ∈ S ∧ GLPairConjugate p r

def generatedPairGroup (E F : LiteralE32) : Subgroup (Equiv.Perm V5) :=
  Subgroup.closure ((E.1 : Set (Equiv.Perm V5)) ∪ (F.1 : Set (Equiv.Perm V5)))

def IsOrbitalRepresentativeSet (H : Subgroup (Equiv.Perm V5))
    (T : Finset (UnorderedPair V5)) : Prop :=
  ∀ p, ∃! r, r ∈ T ∧ r ∈ orbital H p

def HasUnorderedOrbitalCount (p : Sym2 LiteralE32) (n : Nat) : Prop :=
  ∃ E F : LiteralE32, p = Sym2.mk E F ∧
    ∃ T : Finset (UnorderedPair V5), T.card = n ∧
      IsOrbitalRepresentativeSet (generatedPairGroup E F) T

/-- The exact unordered-pair orbit and intersection census. -/
def claim39141 : Prop := by
  classical
  exact
    (∃ S : Finset (Sym2 LiteralE32),
      S.card = 75 ∧ IsPairOrbitRepresentativeSet S ∧
        (S.filter (fun p => pairIntersectionCard p = 1)).card = 21 ∧
        (S.filter (fun p => pairIntersectionCard p = 2)).card = 28 ∧
        (S.filter (fun p => pairIntersectionCard p = 4)).card = 14 ∧
        (S.filter (fun p => pairIntersectionCard p = 8)).card = 8 ∧
        (S.filter (fun p => pairIntersectionCard p = 32)).card = 4) ∧
      Fintype.card {p : Sym2 LiteralE32 // pairIntersectionCard p = 1} = 24425520 ∧
      Fintype.card {p : Sym2 LiteralE32 // pairIntersectionCard p = 2} = 10313576 ∧
      Fintype.card {p : Sym2 LiteralE32 // pairIntersectionCard p = 4} = 950460 ∧
      Fintype.card {p : Sym2 LiteralE32 // pairIntersectionCard p = 8} = 125860 ∧
      Fintype.card {p : Sym2 LiteralE32 // pairIntersectionCard p = 32} = 8464

/-- The exact distribution of the numbers of unordered orbitals over the
seventy-five simultaneous linear pair orbits. -/
def claim39145 : Prop := by
  classical
  exact
    ∃ S : Finset (Sym2 LiteralE32),
      S.card = 75 ∧ IsPairOrbitRepresentativeSet S ∧
        (S.filter (fun p => HasUnorderedOrbitalCount p 2)).card = 3 ∧
        (S.filter (fun p => HasUnorderedOrbitalCount p 3)).card = 2 ∧
        (S.filter (fun p => HasUnorderedOrbitalCount p 4)).card = 7 ∧
        (S.filter (fun p => HasUnorderedOrbitalCount p 5)).card = 7 ∧
        (S.filter (fun p => HasUnorderedOrbitalCount p 6)).card = 9 ∧
        (S.filter (fun p => HasUnorderedOrbitalCount p 7)).card = 4 ∧
        (S.filter (fun p => HasUnorderedOrbitalCount p 8)).card = 4 ∧
        (S.filter (fun p => HasUnorderedOrbitalCount p 9)).card = 2 ∧
        (S.filter (fun p => HasUnorderedOrbitalCount p 10)).card = 8 ∧
        (S.filter (fun p => HasUnorderedOrbitalCount p 11)).card = 6 ∧
        (S.filter (fun p => HasUnorderedOrbitalCount p 13)).card = 7 ∧
        (S.filter (fun p => HasUnorderedOrbitalCount p 16)).card = 4 ∧
        (S.filter (fun p => HasUnorderedOrbitalCount p 19)).card = 8 ∧
        (S.filter (fun p => HasUnorderedOrbitalCount p 31)).card = 4

/-- Every literal regular affine pair is conjugate inside its unordered
orbital closure. -/
def claim39142 : Prop :=
  ∀ E F : Subgroup (Equiv.Perm V5),
    IsLiteralRegularE32 E → IsLiteralRegularE32 F →
      let H := Subgroup.closure ((E : Set (Equiv.Perm V5)) ∪ (F : Set (Equiv.Perm V5)))
      ∃ g, g ∈ unorderedOrbitalClosure H ∧ ConjugateSubgroup g E F

end
end MathlibPlus.Open.ResearchFormalization.Batch39139
