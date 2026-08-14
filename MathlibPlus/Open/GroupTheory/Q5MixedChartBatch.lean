import Mathlib

namespace MathlibPlus.Open.GroupTheory

private abbrev Q5Point := Fin 8 × ZMod 5
private abbrev Q5Local := Equiv.Perm (ZMod 5)

private noncomputable def q5Affine (f : Q5Local) : Prop :=
  ∃ a b : ZMod 5, a ≠ 0 ∧ ∀ x, f x = a * x + b

private noncomputable def q5Identity (f : Q5Local) : Prop := ∀ x, f x = x

private noncomputable def q5NonAffine (f : Q5Local) : Prop := ¬ q5Affine f

private noncomputable def q5LocalChart (σ τ₁ τ₂ : Q5Local) (i j : Fin 8) :
    Fin 8 → Q5Local := fun b =>
  if b = 0 then σ else if b = i then τ₁ else if b = j then τ₂ else Equiv.refl _

private noncomputable def q5Chart (σ τ₁ τ₂ : Q5Local) (i j : Fin 8) :
    Equiv.Perm Q5Point :=
  { toFun := fun x => (x.1, q5LocalChart σ τ₁ τ₂ i j x.1 x.2)
    invFun := fun x =>
      (x.1, (q5LocalChart σ τ₁ τ₂ i j x.1).symm x.2)
    left_inv := by
      intro x
      simp [q5LocalChart]
    right_inv := by
      intro x
      simp [q5LocalChart] }

private abbrev Q5Triple :=
  {t : Q5Local × Q5Local × Q5Local //
    q5Affine t.1 ∧ ¬ q5Identity t.1 ∧
    q5NonAffine t.2.1 ∧ q5NonAffine t.2.2 ∧ t.2.1 ≠ t.2.2}

private noncomputable def q5ConjugateTriple (t u : Q5Triple) : Prop :=
  ∃ g : Q5Local, q5Affine g ∧
    u.1.1 = g * t.1.1 * g⁻¹ ∧
    u.1.2.1 = g * t.1.2.1 * g⁻¹ ∧
    u.1.2.2 = g * t.1.2.2 * g⁻¹

private noncomputable def q5TripleOrbitSize (t : Q5Triple) : ℕ :=
  Nat.card {u : Q5Triple // q5ConjugateTriple t u}

private noncomputable def q5TripleRepresentatives : Prop :=
  ∃ reps : Finset Q5Triple,
    reps.card = 9414 ∧
    ∀ t : Q5Triple,
      ∃! u : Q5Triple, u ∈ reps ∧ q5ConjugateTriple t u

private noncomputable def q5Orbit {α : Type*} (X : Subgroup (Equiv.Perm α)) (x : α) : Set α :=
  {y | ∃ g : Equiv.Perm α, g ∈ X ∧ g x = y}

private noncomputable def q5PairMap (F : Equiv.Perm Q5Point) :
    Q5Point × Q5Point → Q5Point × Q5Point :=
  fun z => (F z.1, F z.2)

private noncomputable def q5PairOrbit (X : Subgroup (Equiv.Perm Q5Point))
    (z : Q5Point × Q5Point) : Set (Q5Point × Q5Point) :=
  {w | ∃ g : Equiv.Perm Q5Point, g ∈ X ∧
    (g z.1, g z.2) = w}

private noncomputable def q5OrbitalControl
    (X : Subgroup (Equiv.Perm Q5Point)) (F : Equiv.Perm Q5Point) : Prop :=
  (∃ reps : Finset (Q5Point × Q5Point),
    reps.card = 9 ∧
    ∀ z : Q5Point × Q5Point,
      ∃! r : Q5Point × Q5Point,
        r ∈ reps ∧ ∃ g : Equiv.Perm Q5Point, g ∈ X ∧
          (g z.1, g z.2) = r) ∧
  ∀ z : Q5Point × Q5Point,
    q5PairMap F '' q5PairOrbit X z = q5PairOrbit X z

private noncomputable def q5GeneratedGroup
    (R : Subgroup (Equiv.Perm Q5Point)) (F : Equiv.Perm Q5Point) :
    Subgroup (Equiv.Perm Q5Point) :=
  Subgroup.closure
    ((R : Set (Equiv.Perm Q5Point)) ∪
      {g | ∃ r : Equiv.Perm Q5Point, r ∈ R ∧ g = F * r * F⁻¹})

private noncomputable def q5TwoClosure
    (X : Subgroup (Equiv.Perm Q5Point)) (F : Equiv.Perm Q5Point) : Prop :=
  ∀ x y : Q5Point, ∃ g : Equiv.Perm Q5Point,
    g ∈ X ∧ g x = F x ∧ g y = F y

private noncomputable def q5BlockAction
    (R : Subgroup (Equiv.Perm Q5Point)) : Prop :=
  ∀ g : Equiv.Perm Q5Point, g ∈ R →
    ∃ π : Equiv.Perm (Fin 8), ∀ b : Fin 8, ∀ x : ZMod 5,
      (g (b, x)).1 = π b

private noncomputable def q5Regular
    (R : Subgroup (Equiv.Perm Q5Point)) : Prop :=
  ∀ x y : Q5Point, ∃! g : R, g.1 x = y

private noncomputable def q5EModel
    (R : Subgroup (Equiv.Perm Q5Point)) : Prop :=
  ∃ φ : Multiplicative (ZMod 8) →* MulAut (Multiplicative (ZMod 5)),
    (∀ a : Multiplicative (ZMod 5), φ (.ofAdd 1) a = a⁻¹) ∧
    Nonempty (R ≃* ((Multiplicative (ZMod 5)) ⋊[φ]
      (Multiplicative (ZMod 8))))

private noncomputable def q5RModel (R : Subgroup (Equiv.Perm Q5Point)) : Prop :=
  q5EModel R ∧ q5BlockAction R ∧ q5Regular R ∧ Nat.card R = 40

private noncomputable def q5Control
    (R : Subgroup (Equiv.Perm Q5Point)) (t : Q5Triple)
    (i j : Fin 8) : Prop :=
  let F := q5Chart t.1.1 t.1.2.1 t.1.2.2 i j
  let X := q5GeneratedGroup R F
  q5TwoClosure X F ∧ q5OrbitalControl X F

/-- The exact local-chart and ordered-normalizer counts are written on the
    concrete `ZMod 5` permutation carrier; the two nonaffine charts remain
    ordered. -/
def mixedQ5SupportThreeNormalization_claim33237 : Prop :=
  Nat.card {f : Q5Local // q5Affine f ∧ ¬ q5Identity f} = 19 ∧
  Nat.card {f : Q5Local // q5NonAffine f} = 100 ∧
  Nat.card Q5Triple = 188100 ∧
  Nat.card {q : Fin 8 × Fin 8 // 1 ≤ q.1 ∧ q.1 < q.2} = 21 ∧
  q5TripleRepresentatives ∧
  ∃ reps : Finset Q5Triple,
    reps.card = 9414 ∧
    (∀ t : Q5Triple,
      ∃! u : Q5Triple, u ∈ reps ∧ q5ConjugateTriple t u) ∧
    (∀ R : Subgroup (Equiv.Perm Q5Point), q5RModel R →
      ∀ t ∈ reps, ∀ q : Fin 8 × Fin 8,
        1 ≤ q.1 → q.1 < q.2 → q5Control R t q.1 q.2) ∧
    Nat.card {t : Q5Triple // t ∈ reps ∧ q5TripleOrbitSize t = 10} = 18 ∧
    Nat.card {t : Q5Triple // t ∈ reps ∧ q5TripleOrbitSize t = 20} = 9396

/-- Every normalized triple and every one of the 21 ordered position masks
    passes the exact nine-orbital control. -/
def mixedQ5SupportThreeExhaustiveControls_claim33239 : Prop :=
  ∀ R : Subgroup (Equiv.Perm Q5Point), q5RModel R →
    ∃ reps : Finset Q5Triple,
      reps.card = 9414 ∧
      (∀ t : Q5Triple,
        ∃! u : Q5Triple, u ∈ reps ∧ q5ConjugateTriple t u) ∧
      (∀ t ∈ reps, ∀ q : Fin 8 × Fin 8,
        1 ≤ q.1 → q.1 < q.2 → q5Control R t q.1 q.2) ∧
      9414 * 21 = (197694 : ℕ)

end MathlibPlus.Open.GroupTheory
