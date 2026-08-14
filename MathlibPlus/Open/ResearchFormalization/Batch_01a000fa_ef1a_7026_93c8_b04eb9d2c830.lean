import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch01

/-- The Boolean cube used by the fixed-global-level witness. -/
abbrev RademacherCube (n : ℕ) :=
  {x : Fin n → ℤ // ∀ i, x i = (-1 : ℤ) ∨ x i = (1 : ℤ)}

/-- The first fixed-level tree in R-3044.1. -/
def r3044T1 (x : RademacherCube 4) : ℤ :=
  if x.1 (1 : Fin 4) = (-1 : ℤ) then x.1 (2 : Fin 4) else -x.1 (3 : Fin 4)

/-- The second fixed-level tree in R-3044.1. -/
def r3044T2 (x : RademacherCube 4) : ℤ :=
  if x.1 (0 : Fin 4) = (1 : ℤ) then x.1 (2 : Fin 4) else -x.1 (3 : Fin 4)

/-- The exact positive mixture asserted in R-3044.1. -/
def r3044F (x : RademacherCube 4) : ℚ :=
  ((2 : ℚ) / 5) * (r3044T1 x : ℚ) + ((3 : ℚ) / 5) * (r3044T2 x : ℚ)

/-- R-3044.1, with the coordinates fixed globally as in the packet. -/
def r3044_1 : Prop :=
  ∃ (T₁ T₂ : RademacherCube 4 → ℤ) (F : RademacherCube 4 → ℚ),
    (∀ x, T₁ x = r3044T1 x) ∧
    (∀ x, T₂ x = r3044T2 x) ∧
    (∀ x, F x = ((2 : ℚ) / 5) * (T₁ x : ℚ) + ((3 : ℚ) / 5) * (T₂ x : ℚ))

/-- The composite predicate in the residual parameter set of R-3035. -/
def r3035Composite (n : ℕ) : Prop :=
  ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = n

/-- Membership in the exact residual parameter set 𝓝 from R-3035.1. -/
def r3035ResidualParameter (n : ℕ) : Prop :=
  r3035Composite n ∧
    n % 2 = 1 ∧
    n ≠ 15 ∧
    n ≠ 21 ∧
    (∀ p : ℕ, Nat.Prime p → ¬p ^ 2 ∣ n) ∧
    (3 ∣ n ∨ Nat.gcd n (Nat.totient n) > 1) ∧
    (∀ p : ℕ, Nat.Prime p → n ≠ 3 * p)

/-- The group and coefficient carriers in R-3046. -/
abbrev r3046H (m : ℕ) := Fin m → ZMod 3
abbrev r3046D (d : ℕ) := Fin d → ZMod 3
abbrev r3046Module (m d : ℕ) (L : AddSubgroup (r3046H m)) :=
  (r3046H m ⧸ L) → r3046D d

/-- Translation on the coinduced function module, using the packet's quotient convention. -/
noncomputable def r3046Translate (m d : ℕ) (L : AddSubgroup (r3046H m))
    (h : r3046H m) (f : r3046Module m d L) : r3046Module m d L :=
  Quotient.lift (fun x : r3046H m => f (QuotientAddGroup.mk (x - h))) (by
    intro a b hab
    have habq : QuotientAddGroup.mk (a : r3046H m) = QuotientAddGroup.mk b :=
      Quotient.sound hab
    apply congrArg f
    rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_sub]
    exact congrArg (fun q => q - QuotientAddGroup.mk h) habq)

/-- Constant functions used for the residual global shear. -/
def r3046Constant (m d : ℕ) (L : AddSubgroup (r3046H m))
    (u : r3046D d) : r3046Module m d L :=
  fun _ => u

/-- The additive cocycle identity for the action in (1). -/
def r3046Cocycle (m d : ℕ) (L : AddSubgroup (r3046H m))
    (c : r3046H m → r3046Module m d L) : Prop :=
  ∀ h k, c (h + k) = c h + r3046Translate m d L h (c k)

/-- R-3046.1, stated on representatives of the quotient. -/
def r3046_1 : Prop :=
  ∀ (m d : ℕ) (L : AddSubgroup (r3046H m))
    (h : r3046H m) (f : r3046Module m d L) (x : r3046H m),
    r3046Translate m d L h f (QuotientAddGroup.mk x) =
      f (QuotientAddGroup.mk (x - h))

/-- R-3046.2, the cocycle splitting into a coboundary and a constant linear character. -/
def r3046_2 : Prop :=
  ∀ (m d : ℕ) (L : AddSubgroup (r3046H m))
    (c : r3046H m → r3046Module m d L),
    r3046Cocycle m d L c →
      ∃ f : r3046Module m d L,
        ∃ χ : r3046H m →ₗ[ZMod 3] r3046D d,
          ∀ h,
            c h = r3046Translate m d L h f - f + r3046Constant m d L (χ h)

abbrev r3046DirectCoeff (ι : Type) (d : ι → ℕ) :=
  (i : ι) → r3046D (d i)
abbrev r3046DirectModule (m : ℕ) (ι : Type) (d : ι → ℕ)
    (L : ι → AddSubgroup (r3046H m)) :=
  (i : ι) → r3046Module m (d i) (L i)

noncomputable def r3046DirectTranslate (m : ℕ) (ι : Type) (d : ι → ℕ)
    (L : ι → AddSubgroup (r3046H m)) (h : r3046H m)
    (f : r3046DirectModule m ι d L) : r3046DirectModule m ι d L :=
  fun i => r3046Translate m (d i) (L i) h (f i)

def r3046DirectConstant (m : ℕ) (ι : Type) (d : ι → ℕ)
    (L : ι → AddSubgroup (r3046H m)) (u : r3046DirectCoeff ι d) :
    r3046DirectModule m ι d L :=
  fun i => r3046Constant m (d i) (L i) (u i)

def r3046DirectCocycle (m : ℕ) (ι : Type) (d : ι → ℕ)
    (L : ι → AddSubgroup (r3046H m))
    (c : r3046H m → r3046DirectModule m ι d L) : Prop :=
  ∀ h k, c (h + k) = c h + r3046DirectTranslate m ι d L h (c k)

/-- R-3046.3, componentwise splitting for every finite direct sum. -/
def r3046_3 : Prop :=
  ∀ (m : ℕ) (ι : Type) (_finite : Fintype ι) (d : ι → ℕ)
    (L : ι → AddSubgroup (r3046H m))
    (c : r3046H m → r3046DirectModule m ι d L),
    r3046DirectCocycle m ι d L c →
      ∃ f : r3046DirectModule m ι d L,
        ∃ χ : r3046H m →ₗ[ZMod 3] r3046DirectCoeff ι d,
          ∀ h,
            c h = r3046DirectTranslate m ι d L h f - f +
              r3046DirectConstant m ι d L (χ h)

/-- R-3046.4, including the explicit restriction, fibre translation, and residual shear. -/
def r3046_4 : Prop :=
  ∀ (m d : ℕ) (L : AddSubgroup (r3046H m))
    (c : r3046H m → r3046Module m d L),
    r3046Cocycle m d L c →
      ∃ χ : r3046H m →ₗ[ZMod 3] r3046D d,
        (∀ ℓ, ℓ ∈ L → χ ℓ = c ℓ (QuotientAddGroup.mk (0 : r3046H m))) ∧
        let c₀ : r3046H m → r3046Module m d L :=
          fun h => c h - r3046Constant m d L (χ h)
        (∀ ℓ, ℓ ∈ L → c₀ ℓ = 0) ∧
          ∃ f : r3046Module m d L,
            (∀ x,
              f (QuotientAddGroup.mk x) =
                c₀ (-x) (QuotientAddGroup.mk (0 : r3046H m))) ∧
            (∀ h x,
              f (QuotientAddGroup.mk (x - h)) -
                  f (QuotientAddGroup.mk x) = c₀ h (QuotientAddGroup.mk x)) ∧
            (∀ h,
              c h = r3046Translate m d L h f - f +
                r3046Constant m d L (χ h))

abbrev r3047V := Fin 3 → Fin 2 → ZMod 2

def r3047CoordinateProjection (i : Fin 3) :
    r3047V →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  { toFun := fun x => x i
    map_add' := by intro x y; rfl
    map_smul' := by intro a x; rfl }

def r3047PairProjection (i j : Fin 3) :
    r3047V →ₗ[ZMod 2] ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) :=
  (r3047CoordinateProjection i).prod (r3047CoordinateProjection j)

def r3047Subdirect (U : Submodule (ZMod 2) r3047V) : Prop :=
  ∀ (i : Fin 3) (v : Fin 2 → ZMod 2),
    ∃ x : U, (x : r3047V) i = v

def r3047CoordinatePermutation (σ : Equiv.Perm (Fin 3)) :
    r3047V →ₗ[ZMod 2] r3047V :=
  { toFun := fun x i => x (σ.symm i)
    map_add' := by intro x y; funext i; rfl
    map_smul' := by intro a x; funext i; rfl }

def r3047S3Invariant (U : Submodule (ZMod 2) r3047V) : Prop :=
  ∀ σ : Equiv.Perm (Fin 3), U.map (r3047CoordinatePermutation σ) = U

def r3047DiagonalGLAction
    (g : (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)) :
    r3047V →ₗ[ZMod 2] r3047V :=
  { toFun := fun x i => g (x i)
    map_add' := by intro x y; funext i; exact g.map_add _ _
    map_smul' := by intro a x; funext i; exact g.map_smul a (x i) }

def r3047DiagonalGLInvariant (U : Submodule (ZMod 2) r3047V) : Prop :=
  ∀ g : (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2),
    U.map (r3047DiagonalGLAction g) = U

def r3047Irreducible (U : Submodule (ZMod 2) r3047V) : Prop :=
  r3047S3Invariant U ∧ r3047DiagonalGLInvariant U ∧
    ∀ W : Submodule (ZMod 2) r3047V, W ≤ U →
      (r3047S3Invariant W ∧ r3047DiagonalGLInvariant W) →
        W = ⊥ ∨ W = U

noncomputable def r3047PairProjectionSize
    (U : Submodule (ZMod 2) r3047V) (i j : Fin 3) : ℕ :=
  letI := Fintype.ofFinite U
  (Finset.univ.image (fun x : U => r3047PairProjection i j x)).card

def r3047DiagonalGraph (U : Submodule (ZMod 2) r3047V) : Prop :=
  ∀ x : r3047V, x ∈ U ↔
    (x (0 : Fin 3) = x (1 : Fin 3) ∧ x (1 : Fin 3) = x (2 : Fin 3))

def r3047PairwiseFull (U : Submodule (ZMod 2) r3047V) : Prop :=
  r3047PairProjectionSize U (0 : Fin 3) (1 : Fin 3) = 16 ∧
  r3047PairProjectionSize U (0 : Fin 3) (2 : Fin 3) = 16 ∧
  r3047PairProjectionSize U (1 : Fin 3) (2 : Fin 3) = 16

/-- R-3047, Records 1--3: the finite subdirect-module stress-test counts and types. -/
noncomputable def r3047_1 : Prop :=
  letI : Fintype {U : Submodule (ZMod 2) r3047V // r3047Subdirect U} :=
    Fintype.ofFinite _
  letI : Fintype {U : Submodule (ZMod 2) r3047V //
      r3047Subdirect U ∧ r3047S3Invariant U} :=
    Fintype.ofFinite _
  letI : Fintype {U : Submodule (ZMod 2) r3047V //
      r3047Subdirect U ∧ r3047Irreducible U} :=
    Fintype.ofFinite _
  Fintype.card (Submodule (ZMod 2) r3047V) = 2825 ∧
  Fintype.card {U : Submodule (ZMod 2) r3047V // r3047Subdirect U} = 928 ∧
  Fintype.card {U : Submodule (ZMod 2) r3047V //
      r3047Subdirect U ∧ r3047S3Invariant U} = 15 ∧
  Fintype.card {U : Submodule (ZMod 2) r3047V //
      r3047Subdirect U ∧ r3047Irreducible U} = 2 ∧
  ∃ Udiag Upair : Submodule (ZMod 2) r3047V,
    r3047Subdirect Udiag ∧ r3047Subdirect Upair ∧
    r3047Irreducible Udiag ∧ r3047Irreducible Upair ∧
    Udiag ≠ Upair ∧
    r3047DiagonalGraph Udiag ∧
    r3047PairwiseFull Upair ∧
    Module.finrank (ZMod 2) Udiag = 2 ∧
    Module.finrank (ZMod 2) Upair = 4 ∧
    r3047PairProjectionSize Udiag (0 : Fin 3) (1 : Fin 3) = 4 ∧
    r3047PairProjectionSize Udiag (0 : Fin 3) (2 : Fin 3) = 4 ∧
    r3047PairProjectionSize Udiag (1 : Fin 3) (2 : Fin 3) = 4 ∧
    r3047PairProjectionSize Upair (0 : Fin 3) (1 : Fin 3) = 16 ∧
    r3047PairProjectionSize Upair (0 : Fin 3) (2 : Fin 3) = 16 ∧
    r3047PairProjectionSize Upair (1 : Fin 3) (2 : Fin 3) = 16 ∧
    ∀ U : Submodule (ZMod 2) r3047V,
      r3047Subdirect U ∧ r3047Irreducible U → U = Udiag ∨ U = Upair

abbrev r3035Q4n (n : ℕ) := ZMod n × ZMod 4

def r3035QMul (n : ℕ) (a b : r3035Q4n n) : r3035Q4n n :=
  (a.1 + ((-1 : ZMod n) ^ a.2.val) * b.1, a.2 + b.2)

def r3035QInv (n : ℕ) (a : r3035Q4n n) : r3035Q4n n :=
  (-(((-1 : ZMod n) ^ a.2.val) * a.1), -a.2)

def r3035QIdentity (n : ℕ) : r3035Q4n n := (0, 0)
def r3035QCentralInvolution (n : ℕ) : r3035Q4n n := (0, 2)

def r3035ConnectionSet (n : ℕ) (S : Set (r3035Q4n n)) : Prop :=
  r3035QIdentity n ∉ S ∧ ∀ s, s ∈ S ↔ r3035QInv n s ∈ S

def r3035CayleyRelation (n : ℕ) (S : Set (r3035Q4n n))
    (a b : r3035Q4n n) : Prop :=
  r3035QMul n (r3035QInv n a) b ∈ S

/-- R-3035.2: the displayed generalized-quaternion presentation and its
identity-free inverse-closed ordinary Cayley-graph scope. -/
def r3035_2 : Prop :=
  ∀ n, n % 2 = 1 →
    (∀ a b c,
        r3035QMul n (r3035QMul n a b) c =
          r3035QMul n a (r3035QMul n b c)) ∧
    (∀ a,
        r3035QMul n (r3035QIdentity n) a = a ∧
          r3035QMul n a (r3035QIdentity n) = a) ∧
    (∀ a,
        r3035QMul n (r3035QInv n a) a = r3035QIdentity n ∧
          r3035QMul n a (r3035QInv n a) = r3035QIdentity n) ∧
    (r3035QMul n (r3035QCentralInvolution n)
        (r3035QCentralInvolution n) = r3035QIdentity n) ∧
    (∀ a,
        r3035QMul n (r3035QCentralInvolution n) a =
            r3035QMul n a (r3035QCentralInvolution n)) ∧
    (∀ S, r3035ConnectionSet n S →
      ∀ a b, r3035CayleyRelation n S a b ↔
        r3035CayleyRelation n S b a)

end MathlibPlus.Open.ResearchFormalization.Batch01
