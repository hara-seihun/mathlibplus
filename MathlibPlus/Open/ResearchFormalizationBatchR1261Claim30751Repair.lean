import Mathlib

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatchR1261Claim30751

abbrev ProjectivePoint (K : Type*) [Field K] (d : ℕ) :=
  ℙ K (Fin d → K)

/-- The semilinear projective elements used for the full `PΓL` carrier. -/
def semilinearProjectiveElement {K : Type*} [Field K] [Fintype K]
    (d : ℕ) (p : Equiv.Perm (ProjectivePoint K d)) : Prop :=
  ∃ (σ : K ≃+* K) (f : (Fin d → K) ≃ (Fin d → K))
    (hf : ∀ v : Fin d → K, v ≠ 0 → f v ≠ 0),
    f 0 = 0 ∧
      (∀ v w : Fin d → K, f (v + w) = f v + f w) ∧
        (∀ (c : K) (v : Fin d → K),
          f (c • v) = σ c • f v) ∧
          (∀ (v : Fin d → K) (hv : v ≠ 0),
            p (Projectivization.mk K v hv) =
              Projectivization.mk K (f v) (hf v hv))

/-- The full semilinear projective permutation carrier. -/
def pGammaLGroup (K : Type*) [Field K] [Fintype K] (d : ℕ) :
    Subgroup (Equiv.Perm (ProjectivePoint K d)) :=
  Subgroup.closure
    {p : Equiv.Perm (ProjectivePoint K d) |
      semilinearProjectiveElement d p}

/-- A Singer torus is used as a subgroup of the full projective carrier, not
as a subgroup of the simple socle. -/
def fullSingerData {K : Type*} [Field K] [Fintype K]
    (d m : ℕ) (U : Subgroup (pGammaLGroup K d))
    (u₀ : U) : Prop :=
  1 < m ∧
    Odd m ∧
      ¬Nat.Prime m ∧
        Squarefree m ∧
          Nat.Coprime m 6 ∧
            m = (Nat.card K ^ d - 1) / (Nat.card K - 1) ∧
              Nat.card U = m ∧
                IsCyclic U ∧
                  (∀ u : U, u ∈ Subgroup.zpowers u₀) ∧
                    (∀ x y : ProjectivePoint K d,
                      ∃! u : U,
                        ((u : pGammaLGroup K d) :
                          Equiv.Perm (ProjectivePoint K d)) x = y) ∧
                      Subgroup.centralizer
                          (U : Set (pGammaLGroup K d)) = U

/-- The three common support-stabilizer shapes. -/
def supportStabilizerShape (D : Type*) [Group D] [Fintype D] : Prop :=
  Nonempty (D ≃* Multiplicative (ZMod 1)) ∨
    Nonempty (D ≃* Multiplicative (ZMod 4)) ∨
      Nonempty (D ≃* QuaternionGroup 3)

/-- The intrinsic parity action on the full torus. -/
def parityElement {A : Type*} [Group A]
    (χd : Multiplicative (ZMod 2)) (u : A) : A :=
  if Multiplicative.toAdd χd = 0 then u else u⁻¹

def paritySign (χd : Multiplicative (ZMod 2)) (m : ℕ) : ZMod m :=
  if Multiplicative.toAdd χd = 0 then 1 else -1

/-- The degree-one cocycle law in `ZMod m(χ)`. -/
def parityTwistedCocycle {D : Type*} [Group D]
    (χ : D →* Multiplicative (ZMod 2)) (m : ℕ)
    (τ : D → ZMod m) : Prop :=
  ∀ d e : D,
    τ (d * e) = τ d + paritySign (χ d) m * τ e

/-- The actual source/target support-action carrier.  The maps `sourceLift`
and `targetLift` are the two support lifts in the same local projective
permutation group; `transporter` records their relation after the selected
quotient transporter.  The equations identify `α` and `β` with the induced
conjugation actions on the simple factor, rather than leaving them as
unrelated homomorphisms into an automorphism group. -/
def supportActionTransporterData {K : Type*} [Field K] [Fintype K]
    {d : ℕ} {D : Type*} [Group D]
    (T₀ L U : Subgroup (pGammaLGroup K d))
    (χ : D →* Multiplicative (ZMod 2))
    (α β : D →* MulAut T₀)
    (sourceLift targetLift : D →* L) : Prop :=
  T₀ ≤ L ∧
    U ≤ L ∧
      IsSimpleGroup T₀ ∧
        (∀ δ : D, ∀ x : T₀,
          ((α δ) x : pGammaLGroup K d) =
            (sourceLift δ : pGammaLGroup K d) * (x : pGammaLGroup K d) *
              (sourceLift δ : pGammaLGroup K d)⁻¹) ∧
          (∀ δ : D, ∀ x : T₀,
            ((β δ) x : pGammaLGroup K d) =
              (targetLift δ : pGammaLGroup K d) * (x : pGammaLGroup K d) *
                (targetLift δ : pGammaLGroup K d)⁻¹) ∧
            (∃ q : L, ∀ δ : D,
              (targetLift δ : pGammaLGroup K d) =
                (q : pGammaLGroup K d)⁻¹ *
                  (sourceLift δ : pGammaLGroup K d) *
                    (q : pGammaLGroup K d)) ∧
              (∀ δ : D, ∀ u : U,
                (sourceLift δ : pGammaLGroup K d) *
                    (u : pGammaLGroup K d) *
                      (sourceLift δ : pGammaLGroup K d)⁻¹ =
                  parityElement (χ δ) (u : pGammaLGroup K d)) ∧
                (∀ δ : D, ∀ u : U,
                  (targetLift δ : pGammaLGroup K d) *
                      (u : pGammaLGroup K d) *
                        (targetLift δ : pGammaLGroup K d)⁻¹ =
                    parityElement (χ δ) (u : pGammaLGroup K d))

/-- The torus element corresponding to a residue exponent. -/
def torusPower {K : Type*} [Field K] [Fintype K]
    {d m : ℕ} (u₀ : Subgroup (pGammaLGroup K d))
    (a : ZMod m) (generator : u₀) : pGammaLGroup K d :=
  (generator : pGammaLGroup K d) ^ a.val

/-- Claim 30751: in the actual common support-action/transporter setting,
the source and target actions agree on the full Singer torus through the
intrinsic parity character, and their difference is a parity-twisted torus
one-cocycle acting by inner conjugation on every element of the simple
factor. -/
def claim30751 : Prop :=
  ∀ (K : Type*) [Field K] [Fintype K] (d m : ℕ)
    (D : Type*) [Group D] [Fintype D]
    (T₀ L U : Subgroup (pGammaLGroup K d))
    (u₀ : U) (χ : D →* Multiplicative (ZMod 2))
    (α β : D →* MulAut T₀)
    (sourceLift targetLift : D →* L),
    fullSingerData d m U u₀ →
      supportStabilizerShape D →
        supportActionTransporterData
            T₀ L U χ α β sourceLift targetLift →
          ∃ τ : D → ZMod m,
            parityTwistedCocycle χ m τ ∧
              ∀ δ : D, ∀ x : T₀,
                ((β δ) x : pGammaLGroup K d) =
                  torusPower U (τ δ) u₀ *
                    ((α δ) x : pGammaLGroup K d) *
                      (torusPower U (τ δ) u₀)⁻¹

end MathlibPlus.Open.ResearchFormalizationBatchR1261Claim30751
