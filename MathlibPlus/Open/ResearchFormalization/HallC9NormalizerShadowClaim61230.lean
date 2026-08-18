import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.HallC9NormalizerShadowClaim61230

noncomputable section

abbrev C9 := ZMod 9

abbrev HallProduct (V : Type*) := V × C9

private def inverseClosed {A : Type*} [AddGroup A]
    (S : Set A) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

private def identityFree {A : Type*} [AddGroup A]
    (S : Set A) : Prop :=
  (0 : A) ∉ S

private def additiveCayleyAdj {A : Type*} [AddGroup A]
    (S : Set A) (x y : A) : Prop :=
  y - x ∈ S

private def pointedCayleyGraphIso {A : Type*} [AddGroup A]
    (S T : Set A) (f : A ≃ A) : Prop :=
  f 0 = 0 ∧
    ∀ x y, additiveCayleyAdj S x y ↔
      additiveCayleyAdj T (f x) (f y)

private def symmetricBinaryRelationalCI
    (V : Type*) [Fintype V] [AddCommGroup V] : Prop :=
  ∀ (κ : Type) [Fintype κ] (S T : κ → Set V),
    (∀ i, inverseClosed (S i) ∧ inverseClosed (T i)) →
      ∀ f : V ≃ V,
        (∀ i x y,
          y - x ∈ S i ↔ f y - f x ∈ T i) →
          ∃ L : V ≃+ V, ∀ i,
            Set.image (fun x => L x) (S i) = T i

private def elementaryAbelianTwo
    (V : Type*) [AddCommGroup V] : Prop :=
  ∀ x : V, x + x = 0

private def hallMap {V : Type*} [AddCommGroup V]
    (β : V ≃ V) (u : C9ˣ) (c : V → C9) :
    HallProduct V → HallProduct V :=
  fun p => (β p.1, (u : C9) * p.2 + c p.1)

private noncomputable def unitAddEquiv (u : C9ˣ) : C9 ≃+ C9 :=
  AddEquiv.ofBijective (AddMonoidHom.mulLeft (u : C9))
    (Units.mulLeft_bijective u)

private noncomputable def alphaEquiv {V : Type*} [AddCommGroup V]
    (L : V ≃+ V) (u : C9ˣ) : HallProduct V ≃+ HallProduct V :=
  AddEquiv.prodCongr L (unitAddEquiv u)

private def hallForm {V : Type*} [AddCommGroup V]
    (β : V ≃ V) (u : C9ˣ) (c : V → C9)
    (f : HallProduct V ≃ HallProduct V) : Prop :=
  ∀ p, f p = hallMap β u c p

private abbrev binaryCube (r : ℕ) := Fin r → ZMod 2

private def hallNormalizerConclusion
    (V : Type*) [Fintype V] [AddCommGroup V] : Prop :=
  ∀ (S T : Set (HallProduct V)),
    identityFree S ∧ identityFree T →
      inverseClosed S ∧ inverseClosed T →
        ∀ (β : V ≃ V) (u : C9ˣ) (c : V → C9)
          (f : HallProduct V ≃ HallProduct V),
          β 0 = 0 → c 0 = 0 →
            hallForm β u c f →
              pointedCayleyGraphIso S T f →
                ∃ L : V ≃+ V,
                  Set.image (alphaEquiv L u) S = T

/-- Claim 61230: a pointed Hall-`C₉`-normalizing Cayley isomorphism has a
    group-automorphism shadow with the same cyclic unit and no fibre carries. -/
def hallC9NormalizerShadow_claim61230 : Prop :=
  (∀ (V : Type*) [Fintype V] [AddCommGroup V],
      elementaryAbelianTwo V →
        symmetricBinaryRelationalCI V →
          hallNormalizerConclusion V) ∧
    (∀ (V : Type*) [Fintype V] [AddCommGroup V],
      symmetricBinaryRelationalCI (V × ZMod 3) →
        symmetricBinaryRelationalCI V) ∧
      (∀ r : ℕ,
        r = 3 ∨ r = 4 ∨ r = 5 →
          symmetricBinaryRelationalCI (binaryCube r × ZMod 3))

end

end MathlibPlus.Open.ResearchFormalization.HallC9NormalizerShadowClaim61230
