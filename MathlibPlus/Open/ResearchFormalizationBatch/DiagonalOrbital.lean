import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

/-- The local and quotient carriers in the diagonal model. -/
abbrev localSpace (d : ℕ) := Fin d → ZMod 2

abbrev quotientSpace (s : ℕ) := (Fin s → ZMod 2) × ZMod 9

abbrev diagonalSpace (d s : ℕ) := localSpace d × quotientSpace s

/-- Regularity together with exponent two is the elementary-abelian regular action
used by the diagonal-model claims. -/
def IsRegularElementaryAbelian {α : Type} [Fintype α]
    (E : Subgroup (Equiv.Perm α)) : Prop :=
  (∀ x y : α, ∃! e : E, e.1 x = y) ∧
    (∀ e : E, e.1 * e.1 = 1)

def generatedLocal {α : Type} [Fintype α]
    (E F : Subgroup (Equiv.Perm α)) : Subgroup (Equiv.Perm α) :=
  Subgroup.closure ((E : Set (Equiv.Perm α)) ∪ (F : Set (Equiv.Perm α)))

def orderedOrbital {α : Type} (K : Subgroup (Equiv.Perm α))
    (x y : α) : Set (α × α) :=
  {p | ∃ k : K, p = (k.1 x, k.1 y)}

def unorderedOrbital {α : Type} (K : Subgroup (Equiv.Perm α))
    (x y : α) : Set (α × α) :=
  orderedOrbital K x y ∪
    {p | ∃ k : K, p = (k.1 y, k.1 x)}

def pairMap {α : Type} (u : Equiv.Perm α) : α × α → α × α :=
  fun p => (u p.1, u p.2)

def fixesUnorderedOrbitals {α : Type} (u : Equiv.Perm α)
    (K : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ x y : α,
    Set.image (pairMap u) (unorderedOrbital K x y) = unorderedOrbital K x y

def conjugatesBy {α : Type} (u : Equiv.Perm α)
    (E F : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ e : Equiv.Perm α, e ∈ E ↔ u⁻¹ * e * u ∈ F

def diagonalPerm {d s : ℕ} (e : Equiv.Perm (localSpace d))
    (t : quotientSpace s) : Equiv.Perm (diagonalSpace d s) :=
  Equiv.prodCongr e (Equiv.addRight t)

def liftedPerm {d s : ℕ} (u : Equiv.Perm (localSpace d)) :
    Equiv.Perm (diagonalSpace d s) :=
  Equiv.prodCongr u (Equiv.refl (quotientSpace s))

def diagonalGenerators {d s : ℕ}
    (E : Subgroup (Equiv.Perm (localSpace d))) :
    Set (Equiv.Perm (diagonalSpace d s)) :=
  {g | ∃ e : Equiv.Perm (localSpace d), e ∈ E ∧
    ∃ t : quotientSpace s, g = diagonalPerm e t}

def diagonalCopy {d s : ℕ}
    (E : Subgroup (Equiv.Perm (localSpace d))) :
    Subgroup (Equiv.Perm (diagonalSpace d s)) :=
  Subgroup.closure (diagonalGenerators E)

def diagonalOrbitalDescription {d s : ℕ}
    (K : Subgroup (Equiv.Perm (localSpace d)))
    (v w : localSpace d) (q q' : quotientSpace s) :
    Set (diagonalSpace d s × diagonalSpace d s) :=
  {r | ∃ k : K,
    r.1.1 = k.1 v ∧ r.2.1 = k.1 w ∧
      r.2.2 - r.1.2 = q' - q}

def IsUnionOfOrbitals {α : Type} (K : Subgroup (Equiv.Perm α))
    (R : Set (α × α)) : Prop :=
  ∀ x y : α, (x, y) ∈ R → orderedOrbital K x y ⊆ R

def preservesRelation {α : Type} (u : Equiv.Perm α)
    (R : Set (α × α)) : Prop :=
  Set.image (pairMap u) R = R

def claim45991 : Prop :=
  ∀ d s : ℕ,
    (d = 3 ∨ d = 4 ∨ d = 5) → d + s ≤ 5 →
    ∀ E F : Subgroup (Equiv.Perm (localSpace d)),
      IsRegularElementaryAbelian E →
      IsRegularElementaryAbelian F →
      ∀ u : Equiv.Perm (localSpace d),
        conjugatesBy u E F →
        fixesUnorderedOrbitals u (generatedLocal E F) →
        conjugatesBy (liftedPerm (d := d) (s := s) u)
          (diagonalCopy (d := d) (s := s) E)
          (diagonalCopy (d := d) (s := s) F)

def claim45992 : Prop :=
  ∀ d s : ℕ,
    (d = 3 ∨ d = 4 ∨ d = 5) → d + s ≤ 5 →
    ∀ E F : Subgroup (Equiv.Perm (localSpace d)),
      IsRegularElementaryAbelian E →
      IsRegularElementaryAbelian F →
      let K := generatedLocal E F
      let R := diagonalCopy (d := d) (s := s) E
      let T := diagonalCopy (d := d) (s := s) F
      let H := Subgroup.closure ((R : Set (Equiv.Perm (diagonalSpace d s))) ∪
        (T : Set (Equiv.Perm (diagonalSpace d s))))
      (∀ e : Equiv.Perm (localSpace d), e ∈ E → ∀ t : quotientSpace s,
        diagonalPerm e 0 * diagonalPerm 1 t =
          diagonalPerm 1 t * diagonalPerm e 0) ∧
      H = diagonalCopy (d := d) (s := s) K ∧
      (∀ v w : localSpace d, ∀ q q' : quotientSpace s,
        orderedOrbital H (v, q) (w, q') =
          diagonalOrbitalDescription K v w q q')

def claim45993 : Prop :=
  ∀ d s : ℕ,
    (d = 3 ∨ d = 4 ∨ d = 5) → d + s ≤ 5 →
    ∀ E F : Subgroup (Equiv.Perm (localSpace d)),
      IsRegularElementaryAbelian E →
      IsRegularElementaryAbelian F →
      let K := generatedLocal E F
      (∀ e : E, e.1 * e.1 = 1) ∧
      (∀ v w : localSpace d, ∃! e : E,
        e.1 v = w ∧ e.1 w = v) ∧
      (∀ v w : localSpace d,
        Set.image (fun p : localSpace d × localSpace d => (p.2, p.1))
          (orderedOrbital K v w) = orderedOrbital K v w) ∧
      (∀ u : Equiv.Perm (localSpace d),
        fixesUnorderedOrbitals u K →
        ∀ v w : localSpace d,
          Set.image (pairMap u) (orderedOrbital K v w) =
            orderedOrbital K v w)

def claim45994 : Prop :=
  ∀ d s : ℕ,
    (d = 3 ∨ d = 4 ∨ d = 5) → d + s ≤ 5 →
    ∀ E F : Subgroup (Equiv.Perm (localSpace d)),
      IsRegularElementaryAbelian E →
      IsRegularElementaryAbelian F →
      ∀ u : Equiv.Perm (localSpace d),
        conjugatesBy u E F →
        fixesUnorderedOrbitals u (generatedLocal E F) →
        let K := generatedLocal E F
        let R := diagonalCopy (d := d) (s := s) E
        let T := diagonalCopy (d := d) (s := s) F
        let H := Subgroup.closure ((R : Set (Equiv.Perm (diagonalSpace d s))) ∪
          (T : Set (Equiv.Perm (diagonalSpace d s))))
        (H = diagonalCopy (d := d) (s := s) K ∧
          (∀ v w : localSpace d,
            Set.image (fun p : localSpace d × localSpace d => (p.2, p.1))
              (orderedOrbital K v w) = orderedOrbital K v w) ∧
          (∀ v w : localSpace d, ∀ q q' : quotientSpace s,
            orderedOrbital H (v, q) (w, q') =
              diagonalOrbitalDescription K v w q q')) →
        (∀ x y : diagonalSpace d s,
          Set.image (pairMap (liftedPerm (d := d) (s := s) u)) (orderedOrbital H x y) =
            orderedOrbital H x y) ∧
        conjugatesBy (liftedPerm (d := d) (s := s) u) R T ∧
        (∀ rel : Set (diagonalSpace d s × diagonalSpace d s),
          IsUnionOfOrbitals H rel → preservesRelation (liftedPerm (d := d) (s := s) u) rel)

end
end MathlibPlus.Open.ResearchFormalizationBatch
