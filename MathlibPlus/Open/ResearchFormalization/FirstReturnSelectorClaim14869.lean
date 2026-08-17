import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.FirstReturnSelectorClaim14869

/-- The fixed-length Dyck-word carrier used by the canonical selector. -/
abbrev RawWord (n : ℕ) := Fin (2 * n) → Bool

private def upCount {n : ℕ} (w : RawWord n) (t : Fin (2 * n + 1)) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * n))).filter
    (fun i => i.val < t.val ∧ w i = true)).card

private def downCount {n : ℕ} (w : RawWord n) (t : Fin (2 * n + 1)) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * n))).filter
    (fun i => i.val < t.val ∧ w i = false)).card

private def isDyck {n : ℕ} (w : RawWord n) : Prop :=
  upCount w (Fin.last (2 * n)) = n ∧
    ∀ t, downCount w t ≤ upCount w t

/-- Inversion area on the finite word representation. -/
private def listArea (w : List Bool) : ℕ :=
  ((Finset.univ : Finset (Fin w.length × Fin w.length)).filter
    (fun p => p.1.val < p.2.val ∧
      w.get p.1 = false ∧ w.get p.2 = true)).card

/-- Split the suffix after the initial up-step at its first return. -/
private def splitReturnAux : ℕ → List Bool → List Bool × List Bool
  | _, [] => ([], [])
  | level, x :: xs =>
      if x then
        let q := splitReturnAux (level + 1) xs
        (true :: q.1, q.2)
      else if level = 1 then
        ([], xs)
      else
        let q := splitReturnAux (level - 1) xs
        (false :: q.1, q.2)

private def firstReturnParts (w : List Bool) : List Bool × List Bool :=
  match w with
  | true :: rest => splitReturnAux 1 rest
  | _ => ([], [])

/-- The fuel-bounded implementation of the first-return canonical selector. -/
def canonicalSelectorFuel : ℕ → List Bool → List Bool
  | 0, w => w
  | fuel + 1, w =>
      match w with
      | true :: rest =>
          let parts := splitReturnAux 1 rest
          let A := parts.1
          let B := parts.2
          if Odd (listArea A) then
            true :: (canonicalSelectorFuel fuel A ++ [false] ++ B)
          else if Odd (listArea B) then
            true :: (A ++ [false] ++ canonicalSelectorFuel fuel B)
          else
            match B with
            | true :: tail => true :: (A ++ [true, false] ++ tail)
            | _ => w
      | _ => w

private def canonicalSelectorList (w : List Bool) : List Bool :=
  canonicalSelectorFuel w.length w

private def listOfRaw {n : ℕ} (w : RawWord n) : List Bool :=
  List.ofFn w

private def rawOfList {n : ℕ} (w : List Bool) : RawWord n :=
  fun i => w.getD i.val false

private def canonicalSelectorRaw {n : ℕ} (w : RawWord n) : RawWord n :=
  rawOfList (canonicalSelectorList (listOfRaw w))

/-- Inserting the outer return arc, i.e. the outer-wrap operation. -/
private def outerWrap {n : ℕ} (w : RawWord n) : RawWord (n + 1) :=
  rawOfList (true :: listOfRaw w ++ [false])

private def firstReturn (a b : ℕ) (A : RawWord a) (B : RawWord b)
    (w : RawWord (a + b + 1)) : Prop :=
  isDyck A ∧ isDyck B ∧ isDyck w ∧
    listOfRaw w =
      true :: (listOfRaw A ++ [false] ++ listOfRaw B) ∧
    firstReturnParts (listOfRaw w) =
      (listOfRaw A, listOfRaw B)

private def firstReturnArea : Prop :=
  ∀ (a b : ℕ) (A : RawWord a) (B : RawWord b)
    (w : RawWord (a + b + 1)),
    firstReturn a b A B w →
      listArea (listOfRaw w) =
        listArea (listOfRaw A) + listArea (listOfRaw B) + (a + 1) * b

/-- The three exact branches of the odd-area selector, including the
return-valley toggle in the even-factor case. -/
private def selectorBranch (a b : ℕ) (A : RawWord a) (B : RawWord b)
    (w : RawWord (a + b + 1)) : Prop :=
  (Odd (listArea (listOfRaw A)) ∧
    listOfRaw (canonicalSelectorRaw w) =
      true ::
        (listOfRaw (canonicalSelectorRaw A) ++
          [false] ++ listOfRaw B)) ∨
  (Odd (listArea (listOfRaw B)) ∧
    listOfRaw (canonicalSelectorRaw w) =
      true ::
        (listOfRaw A ++ [false] ++
          listOfRaw (canonicalSelectorRaw B))) ∨
  (Even (listArea (listOfRaw A)) ∧
    Even (listArea (listOfRaw B)) ∧
    Odd ((a + 1) * b) ∧
    ∃ tail : List Bool,
      listOfRaw B = true :: tail ∧
      listOfRaw (canonicalSelectorRaw w) =
        true :: (listOfRaw A ++ [true, false] ++ tail))

private def oddSelector : Prop :=
  ∀ (a b : ℕ) (A : RawWord a) (B : RawWord b)
    (w : RawWord (a + b + 1)),
    firstReturn a b A B w →
      Odd (listArea (listOfRaw w)) →
        selectorBranch a b A B w

private def selectorWrap : Prop :=
  ∀ (n : ℕ) (w : RawWord n),
    isDyck w →
      Odd (listArea (listOfRaw w)) →
        canonicalSelectorRaw (outerWrap w) =
          outerWrap (canonicalSelectorRaw w)

/-- Claim 14869: the first-return inversion-area identity, the odd-area
recursive selector with its even-factor return-valley toggle, and the exact
outer-wrap compatibility on odd-area Dyck words. -/
def claim14869 : Prop :=
  firstReturnArea ∧ oddSelector ∧ selectorWrap

end MathlibPlus.Open.ResearchFormalization.FirstReturnSelectorClaim14869
