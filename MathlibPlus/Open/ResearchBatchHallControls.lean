import Mathlib

namespace MathlibPlus.Open.ResearchBatchHallControls

noncomputable section

abbrev Gm (m : ℕ) := ZMod m × ZMod 8

def gmMul (m : ℕ) (g h : Gm m) : Gm m :=
  (g.1 + (-1 : ZMod m) ^ g.2.val * h.1, g.2 + h.2)

def gmOne (m : ℕ) : Gm m := (0, 0)

def gmInv (m : ℕ) (g : Gm m) : Gm m :=
  (-((-1 : ZMod m) ^ g.2.val * g.1), -g.2)

def gmPow (m : ℕ) (g : Gm m) : ℕ → Gm m
  | 0 => gmOne m
  | n + 1 => gmMul m (gmPow m g n) g

def gmGroupAxioms (m : ℕ) : Prop :=
  (∀ a b c, gmMul m (gmMul m a b) c = gmMul m a (gmMul m b c)) ∧
    (∀ g, gmMul m (gmOne m) g = g ∧ gmMul m g (gmOne m) = g) ∧
    (∀ g, gmMul m (gmInv m g) g = gmOne m ∧ gmMul m g (gmInv m g) = gmOne m)

def gmA (m : ℕ) : Gm m := (1, 0)
def gmB (m : ℕ) : Gm m := (0, 1)

def gmPresentationRelations (m : ℕ) : Prop :=
  gmPow m (gmA m) m = gmOne m ∧
    gmPow m (gmB m) 8 = gmOne m ∧
    gmMul m (gmMul m (gmInv m (gmB m)) (gmA m)) (gmB m) = gmInv m (gmA m)

def gmRegularAction (m : ℕ) : Prop :=
  ∀ v w : Gm m, ∃! g : Gm m, gmMul m g v = w

def oddHallCarrier (m : ℕ) : Set (Gm m) :=
  {g | ∃ n : ℕ, n % 2 = 1 ∧ gmPow m g n = gmOne m}

def explicitOddHallCarrier (m : ℕ) : Set (Gm m) :=
  {g | g.2 = 0}

def gmAutomorphism (m : ℕ) (φ : Gm m → Gm m) : Prop :=
  Function.Bijective φ ∧
    (∀ g h, φ (gmMul m g h) = gmMul m (φ g) (φ h)) ∧
    φ (gmOne m) = gmOne m

def hallBlock (m : ℕ) (j : ZMod 8) : Set (Gm m) :=
  {g | g.2 = j}

def hallOrbitBlock (m : ℕ) (j : ZMod 8) : Set (Gm m) :=
  (fun g : Gm m => gmMul m g (0, j)) '' explicitOddHallCarrier m

def characteristicOddHall (m : ℕ) : Prop :=
  explicitOddHallCarrier m = oddHallCarrier m ∧
    ∀ φ : Gm m → Gm m, gmAutomorphism m φ →
      φ '' explicitOddHallCarrier m = explicitOddHallCarrier m

/-- The presented `C_m ⋊ C_8` operation, its regular action, and the eight
cosets/orbit blocks of its characteristic odd Hall carrier. -/
def oddHallRegularActionClaim : Prop :=
  ∀ m : ℕ, 1 < m → m % 2 = 1 →
    gmGroupAxioms m ∧ gmPresentationRelations m ∧ gmRegularAction m ∧
      characteristicOddHall m ∧
      ∀ j : ZMod 8, hallOrbitBlock m j = hallBlock m j

def completeGraphAutomorphism (m : ℕ) (φ : Gm m → Gm m) : Prop :=
  Function.Bijective φ ∧ ∀ x y, x ≠ y ↔ φ x ≠ φ y

def transposition (m : ℕ) : Gm m → Gm m :=
  Equiv.swap (0, 0) (0, 1)

def standardRegularCopy (m : ℕ) : Set (Gm m → Gm m) :=
  Set.range (fun g : Gm m => gmMul m g)

def conjugateBy (m : ℕ) (τ : Gm m → Gm m) (f : Gm m → Gm m) : Gm m → Gm m :=
  τ ∘ f ∘ τ

def conjugatedRegularCopy (m : ℕ) : Set (Gm m → Gm m) :=
  Set.image (conjugateBy m (transposition m)) (standardRegularCopy m)

def isRegularCopy (m : ℕ) (C : Set (Gm m → Gm m)) : Prop :=
  (∀ f, f ∈ C → Function.Bijective f) ∧
    (∀ v w : Gm m, ∃! f, f ∈ C ∧ f v = w)

def hallPartition (m : ℕ) : Set (Set (Gm m)) :=
  Set.range (hallBlock m)

def completeMultipartiteGraphAutomorphism (m : ℕ) (φ : Gm m → Gm m) : Prop :=
  Function.Bijective φ ∧
    ∀ u v, u.1 ≠ v.1 ↔ (φ u).1 ≠ (φ v).1

def wreathPermutation (m : ℕ) (φ : Gm m → Gm m) : Prop :=
  ∃ σ : Equiv.Perm (ZMod m),
    ∃ locals : ZMod m → Equiv.Perm (ZMod 8),
      ∀ g : Gm m, φ g = (σ g.1, locals g.1 g.2)

def wreathPermutationSet (m : ℕ) : Set (Gm m → Gm m) :=
  {φ | wreathPermutation m φ}

def completeMultipartiteHallControlClaim : Prop :=
  ∀ m : ℕ, 1 < m → m % 2 = 1 →
    let τ := transposition m
    completeMultipartiteGraphAutomorphism m τ ∧
      isRegularCopy m (standardRegularCopy m) ∧
      isRegularCopy m (conjugatedRegularCopy m) ∧
      (∃ B : Set (Gm m), B ∈ hallPartition m ∧ τ '' B ∉ hallPartition m) ∧
      (∀ φ : Gm m → Gm m, completeMultipartiteGraphAutomorphism m φ ↔
        φ ∈ wreathPermutationSet m)

def completeGraphHallControlClaim : Prop :=
  ∀ m : ℕ, 1 < m → m % 2 = 1 →
    let τ := transposition m
    completeGraphAutomorphism m τ ∧
      isRegularCopy m (standardRegularCopy m) ∧
      isRegularCopy m (conjugatedRegularCopy m) ∧
      conjugatedRegularCopy m ≠ standardRegularCopy m ∧
      ∃ B : Set (Gm m), B ∈ hallPartition m ∧ τ '' B ∉ hallPartition m

end
end MathlibPlus.Open.ResearchBatchHallControls
