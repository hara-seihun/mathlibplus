import Mathlib

noncomputable section

namespace MathlibPlus.Open.NewResearch2.R0473


private def CompleteTuple {n k : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin k → Fin n,
    Function.Injective f ∧
      ∀ i j, i ≠ j → G.Adj (f i) (f j)

private def IndependentTuple {n k : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin k → Fin n,
    Function.Injective f ∧
      ∀ i j, i ≠ j → ¬G.Adj (f i) (f j)

private def Good45 (G : SimpleGraph (Fin 24)) : Prop :=
  ¬CompleteTuple (k := 4) G ∧ ¬IndependentTuple (k := 5) G

private def GraphIso {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃ e : Equiv.Perm (Fin n),
    ∀ u v, G.Adj (e u) (e v) ↔ H.Adj u v

private def GraphAuto {n : ℕ} (G : SimpleGraph (Fin n))
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ u v, G.Adj (σ u) (σ v) ↔ G.Adj u v

private def SelectedAuto (G : SimpleGraph (Fin 24))
    (σ : Equiv.Perm (Fin 24)) : Prop :=
  Function.Involutive σ ∧
    (∀ v, σ v ≠ v) ∧
    GraphAuto G σ

private def Catalogue (C : Fin 352366 → SimpleGraph (Fin 24)) : Prop :=
  (∀ i, Good45 (C i)) ∧
    (∀ i j, i ≠ j → ¬GraphIso (C i) (C j)) ∧
    (∀ G : SimpleGraph (Fin 24), Good45 G → ∃ i, GraphIso G (C i))

private def Pairing12 (σ : Equiv.Perm (Fin 24))
    (reps : Fin 12 → Fin 24) : Prop :=
  Function.Involutive σ ∧
    (∀ v, σ v ≠ v) ∧
    (∀ i, reps i ≠ σ (reps i)) ∧
    (∀ i j, i ≠ j →
      reps i ≠ reps j ∧ reps i ≠ σ (reps j) ∧
        σ (reps i) ≠ reps j ∧ σ (reps i) ≠ σ (reps j)) ∧
    (∀ v : Fin 24, ∃ i, v = reps i ∨ v = σ (reps i))

private abbrev PairIndex12 := {p : Fin 12 × Fin 12 // p.1 < p.2}
private abbrev BitIndex12 := Fin 12 ⊕ (PairIndex12 × Fin 2)
private abbrev QuotientAssignment := BitIndex12 → Bool
private abbrev Endpoint12 := Fin 12 × Fin 2

private def QuotientEncoding (G : SimpleGraph (Fin 24))
    (σ : Equiv.Perm (Fin 24)) (reps : Fin 12 → Fin 24)
    (q : QuotientAssignment) : Prop :=
  (∀ i, G.Adj (reps i) (σ (reps i)) ↔
    q (Sum.inl i) = true) ∧
    (∀ p : PairIndex12,
      let i := p.1.1
      let j := p.1.2
      (G.Adj (reps i) (reps j) ↔
        q (Sum.inr (p, (0 : Fin 2))) = true) ∧
      (G.Adj (σ (reps i)) (σ (reps j)) ↔
        q (Sum.inr (p, (0 : Fin 2))) = true) ∧
      (G.Adj (reps i) (σ (reps j)) ↔
        q (Sum.inr (p, (1 : Fin 2))) = true) ∧
      (G.Adj (σ (reps i)) (reps j) ↔
        q (Sum.inr (p, (1 : Fin 2))) = true))

private def SelectedCard (C : Fin 352366 → SimpleGraph (Fin 24)) : ℕ :=
  Nat.card {
    p : (Σ i : Fin 352366, Equiv.Perm (Fin 24)) //
      SelectedAuto (C p.1) p.2 }

private def SelectedQ (C : Fin 352366 → SimpleGraph (Fin 24))
    (q : QuotientAssignment) : Prop :=
  ∃ (i : Fin 352366) (σ : Equiv.Perm (Fin 24))
      (reps : Fin 12 → Fin 24),
    SelectedAuto (C i) σ ∧
      Pairing12 σ reps ∧
      QuotientEncoding (C i) σ reps q

private def FeaturelessWreathAdj (q : QuotientAssignment)
    (a b : Endpoint12) : Prop :=
  if h : a.1 = b.1 then
    a.2 ≠ b.2 ∧ q (Sum.inl a.1) = true
  else
    (if h' : a.1 < b.1 then
      q (Sum.inr
        (⟨(a.1, b.1), h'⟩,
          if a.2 = b.2 then (0 : Fin 2) else (1 : Fin 2))) = true
    else if h'' : b.1 < a.1 then
      q (Sum.inr
        (⟨(b.1, a.1), h''⟩,
          if b.2 = a.2 then (0 : Fin 2) else (1 : Fin 2))) = true
    else False)

private def WreathRelated (q q' : QuotientAssignment) : Prop :=
  ∃ (π : Equiv.Perm (Fin 12)) (flips : Fin 12 → Fin 2),
    ∀ a b : Endpoint12,
      FeaturelessWreathAdj q' a b ↔
        FeaturelessWreathAdj q
          (π a.1, a.2 + flips a.1)
          (π b.1, b.2 + flips b.1)

private def SeedPartition (C : Fin 352366 → SimpleGraph (Fin 24))
    (seeds : Fin 8853 → QuotientAssignment) : Prop :=
  (∀ i j, WreathRelated (seeds i) (seeds j) ↔ i = j) ∧
    (∀ q, SelectedQ C q ↔ ∃ i, WreathRelated q (seeds i))

private def GadgetColor : (Fin 12 ⊕ Fin 24) → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

private def GadgetAdj (G : SimpleGraph (Fin 24))
    (σ : Equiv.Perm (Fin 24)) (reps : Fin 12 → Fin 24)
    (a b : Fin 12 ⊕ Fin 24) : Prop :=
  match a, b with
  | Sum.inl _, Sum.inl _ => False
  | Sum.inl i, Sum.inr v => v = reps i ∨ v = σ (reps i)
  | Sum.inr v, Sum.inl i => v = reps i ∨ v = σ (reps i)
  | Sum.inr v, Sum.inr w => G.Adj v w

private def ColoredGadgetIso
    (G : SimpleGraph (Fin 24)) (σ : Equiv.Perm (Fin 24))
    (reps : Fin 12 → Fin 24)
    (H : SimpleGraph (Fin 24)) (τ : Equiv.Perm (Fin 24))
    (reps' : Fin 12 → Fin 24) : Prop :=
  ∃ e : Equiv.Perm (Fin 12 ⊕ Fin 24),
    (∀ v, GadgetColor v = GadgetColor (e v)) ∧
      (∀ a b,
        GadgetAdj G σ reps (e a) (e b) ↔ GadgetAdj H τ reps' a b)

/-- Claim 21831: the complete order-24 (4,5) catalogue has 352366 entries. -/
def claim21831 : Prop :=
  ∃ C : Fin 352366 → SimpleGraph (Fin 24), Catalogue C

/-- Claim 21832: the selected fixed-point-free involution census is 9016. -/
def claim21832 : Prop :=
  ∃ C : Fin 352366 → SimpleGraph (Fin 24),
    Catalogue C ∧ SelectedCard C = 9016

/-- Claim 21833: a selected involution has twelve internal and two-per-pair bits. -/
def claim21833 : Prop :=
  ∀ (G : SimpleGraph (Fin 24)) (σ : Equiv.Perm (Fin 24)),
    SelectedAuto G σ →
      ∃ (reps : Fin 12 → Fin 24) (q : QuotientAssignment),
        Pairing12 σ reps ∧
          QuotientEncoding G σ reps q ∧
          Nat.card (Fin 12) + 2 * Nat.card PairIndex12 = 144

/-- Claim 21834: quotient assignments are identified by C₂ wr S₁₂. -/
def claim21834 : Prop :=
  (∀ q : QuotientAssignment, WreathRelated q q) ∧
    (∀ q q', WreathRelated q q' → WreathRelated q' q) ∧
    (∀ q q' q'', WreathRelated q q' → WreathRelated q' q'' →
      WreathRelated q q'') ∧
    (∀ q q', WreathRelated q q' ↔
      ∃ (π : Equiv.Perm (Fin 12)) (flips : Fin 12 → Fin 2),
        ∀ a b : Endpoint12,
          FeaturelessWreathAdj q' a b ↔
            FeaturelessWreathAdj q
              (π a.1, a.2 + flips a.1)
              (π b.1, b.2 + flips b.1))

/-- Claim 21835: the matching-aware colored gadget realizes wreath equivalence. -/
def claim21835 : Prop :=
  ∀ (G H : SimpleGraph (Fin 24))
      (σ τ : Equiv.Perm (Fin 24))
      (reps reps' : Fin 12 → Fin 24)
      (q q' : QuotientAssignment),
    Good45 G → Good45 H →
    SelectedAuto G σ → SelectedAuto H τ →
    Pairing12 σ reps → Pairing12 τ reps' →
    QuotientEncoding G σ reps q → QuotientEncoding H τ reps' q' →
      (ColoredGadgetIso G σ reps H τ reps' ↔ WreathRelated q q')

/-- Claim 21836: 9016 selected elements give 8853 wreath orbits. -/
def claim21836 : Prop :=
  ∃ C : Fin 352366 → SimpleGraph (Fin 24),
    Catalogue C ∧ SelectedCard C = 9016 ∧
      ∃ seeds : Fin 8853 → QuotientAssignment,
        SeedPartition C seeds ∧ (9016 : ℕ) = 8853 + 163

/-- Claim 21837: canonical labels are unchanged exactly on wreath orbits. -/
def claim21837 : Prop :=
  ∃ canonical : QuotientAssignment → QuotientAssignment,
    (∀ q, WreathRelated q (canonical q)) ∧
      (∀ q q', canonical q = canonical q' ↔ WreathRelated q q') ∧
      (∀ q q', WreathRelated q q' → canonical q = canonical q')

private def NonneighborCell (G : SimpleGraph (Fin 43)) (r : Fin 43)
    (e : Fin 24 → Fin 43) : Prop :=
  Function.Injective e ∧
    (∀ x : Fin 43, x ≠ r ∧ ¬G.Adj r x ↔ ∃ i, e i = x)

private def ComplementGood45OnCell (G : SimpleGraph (Fin 43))
    (e : Fin 24 → Fin 43) : Prop :=
  ¬(∃ f : Fin 4 → Fin 24,
      Function.Injective f ∧
        ∀ i j, i ≠ j → ¬G.Adj (e (f i)) (e (f j))) ∧
    ¬(∃ f : Fin 5 → Fin 24,
      Function.Injective f ∧
        ∀ i j, i ≠ j → G.Adj (e (f i)) (e (f j)))

/-- Claim 21839: the degree-18 nonneighbor cell complements to an R(4,5,24) graph. -/
def claim21839 : Prop :=
  ∀ (G : SimpleGraph (Fin 43)) (r : Fin 43),
    (¬CompleteTuple (k := 5) G ∧ ¬IndependentTuple (k := 5) G) →
    Nat.card {w : Fin 43 // G.Adj r w} = 18 →
      ∃ e : Fin 24 → Fin 43,
        NonneighborCell G r e ∧ ComplementGood45OnCell G e

/-- Claim 21840: the involution restricts to a fixed-point-free cell involution. -/
def claim21840 : Prop :=
  ∀ (G : SimpleGraph (Fin 43)) (σ : Equiv.Perm (Fin 43)) (r : Fin 43),
    Function.Involutive σ →
    (∀ w, σ w = w ↔ w = r) →
    σ r = r →
    GraphAuto G σ →
      ∀ e : Fin 24 → Fin 43,
        NonneighborCell G r e →
          (∀ x, G.Adj r (σ x) ↔ G.Adj r x) ∧
            ∃ τ : Equiv.Perm (Fin 24),
              Function.Involutive τ ∧ (∀ i, τ i ≠ i) ∧
                (∀ i, e (τ i) = σ (e i))

/-- Claim 21841: every degree-18 cell has exactly one canonical seed. -/
def claim21841 : Prop :=
  ∀ (G : SimpleGraph (Fin 43)) (σ : Equiv.Perm (Fin 43)) (r : Fin 43)
      (e : Fin 24 → Fin 43) (τ : Equiv.Perm (Fin 24))
      (H : SimpleGraph (Fin 24))
      (C : Fin 352366 → SimpleGraph (Fin 24))
      (seeds : Fin 8853 → QuotientAssignment),
    (¬CompleteTuple (k := 5) G ∧ ¬IndependentTuple (k := 5) G) →
    Function.Involutive σ →
    (∀ w, σ w = w ↔ w = r) → σ r = r →
    GraphAuto G σ →
    Nat.card {w : Fin 43 // G.Adj r w} = 18 →
    NonneighborCell G r e →
    (∀ i, e (τ i) = σ (e i)) →
    Function.Involutive τ → (∀ i, τ i ≠ i) → GraphAuto H τ →
    (∀ i j, H.Adj i j ↔ i ≠ j ∧ ¬G.Adj (e i) (e j)) →
    Good45 H → Catalogue C → SeedPartition C seeds →
      ∃ (reps : Fin 12 → Fin 24) (q : QuotientAssignment)
          (i : Fin 8853),
        Pairing12 τ reps ∧
          QuotientEncoding H τ reps q ∧
          SelectedQ C q ∧
          WreathRelated q (seeds i) ∧
          ∀ j, WreathRelated q (seeds j) ↔ j = i

/-- Claim 21842: forgetting the selected matching can merge nonconjugate elements. -/
def claim21842 : Prop :=
  ∃ (G H : SimpleGraph (Fin 24)) (σ τ : Equiv.Perm (Fin 24)),
    Good45 G ∧ Good45 H ∧
      SelectedAuto G σ ∧ SelectedAuto H τ ∧
      GraphIso G H ∧
      ¬∃ e : Equiv.Perm (Fin 24),
        (∀ u v, G.Adj (e u) (e v) ↔ H.Adj u v) ∧
          (∀ v, e (σ v) = τ (e v))

/-- Claim 21843: the seed partition itself carries no solver or branch conclusion. -/
def claim21843 : Prop :=
  ∃ C : Fin 352366 → SimpleGraph (Fin 24),
    Catalogue C ∧
      ∃ seeds : Fin 8853 → QuotientAssignment,
        SeedPartition C seeds ∧
          (∀ q, SelectedQ C q → ∃! i, WreathRelated q (seeds i))

end MathlibPlus.Open.NewResearch2.R0473
