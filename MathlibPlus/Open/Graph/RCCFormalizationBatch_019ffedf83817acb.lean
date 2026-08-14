import Mathlib

namespace MathlibPlus.Open.Graph.RCCBatch

/-- The cyclic adjacency relation on the part indices. -/
def cycleAdjacent (j : ℕ) (i k : Fin j) : Prop :=
  (i.val + 1) % j = k.val ∨ (k.val + 1) % j = i.val

/-- The graph whose vertices are the explicitly named vertices `v_{c,i}`. -/
def rccGraph (n j : ℕ) : SimpleGraph (Fin n × Fin j) :=
  SimpleGraph.fromRel (fun u v => (u.2.val + 1) % j = v.2.val)

/-- A cyclic independent blow-up with the indicated part sizes. -/
def cyclicBlowup {j : ℕ} (sizes : Fin j → ℕ) :
    SimpleGraph (Σ i : Fin j, Fin (sizes i)) :=
  SimpleGraph.fromRel (fun u v => (u.1.val + 1) % j = v.1.val)

 def rccPart {n j : ℕ} (i : Fin j) : Set (Fin n × Fin j) :=
  {v | v.2 = i}

def blowupPart {j : ℕ} (sizes : Fin j → ℕ) (i : Fin j) :
    Set (Σ k : Fin j, Fin (sizes k)) :=
  {v | v.1 = i}

def independent {V : Type} (G : SimpleGraph V) (s : Set V) : Prop :=
  ∀ ⦃v w : V⦄, v ∈ s → w ∈ s → ¬G.Adj v w

def completeBetween {V : Type} (G : SimpleGraph V) (s t : Set V) : Prop :=
  ∀ ⦃v w : V⦄, v ∈ s → w ∈ t → G.Adj v w

def anticompleteBetween {V : Type} (G : SimpleGraph V) (s t : Set V) : Prop :=
  ∀ ⦃v w : V⦄, v ∈ s → w ∈ t → ¬G.Adj v w

/-- Exact formal statement of Claim 29505. -/
def claim29505 : Prop :=
  ∀ (n j : ℕ), 2 ≤ n → 3 ≤ j →
    (∀ v : Fin n × Fin j, ∃! i : Fin j, v ∈ rccPart i) ∧
    (∀ i : Fin j, independent (rccGraph n j) (rccPart i)) ∧
    (∀ i k : Fin j, cycleAdjacent j i k →
      completeBetween (rccGraph n j) (rccPart i) (rccPart k)) ∧
    (∀ i k : Fin j, ¬cycleAdjacent j i k →
      anticompleteBetween (rccGraph n j) (rccPart i) (rccPart k)) ∧
    (∀ i : Fin j, Set.ncard (blowupPart (fun _ : Fin j => n) i) = n) ∧
    Nonempty (rccGraph n j ≃g cyclicBlowup (fun _ : Fin j => n))

def deficientSizes (n j : ℕ) (i : Fin j) : ℕ :=
  if i.val = 0 then n - 1 else n

def unitTransferSizes (n j : ℕ) (r i : Fin j) : ℕ :=
  if i.val = 0 then n - 1 else if i = r then n + 1 else n

def deficientCardGraph (n j : ℕ) :
    SimpleGraph (Σ i : Fin j, Fin (deficientSizes n j i)) :=
  cyclicBlowup (deficientSizes n j)

def unitTransferGraph (n j : ℕ) (r : Fin j) :
    SimpleGraph (Σ i : Fin j, Fin (unitTransferSizes n j r i)) :=
  cyclicBlowup (unitTransferSizes n j r)

def cardAt {V : Type} (G : SimpleGraph V) (v : V) :
    SimpleGraph {w // w ≠ v} :=
  G.induce {w | w ≠ v}

noncomputable def cardMultiplicity {V W : Type} [Fintype V] (A : SimpleGraph W)
    (G : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v => Nonempty (cardAt G v ≃g A))).card

def sameOpenNeighborhood {V : Type} (G : SimpleGraph V) (v w : V) : Prop :=
  ∀ x : V, G.Adj v x ↔ G.Adj w x

def partClone {j : ℕ} {sizes : Fin j → ℕ}
    (G : SimpleGraph (Σ i : Fin j, Fin (sizes i))) (i : Fin j) : Prop :=
  ∀ ⦃v w : (Σ k : Fin j, Fin (sizes k))⦄,
    v.1 = i → w.1 = i → sameOpenNeighborhood G v w

def sameFalseTwinClass {j : ℕ} {sizes : Fin j → ℕ}
    (G : SimpleGraph (Σ i : Fin j, Fin (sizes i)))
    (v w : Σ i : Fin j, Fin (sizes i)) : Prop :=
  ∀ x, G.Adj v x ↔ G.Adj w x

/-- Exact formal statement of Claim 29508. -/
def claim29508 : Prop :=
  ∀ (n j : ℕ), 2 ≤ n → 3 ≤ j →
    (∀ i : Fin j,
      Set.ncard (blowupPart (deficientSizes n j) i) =
        if i.val = 0 then n - 1 else n) ∧
    (∀ v : Fin n × Fin j,
      Nonempty (cardAt (rccGraph n j) v ≃g deficientCardGraph n j)) ∧
    cardMultiplicity (deficientCardGraph n j) (rccGraph n j) = n * j

def partAction {n j : ℕ} (f : deficientCardGraph n j ≃g deficientCardGraph n j)
    (σ : Fin j → Fin j) : Prop :=
  ∀ v : (Σ i : Fin j, Fin (deficientSizes n j i)),
    (f.toEquiv v).1 = σ v.1

def reflectionAtZero (j : ℕ) (σ : Fin j → Fin j) : Prop :=
  ∀ i : Fin j,
    (σ i).val = if i.val = 0 then 0 else j - i.val

/-- Exact formal statement of Claim 29509. -/
def claim29509 : Prop :=
  ∀ (n j : ℕ), 2 ≤ n → 5 ≤ j →
    (∀ v w : (Σ i : Fin j, Fin (deficientSizes n j i)),
      v.1 = w.1 ↔ sameFalseTwinClass (deficientCardGraph n j) v w) ∧
    (∀ i : Fin j,
      Set.ncard (blowupPart (deficientSizes n j) i) = n - 1 ↔ i.val = 0) ∧
    (∀ f : deficientCardGraph n j ≃g deficientCardGraph n j,
      (∀ v : (Σ i : Fin j, Fin (deficientSizes n j i)),
        v.1.val = 0 ↔ (f.toEquiv v).1.val = 0) ∧
      ∃ σ : Fin j → Fin j,
        partAction f σ ∧
        ((∀ i : Fin j, σ i = i) ∨ reflectionAtZero j σ))

/-- Exact formal statement of Claim 29510. -/
def claim29510 : Prop :=
  ∀ (n j : ℕ) (r : Fin j), 2 ≤ n → 3 ≤ j → r.val ≠ 0 →
    (∀ i : Fin j,
      Set.ncard (blowupPart (unitTransferSizes n j r) i) =
        if i.val = 0 then n - 1 else if i = r then n + 1 else n) ∧
    (∃ v : (Σ i : Fin j, Fin (unitTransferSizes n j r i)),
      v.1 = r ∧
        Nonempty (cardAt (unitTransferGraph n j r) v ≃g deficientCardGraph n j)) ∧
    partClone (unitTransferGraph n j r) r

/-- Exact formal statement of Claim 29511. -/
def claim29511 : Prop :=
  ∀ (n j : ℕ) (r : Fin j), 2 ≤ n → 3 ≤ j → r.val ≠ 0 →
    Set.ncard (blowupPart (unitTransferSizes n j r) r) = n + 1 ∧
    (∀ v : (Σ i : Fin j, Fin (unitTransferSizes n j r i)),
      v.1 = r →
      Nonempty (cardAt (unitTransferGraph n j r) v ≃g deficientCardGraph n j)) ∧
    cardMultiplicity (deficientCardGraph n j) (unitTransferGraph n j r) = n + 1 ∧
    3 ≤ n + 1

def dihedralEquivalent (j : ℕ) (r r' : Fin j) : Prop :=
  r = r' ∨ r.val + r'.val = j

def representativeOffset (j : ℕ) (r : Fin j) : Prop :=
  0 < r.val ∧ r.val ≤ j / 2

/-- Exact formal statement of Claim 29512. -/
def claim29512 : Prop := by
  classical
  exact ∀ (n j : ℕ), 2 ≤ n → 3 ≤ j →
    (∀ r r' : Fin j, r.val ≠ 0 → r'.val ≠ 0 →
      (Nonempty (unitTransferGraph n j r ≃g unitTransferGraph n j r') ↔
        dihedralEquivalent j r r')) ∧
    (Finset.filter (representativeOffset j) Finset.univ).card = j / 2

def graphFromParts {j : ℕ} (part : Fin 10 → Fin j) : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel (fun x y => cycleAdjacent j (part x) (part y))

def hostParts (x : Fin 10) : Fin 5 :=
  ⟨x.val / 2, by omega⟩

def transferOneParts (x : Fin 10) : Fin 5 :=
  if x.val = 0 then (0 : Fin 5)
  else if x.val ≤ 3 then (1 : Fin 5)
  else if x.val ≤ 5 then (2 : Fin 5)
  else if x.val ≤ 7 then (3 : Fin 5)
  else (4 : Fin 5)

def transferTwoParts (x : Fin 10) : Fin 5 :=
  if x.val = 0 then (0 : Fin 5)
  else if x.val ≤ 2 then (1 : Fin 5)
  else if x.val ≤ 5 then (2 : Fin 5)
  else if x.val ≤ 7 then (3 : Fin 5)
  else (4 : Fin 5)

def orderTenRcc : SimpleGraph (Fin 10) := graphFromParts hostParts
def orderTenTransferOne : SimpleGraph (Fin 10) := graphFromParts transferOneParts
def orderTenTransferTwo : SimpleGraph (Fin 10) := graphFromParts transferTwoParts

def extensionFiber {W : Type} (A : SimpleGraph W) :
    Set (SimpleGraph (Fin 10)) :=
  {G | ∃ v : Fin 10, Nonempty (cardAt G v ≃g A)}

def regularOrderTen (G : SimpleGraph (Fin 10)) : Prop := by
  classical
  exact ∃ d : ℕ, ∀ v : Fin 10,
    (Finset.univ.filter (fun w : Fin 10 => G.Adj v w)).card = d

/-- Exact formal statement of Claim 29513. -/
def claim29513 : Prop :=
  let A := cardAt orderTenRcc (0 : Fin 10)
  (regularOrderTen orderTenRcc ∧
      ¬regularOrderTen orderTenTransferOne ∧
      ¬regularOrderTen orderTenTransferTwo) ∧
    (∀ G : SimpleGraph (Fin 10), G ∈ extensionFiber A →
      ((3 ≤ cardMultiplicity A G) ↔
        Nonempty (G ≃g orderTenRcc) ∨
        Nonempty (G ≃g orderTenTransferOne) ∨
        Nonempty (G ≃g orderTenTransferTwo))) ∧
    (∀ G : SimpleGraph (Fin 10),
      (G ∈ extensionFiber A ∧ 3 ≤ cardMultiplicity A G ∧
          ¬regularOrderTen G) ↔
        (Nonempty (G ≃g orderTenTransferOne) ∨
          Nonempty (G ≃g orderTenTransferTwo)))

/-- Exact formal statement of Claim 34996. -/
def claim34996 : Prop :=
  ∀ (n j : ℕ), 2 ≤ n → 5 ≤ j →
    let G := deficientCardGraph n j
    (∀ v w : (Σ i : Fin j, Fin (deficientSizes n j i)),
      (v.1 = w.1 ↔ sameFalseTwinClass G v w)) ∧
    (∀ v w : (Σ i : Fin j, Fin (deficientSizes n j i)), v.1 = w.1 → ¬G.Adj v w) ∧
    (∀ v w : (Σ i : Fin j, Fin (deficientSizes n j i)), v.1 ≠ w.1 →
      ∃ x, G.Adj v x ≠ G.Adj w x) ∧
    (∀ i : Fin j,
      Set.ncard (blowupPart (deficientSizes n j) i) =
        if i.val = 0 then n - 1 else n) ∧
    (∀ i : Fin j,
      Set.ncard (blowupPart (deficientSizes n j) i) = n - 1 ↔ i.val = 0)

end MathlibPlus.Open.Graph.RCCBatch
