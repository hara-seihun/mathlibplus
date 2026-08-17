import Mathlib

namespace MathlibPlus.Open.GraphTheory.R0358VertexDeck

noncomputable section

abbrev Graph12 := SimpleGraph (Fin 12)
abbrev CardGraph11 := SimpleGraph (Fin 11)

def graphIso12Rel (G H : Graph12) : Prop := Nonempty (G ≃g H)
abbrev Graph12Type := Quot graphIso12Rel

def graphIso11Rel (G H : CardGraph11) : Prop := Nonempty (G ≃g H)
abbrev CardGraph11Type := Quot graphIso11Rel

def edgeCount12 (G : Graph12) : ℕ := G.edgeSet.ncard

def deletedCard12 (G : Graph12) (v : Fin 12) : CardGraph11 :=
  G.comap (Fin.succAbove v)

def vertexDeckSignature (G : Graph12) : Multiset CardGraph11Type :=
  (Finset.univ : Finset (Fin 12)).val.map
    (fun v => Quot.mk graphIso11Rel (deletedCard12 G v))

def vertexDeckEqualByPermutation (G H : Graph12) : Prop :=
  ∃ σ : Equiv.Perm (Fin 12), ∀ v : Fin 12,
    Nonempty (deletedCard12 G v ≃g deletedCard12 H (σ v))

def connectedWithEdgeCount (m : ℕ) (G : Graph12) : Prop :=
  G.Connected ∧ edgeCount12 G = m

def graph12TypeAtEdgeCount (m : ℕ) (q : Graph12Type) : Prop :=
  ∃ G : Graph12,
    Quot.mk graphIso12Rel G = q ∧ connectedWithEdgeCount m G

noncomputable def graph12TypeCount (m : ℕ) : ℕ :=
  Nat.card {q : Graph12Type // graph12TypeAtEdgeCount m q}

def deckSignatureAtEdgeCount (m : ℕ) (d : Multiset CardGraph11Type) : Prop :=
  ∃ G : Graph12, connectedWithEdgeCount m G ∧ vertexDeckSignature G = d

noncomputable def deckSignatureCount (m : ℕ) : ℕ :=
  Nat.card {d : Multiset CardGraph11Type // deckSignatureAtEdgeCount m d}

def deckCollisionSignatureAtEdgeCount
    (m : ℕ) (d : Multiset CardGraph11Type) : Prop :=
  ∃ G H : Graph12,
    connectedWithEdgeCount m G ∧ connectedWithEdgeCount m H ∧
    vertexDeckSignature G = d ∧ vertexDeckSignature H = d ∧
    ¬ Nonempty (G ≃g H)

noncomputable def deckCollisionClassCount (m : ℕ) : ℕ :=
  Nat.card {d : Multiset CardGraph11Type // deckCollisionSignatureAtEdgeCount m d}

def vertexDeckInjectivityAt12_14_claim20366 : Prop :=
  ∀ G H : Graph12,
    connectedWithEdgeCount 14 G →
      connectedWithEdgeCount 14 H →
        vertexDeckEqualByPermutation G H → Nonempty (G ≃g H)

def vertexDeckCensusAt12_14_claim20367 : Prop :=
  graph12TypeCount 14 = 130365 ∧
    deckSignatureCount 14 = 130365 ∧
    deckCollisionClassCount 14 = 0

def vertexDeckCensusAt12_15_claim20369 : Prop :=
  graph12TypeCount 15 = 499888 ∧
    deckSignatureCount 15 = 499888 ∧
    deckCollisionClassCount 15 = 0

end
end MathlibPlus.Open.GraphTheory.R0358VertexDeck
