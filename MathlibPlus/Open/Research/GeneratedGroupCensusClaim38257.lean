import MathlibPlus.Open.Research.GeneratedGroupExact

namespace MathlibPlus.Open.Research.GeneratedGroupCensus

noncomputable section

open MathlibPlus.Open.Research.GeneratedGroupExact

abbrev MaskRows := Finset Mask

def classicalFilter {α : Type*} (p : α → Prop) (s : Finset α) : Finset α :=
  @Finset.filter α p (Classical.decPred p) s

def maskRows : MaskRows :=
  Finset.univ

def nonconstantRows : MaskRows :=
  classicalFilter (fun μ => ¬ constantMask μ) maskRows

def constantRows : MaskRows :=
  classicalFilter constantMask maskRows

def nonconjugateRows (q : ℕ) : MaskRows :=
  classicalFilter (fun μ => ¬ conjugateWithinGenerated q μ) maskRows

def conjugateRows (q : ℕ) : MaskRows :=
  classicalFilter (fun μ => conjugateWithinGenerated q μ) maskRows

def nonconstantNonconjugateRows (q : ℕ) : MaskRows :=
  classicalFilter (fun μ => ¬ constantMask μ ∧
    ¬ conjugateWithinGenerated q μ) maskRows

def constantConjugateRows (q : ℕ) : MaskRows :=
  classicalFilter (fun μ => constantMask μ ∧
    conjugateWithinGenerated q μ) maskRows

def signCodeRank (μ : Mask) : ℕ :=
  Module.finrank (ZMod 2) (generatedSignCode μ)

def twoPrimeMaskRows : Finset (ℕ × Mask) :=
  ({5, 7} : Finset ℕ).product maskRows

def rankRowsAcrossPrimes (r : ℕ) : Finset (ℕ × Mask) :=
  classicalFilter (fun qm => signCodeRank qm.2 = r) twoPrimeMaskRows

def generatedGroupOrder (q : ℕ) (μ : Mask) : ℕ :=
  Nat.card (generatedGroup q μ)

def generatedOrderClasses (q : ℕ) : Finset ℕ :=
  maskRows.image (generatedGroupOrder q)

def generatedOrderClassRows (q : ℕ) (n : ℕ) : MaskRows :=
  classicalFilter (fun μ => generatedGroupOrder q μ = n) maskRows

def generatedOrderMultiplicityProfile (q : ℕ) : Multiset ℕ :=
  Multiset.map (fun n => (generatedOrderClassRows q n).card)
    (generatedOrderClasses q).1

def expectedGeneratedOrderMultiplicities : Multiset ℕ :=
  Multiset.ofList [1, 1, 2, 4, 8, 16, 32, 64, 128]

/-- The two-prime mask, sign-rank, conjugacy, and generated-order census. -/
def claim38257 : Prop :=
  Fintype.card Mask = 256 ∧
    (∀ q : ℕ, q = 5 ∨ q = 7 →
      (nonconstantRows.card = 254) ∧
      (constantRows.card = 2) ∧
      (nonconstantNonconjugateRows q).card = 254 ∧
      (constantConjugateRows q).card = 2 ∧
      (∀ μ : Mask, ¬ constantMask μ →
        ¬ conjugateWithinGenerated q μ) ∧
      (∀ μ : Mask, constantMask μ →
        conjugateWithinGenerated q μ) ∧
      (generatedOrderMultiplicityProfile q =
        expectedGeneratedOrderMultiplicities)) ∧
    (rankRowsAcrossPrimes 0).card = 4 ∧
    (rankRowsAcrossPrimes 1).card = 4 ∧
    (rankRowsAcrossPrimes 2).card = 8 ∧
    (rankRowsAcrossPrimes 3).card = 16 ∧
    (rankRowsAcrossPrimes 4).card = 32 ∧
    (rankRowsAcrossPrimes 5).card = 64 ∧
    (rankRowsAcrossPrimes 6).card = 128 ∧
    (rankRowsAcrossPrimes 7).card = 256

end

end MathlibPlus.Open.Research.GeneratedGroupCensus
