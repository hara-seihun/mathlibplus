import MathlibPlus.Open.ResearchFormalization.R0334Claim20014

namespace MathlibPlus.Open.ResearchFormalization.R0334Claim20016

open scoped BigOperators

noncomputable section

/-- The exact Record 13 mask expansion used by the reviewed carrier. -/
def record13ExpandMask (mask : ℕ) : ℕ :=
  (if mask.testBit 0 = true then 1 else 0) +
    (if mask.testBit 1 = true then 14 else 0) +
    (if mask.testBit 2 = true then 112 else 0) +
    (if mask.testBit 3 = true then 128 else 0)

/-- The eight exact trace fibers of Record 13. -/
def record13Base : Fin 8 → Finset ℕ :=
  ![
    ({0, 2, 4, 6, 13, 15} : Finset ℕ),
    ({2, 4, 6, 13, 15} : Finset ℕ),
    ({2, 4, 6, 13, 15} : Finset ℕ),
    ({2, 4, 6, 13, 15} : Finset ℕ),
    ({2, 6, 13, 14, 15} : Finset ℕ),
    ({2, 6, 13, 14, 15} : Finset ℕ),
    ({2, 6, 13, 14, 15} : Finset ℕ),
    ({2, 6, 13, 14, 15} : Finset ℕ)
  ]

def record13Common : Finset ℕ :=
  {22, 30, 50, 54, 62, 114, 118, 243, 247}

def record13Fiber (trace : Fin 8) : Finset ℕ :=
  (record13Base trace).image record13ExpandMask ∪ record13Common

def record13Family : Finset ℕ :=
  Finset.univ.biUnion (fun trace : Fin 8 =>
    (record13Fiber trace).image (fun outside => trace.val + 8 * outside))

/-- Frequency and deficit use the exact eleven-bit coordinate carrier and the
    reviewed convention `|F| - 2 f`. -/
def record13Frequency (coordinate : Fin 11) : ℤ :=
  Int.ofNat ((record13Family.filter (fun member =>
    member.testBit coordinate.val = true)).card)

def record13Deficit (coordinate : Fin 11) : ℤ :=
  (record13Family.card : ℤ) - 2 * record13Frequency coordinate

/-- The five outside coordinates are `a₁,a₂,b₁,b₂,b₃` in the reviewed order. -/
def record13OutsideCoordinates : Fin 5 → Fin 11 :=
  ![4, 5, 7, 8, 9]

/-- Claim 20016: the five displayed outside coordinates have negative deficit
    and strict-above-half frequency in the exact 113-member Record 13 family. -/
def fiveOutsideCoordinatesAreAbundant_claim20016 : Prop :=
  record13Family.card = 113 ∧
    (∀ i : Fin 5,
      record13Frequency (record13OutsideCoordinates i) =
        (![100, 76, 104, 88, 64] : Fin 5 → ℤ) i) ∧
    (∀ i : Fin 5,
      record13Deficit (record13OutsideCoordinates i) =
        (![-87, -39, -95, -63, -15] : Fin 5 → ℤ) i) ∧
    (∀ i : Fin 5,
      record13Deficit (record13OutsideCoordinates i) < 0 ∧
        2 * record13Frequency (record13OutsideCoordinates i) >
          (record13Family.card : ℤ))

end

end MathlibPlus.Open.ResearchFormalization.R0334Claim20016
