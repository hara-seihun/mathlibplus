import MathlibPlus.Open.GraphTheory.C3SquareD10Facts
import MathlibPlus.Open.Research.FormalizationBatch1113_1116

namespace MathlibPlus.Open.GraphTheory.R2268Claim43738

open scoped BigOperators
open MathlibPlus.Open.GraphTheory
open MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

abbrev G := C3SquaredD10
abbrev ConnectionSet := connectionSets G
abbrev FullAut := MulAut G

/-- The valency of an exact identity-free inverse-closed connection set. -/
def connectionSetValency (S : ConnectionSet) : ℕ := S.1.card

def fixedWeightInput (k : ℕ) :=
  {S : ConnectionSet // connectionSetValency S = k}

abbrev fullAutOrbitQuotient :=
  Quotient (MulAction.orbitRel FullAut ConnectionSet)

def fullAutOrbitSlice (k : ℕ) :=
  {q : fullAutOrbitQuotient //
    ∃ S : ConnectionSet,
      connectionSetValency S = k ∧
        Quotient.mk (MulAction.orbitRel FullAut ConnectionSet) S = q}

/-- The literal complement inside the nonidentity elements of the fixed group. -/
def connectionComplement43738 (S : ConnectionSet) : Finset G :=
  (Finset.univ.erase (1 : G)) \ S.1

structure PreflightRow43738 where
  lowValency : ℕ
  complementValency : ℕ
  rawCount : ℕ
  orbitCount : ℕ
  benchmarkSeconds : ℝ

noncomputable def preflightRows43738 : Fin 7 → PreflightRow43738 :=
  ![
    { lowValency := 35, complementValency := 54,
      rawCount := 3037079279416, orbitCount := 3205691828,
      benchmarkSeconds := 262745655 / 1000 },
    { lowValency := 36, complementValency := 53,
      rawCount := 3732865000620, orbitCount := 3939982064,
      benchmarkSeconds := 651847720 / 1000 },
    { lowValency := 37, complementValency := 52,
      rawCount := 4481614598412, orbitCount := 4723716045,
      benchmarkSeconds := 415187440 / 1000 },
    { lowValency := 38, complementValency := 51,
      rawCount := 5257056157080, orbitCount := 5540922485,
      benchmarkSeconds := 842459544 / 1000 },
    { lowValency := 39, complementValency := 50,
      rawCount := 6025509691656, orbitCount := 6344900398,
      benchmarkSeconds := 599571362 / 1000 },
    { lowValency := 40, complementValency := 49,
      rawCount := 6750030320670, orbitCount := 7107724465,
      benchmarkSeconds := 994382337 / 1000 },
    { lowValency := 41, complementValency := 48,
      rawCount := 7390408266150, orbitCount := 7777498523,
      benchmarkSeconds := 791975518 / 1000 }
  ]

def preflightRowFacts43738 (row : PreflightRow43738) : Prop :=
  row.complementValency = 89 - row.lowValency ∧
    Nat.card (fixedWeightInput row.lowValency) = row.rawCount ∧
      Nat.card (fullAutOrbitSlice row.lowValency) = row.orbitCount ∧
        ∀ S : fixedWeightInput row.lowValency,
          (1 : G) ∉ connectionComplement43738 S.1 ∧
            (∀ g : G,
              g ∈ connectionComplement43738 S.1 ↔
                g⁻¹ ∈ connectionComplement43738 S.1) ∧
              (connectionComplement43738 S.1).card = row.complementValency

/-- The seven fixed-weight counts, their full-automorphism orbit counts, and
 the retained benchmark-throughput workload are attached to the exact finite
 connection-set and orbit carriers. -/
def claim43738 : Prop :=
  (∀ i : Fin 7, preflightRowFacts43738 (preflightRows43738 i)) ∧
    Function.Injective (fun i : Fin 7 => (preflightRows43738 i).lowValency) ∧
      (∑ i : Fin 7, (preflightRows43738 i).benchmarkSeconds) =
        (4558169576 / 1000 : ℝ)

end

end MathlibPlus.Open.GraphTheory.R2268Claim43738
