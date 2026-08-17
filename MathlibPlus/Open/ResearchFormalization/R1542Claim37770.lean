import MathlibPlus.Open.ResearchBatch.R1542Claims

namespace MathlibPlus.Open.ResearchFormalization.R1542Claim37770

noncomputable section

abbrev W (p : Nat) :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.W p
abbrev H (p : Nat) :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.H p
abbrev G (p : Nat) :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.G p

def hMul {p : Nat} (omega : ZMod p) (x y : H p) : H p :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.hMul omega x y

def hInv {p : Nat} (omega : ZMod p) (x : H p) : H p :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.hInv omega x

def hZero {p : Nat} : H p :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.hZero

def gMul {p : Nat} (omega : ZMod p) (x y : G p) : G p :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.gMul omega x y

def gInv {p : Nat} (omega : ZMod p) (x : G p) : G p :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.gInv omega x

def gZero {p : Nat} : G p :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.gZero

def scalarCubeRoot {p : Nat} (omega : ZMod p) : Prop :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.scalarCubeRoot omega

def hSlope {p : Nat} (omega : ZMod p) (t : Fin 5) : H p :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.hSlope omega t

def marker {p : Nat} : Set (W p) :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.marker

def sourceConnection {p : Nat} (omega : ZMod p) : Set (G p) :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.sourceConnection omega

def targetConnection {p : Nat} (omega : ZMod p) : Set (G p) :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.targetConnection omega

def identityFree {p : Nat} (S : Set (G p)) : Prop :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.identityFree S

def inverseClosed {p : Nat} (omega : ZMod p) (S : Set (G p)) : Prop :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.inverseClosed omega S

def connectedCayley {p : Nat} (omega : ZMod p) (S : Set (G p)) : Prop :=
  MathlibPlus.Open.ResearchBatch.R1542Claims.connectedCayley omega S

def wordProduct {p : Nat} (omega : ZMod p) : List (G p) → G p
  | [] => gZero
  | x :: xs => gMul omega x (wordProduct omega xs)

def inGenerated {p : Nat} (omega : ZMod p)
    (S : Set (G p)) (x : G p) : Prop :=
  ∃ words : List (G p),
    (∀ z, z ∈ words → z ∈ S ∨ gInv omega z ∈ S) ∧
      wordProduct omega words = x

def hWordProduct {p : Nat} (omega : ZMod p) : List (H p) → H p
  | [] => hZero
  | x :: xs => hMul omega x (hWordProduct omega xs)

def inHGenerated {p : Nat} (omega : ZMod p)
    (S : Set (H p)) (x : H p) : Prop :=
  ∃ words : List (H p),
    (∀ z, z ∈ words → z ∈ S ∨ hInv omega z ∈ S) ∧
      hWordProduct omega words = x

def inLinearSpan {p : Nat} (S : Set (W p)) (x : W p) : Prop :=
  ∃ n : Nat, ∃ coefficients : Fin n → ZMod p,
    ∃ vectors : Fin n → W p,
      (∀ i, vectors i ∈ S) ∧
        x = ∑ i, coefficients i • vectors i

/-- Claim 37770: the exact marker, slope-generator, connection-set, and
connectedness conclusions for every admissible prime. -/
def claim_37770 : Prop :=
  ∀ p : Nat, Nat.Prime p → p % 3 = 1 →
    ∀ omega : ZMod p, scalarCubeRoot omega →
      let S := sourceConnection omega
      let T := targetConnection omega
      identityFree S ∧ identityFree T ∧
        inverseClosed omega S ∧ inverseClosed omega T ∧
          Set.ncard S = 10 * p ^ 2 + 10 ∧
            Set.ncard T = 10 * p ^ 2 + 10 ∧
              (∀ x : W p, inLinearSpan marker x) ∧
                (∀ h : H p,
                  inHGenerated omega
                    ({hSlope omega (0 : Fin 5), hSlope omega (1 : Fin 5)} : Set (H p)) h) ∧
                  (∀ x : G p, inGenerated omega S x) ∧
                    (∀ x : G p, inGenerated omega T x) ∧
                      connectedCayley omega S ∧ connectedCayley omega T

end

end MathlibPlus.Open.ResearchFormalization.R1542Claim37770
