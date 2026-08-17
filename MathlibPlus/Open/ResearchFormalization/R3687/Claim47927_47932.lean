import MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7

namespace MathlibPlus.Open.ResearchFormalization.R3687

open MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7

def signedCode {h : ℕ} (ε : Fin h → ℤ) : ℤ :=
  ∑ i : Fin h, ε i * (2 : ℤ) ^ (h - i.val - 1)

def signedMoment {h : ℕ} (ε : Fin h → ℤ) : ℤ :=
  ∑ i : Fin h, (i.val + 1 : ℤ) * ε i * (2 : ℤ) ^ (h - i.val - 1)

def wordModulus (h : ℕ) : ℤ := (2 : ℤ) ^ h - 1

def leftEndpointShift {h : ℕ} (ε : Fin h → ℤ) : Fin h → ℤ :=
  fun i => (List.rotate (List.ofFn ε) 1).getD i.val 0

def rightEndpointShift {h : ℕ} (ε : Fin h → ℤ) : Fin h → ℤ :=
  fun i => (List.rotate (List.ofFn ε) (h - 1)).getD i.val 0

def complementedWord {h : ℕ} (ε : Fin h → ℤ) : Fin h → ℤ :=
  fun i => -ε i

def centralBalance (k h : ℕ) (ε : Fin h → ℤ) : Prop :=
  (k : ℤ) * signedCode ε + signedMoment ε = 0

def admittedCentralReturnData
    (k h : ℕ) (ε : Fin h → ℤ) (S : Fin (h + 1) → ℤ) : Prop :=
  MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7.firstCentralReturn
      k h ε S ∧
    centralBalance k h ε ∧
    1 ≤ signedCode ε ∧
    signedCode ε ≤ (wordModulus h - 1) / 2

def lastWordSign {h : ℕ} (ε : Fin h → ℤ) : ℤ :=
  (List.ofFn ε).getD (h - 1) 0

def leftEndpointShiftObstruction_claim47927 : Prop :=
  ∀ (k h : ℕ) (ε : Fin h → ℤ) (S : Fin (h + 1) → ℤ),
    2 ≤ h →
      admittedCentralReturnData k h ε S →
        let C := signedCode ε
        let B := signedMoment ε
        let M := wordModulus h
        let K : ℤ := (k + h : ℕ)
        let L := leftEndpointShift ε
        let C_L := signedCode L
        let B_L := signedMoment L
        C_L = 2 * C - M ∧
          B_L = 2 * B - 2 * C + h ∧
          K * C_L + B_L = 2 * (h - 1) * C - K * M + h ∧
          K * C_L + B_L < 0 ∧
          ¬ centralBalance (k + h) h L

def leftRightEndpointShiftObstruction_claim47932 : Prop :=
  ∀ (k h : ℕ) (ε : Fin h → ℤ) (S : Fin (h + 1) → ℤ),
    2 ≤ h →
      admittedCentralReturnData k h ε S →
        let C := signedCode ε
        let B := signedMoment ε
        let M := wordModulus h
        let K : ℤ := (k + h : ℕ)
        let L := leftEndpointShift ε
        let R := rightEndpointShift ε
        let C_R := signedCode R
        let B_R := signedMoment R
        let ε_h := lastWordSign ε
        2 * C_R = C + ε_h * M ∧
          2 * B_R = B + C + ε_h * (M - h) ∧
          2 * (K * C_R + B_R) =
            (h + 1) * C + ε_h * ((K + 1) * M - h) ∧
          |(h + 1) * C| < |((K + 1) * M - h)| ∧
          (∀ e : ℤ, e = -1 ∨ e = 1 →
            (h + 1) * C + e * ((K + 1) * M - h) ≠ 0) ∧
          K * C_R + B_R ≠ 0 ∧
          ¬ centralBalance (k + h) h R ∧
          ¬ centralBalance (k + h) h (complementedWord R) ∧
          ¬ centralBalance (k + h) h (complementedWord L)

end MathlibPlus.Open.ResearchFormalization.R3687
