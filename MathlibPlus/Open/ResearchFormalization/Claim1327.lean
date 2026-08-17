import Mathlib.NumberTheory.PrimeCounting

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Claim1327

def primeCountReal (x : ℝ) : ℝ :=
  (Nat.primeCounting ⌊x⌋₊ : ℝ)

def denominator (c x : ℝ) : ℝ :=
  Real.log x - 1 - c / Real.log x

def leastValidStart (c : ℝ) (N : ℕ) : Prop :=
  (∀ x : ℝ, (N : ℝ) ≤ x →
    primeCountReal x < x / denominator c x) ∧
    (∀ M : ℕ, M < N →
      ¬ (∀ x : ℝ, (M : ℝ) ≤ x →
        primeCountReal x < x / denominator c x))

def correctedCoefficientTable : Fin 42 → ℝ :=
  ![
    (111 : ℝ) / 100, (2221 : ℝ) / 2000, (1111 : ℝ) / 1000,
    (1112 : ℝ) / 1000, (1113 : ℝ) / 1000, (1114 : ℝ) / 1000,
    (1115 : ℝ) / 1000, (1116 : ℝ) / 1000, (1117 : ℝ) / 1000,
    (1118 : ℝ) / 1000, (1119 : ℝ) / 1000, (112 : ℝ) / 100,
    (1121 : ℝ) / 1000, (1122 : ℝ) / 1000, (1123 : ℝ) / 1000,
    (1124 : ℝ) / 1000, (1125 : ℝ) / 1000, (1126 : ℝ) / 1000,
    (1127 : ℝ) / 1000, (1128 : ℝ) / 1000, (1129 : ℝ) / 1000,
    (113 : ℝ) / 100, (1131 : ℝ) / 1000, (1132 : ℝ) / 1000,
    (1133 : ℝ) / 1000, (1134 : ℝ) / 1000, (1135 : ℝ) / 1000,
    (1136 : ℝ) / 1000, (1137 : ℝ) / 1000, (1138 : ℝ) / 1000,
    (1139 : ℝ) / 1000, (114 : ℝ) / 100, (1141 : ℝ) / 1000,
    (1142 : ℝ) / 1000, (1143 : ℝ) / 1000, (1144 : ℝ) / 1000,
    (1145 : ℝ) / 1000, (1146 : ℝ) / 1000, (1147 : ℝ) / 1000,
    (1148 : ℝ) / 1000, (1149 : ℝ) / 1000, (115 : ℝ) / 100]

def correctedStartTable : Fin 42 → ℕ :=
  ![
    62998850942976, 55193608062217, 49246036992716,
    38472138880411, 30658643813468, 23767640743883,
    19278513358342, 15142627022527, 12279648138508,
    9684114630824, 7981446192206, 6323967140812,
    5273225700761, 4170462893841, 3458549136539,
    2825539807244, 2292448124593, 1903596231542,
    1573767234188, 1290096268844, 1073403839693,
    889377392161, 782989678664, 608408258090,
    540050850157, 452875824702, 373479021700,
    335562521091, 263728502964, 242118904367,
    201924836111, 161054192492, 149061190565,
    125233112846, 105053836224, 86061321374,
    77278924451, 61344524412, 57720831343,
    46039922948, 42575222505, 38284442297]

def finalEquality (c x : ℝ) : Prop :=
  primeCountReal x = x / denominator c x

/-- Every corrected-table row and the supplementary 1.14900031 repair has a
least integer start and exactly one equality in the open predecessor unit
interval. -/
def uniqueFinalRealEquality_claim1327 : Prop :=
  (∀ i : Fin 42,
    leastValidStart (correctedCoefficientTable i) (correctedStartTable i) ∧
      ∃! x : ℝ,
        (correctedStartTable i : ℝ) - 1 < x ∧
          x < (correctedStartTable i : ℝ) ∧
          finalEquality (correctedCoefficientTable i) x) ∧
    leastValidStart ((114900031 : ℝ) / 100000000) 42575222481 ∧
      ∃! x : ℝ,
        (42575222481 : ℝ) - 1 < x ∧
          x < 42575222481 ∧
          finalEquality ((114900031 : ℝ) / 100000000) x

end MathlibPlus.Open.ResearchFormalization.Claim1327
