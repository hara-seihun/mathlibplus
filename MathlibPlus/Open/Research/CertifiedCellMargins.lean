import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research

/-- The prime-counting function on real arguments, obtained by the usual floor extension. -/
def primeCountingReal (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ)

/-- The pole-cancelled prime-counting score from the admitted claim. -/
def B (x : ℝ) : ℝ :=
  Real.log x * (Real.log x - 1 - x / primeCountingReal x)

/-- The upper cell value `α(N) = max_{x ≥ N} B(x)`, represented by its supremum. -/
noncomputable def alpha (N : ℕ) : ℝ :=
  sSup (B '' Set.Ici (N : ℝ))

/-- The lower cell value `β(N) = B(N - 1)`. -/
def beta (N : ℕ) : ℝ :=
  B ((N - 1 : ℕ) : ℝ)

/-- The 42 corrected rows and the supplementary repair row. -/
def cells : Finset (ℚ × ℕ) :=
  {(111 / 100, 62998850942976),
   (11105 / 10000, 55193608062217),
   (1111 / 1000, 49246036992716),
   (1112 / 1000, 38472138880411),
   (1113 / 1000, 30658643813468),
   (1114 / 1000, 23767640743883),
   (1115 / 1000, 19278513358342),
   (1116 / 1000, 15142627022527),
   (1117 / 1000, 12279648138508),
   (1118 / 1000, 9684114630824),
   (1119 / 1000, 7981446192206),
   (112 / 100, 6323967140812),
   (1121 / 1000, 5273225700761),
   (1122 / 1000, 4170462893841),
   (1123 / 1000, 3458549136539),
   (1124 / 1000, 2825539807244),
   (1125 / 1000, 2292448124593),
   (1126 / 1000, 1903596231542),
   (1127 / 1000, 1573767234188),
   (1128 / 1000, 1290096268844),
   (1129 / 1000, 1073403839693),
   (113 / 100, 889377392161),
   (1131 / 1000, 782989678664),
   (1132 / 1000, 608408258090),
   (1133 / 1000, 540050850157),
   (1134 / 1000, 452875824702),
   (1135 / 1000, 373479021700),
   (1136 / 1000, 335562521091),
   (1137 / 1000, 263728502964),
   (1138 / 1000, 242118904367),
   (1139 / 1000, 201924836111),
   (114 / 100, 161054192492),
   (1141 / 1000, 149061190565),
   (1142 / 1000, 125233112846),
   (1143 / 1000, 105053836224),
   (1144 / 1000, 86061321374),
   (1145 / 1000, 77278924451),
   (1146 / 1000, 61344524412),
   (1147 / 1000, 57720831343),
   (1148 / 1000, 46039922948),
   (1149 / 1000, 42575222505),
   (115 / 100, 38284442297),
   (114900031 / 100000000, 42575222481)}

def widthMargin (cell : ℚ × ℕ) : ℝ :=
  beta cell.2 - alpha cell.2

def lowerInteriorMargin (cell : ℚ × ℕ) : ℝ :=
  (cell.1 : ℝ) - alpha cell.2

def upperInteriorMargin (cell : ℚ × ℕ) : ℝ :=
  beta cell.2 - (cell.1 : ℝ)

noncomputable def minWidthMargin : ℝ :=
  sInf (widthMargin '' (cells : Set (ℚ × ℕ)))

noncomputable def minLowerInteriorMargin : ℝ :=
  sInf (lowerInteriorMargin '' (cells : Set (ℚ × ℕ)))

noncomputable def minUpperInteriorMargin : ℝ :=
  sInf (upperInteriorMargin '' (cells : Set (ℚ × ℕ)))

/-- Certified widths and interior margins for all 43 admitted cells. -/
def certifiedCellWidthAndInteriorMargins : Prop :=
  minWidthMargin >
      (14998727706977673 : ℝ) / ((10 : ℝ) ^ 27) ∧
    minLowerInteriorMargin >
      (55651560581617361 : ℝ) / ((10 : ℝ) ^ 28) ∧
    minUpperInteriorMargin >
      (99383965519562590 : ℝ) / ((10 : ℝ) ^ 29)

end MathlibPlus.Open.Research
