import MathlibPlus.Open.Analysis.PrimeCountingRepairs

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

noncomputable section

open MathlibPlus.Open.Analysis

/-- The literal 28-row table in Claim 976, with decimal coefficients and
repairs represented by their exact rational values. -/
def exactTwentyEightAuditRows_claim976 : List AuditRow :=
  [ { publishedCoeff := (1072 : ℝ) / 1000
      start := 18339738
      piStart := 1171675
      optimizer := 18339738
      piOptimizer := 1171675
      repair := (1071999606 : ℝ) / 1000000000 }
  , { publishedCoeff := (1073 : ℝ) / 1000
      start := 13026859
      piStart := 850899
      optimizer := 13026859
      piOptimizer := 850899
      repair := (1072999464 : ℝ) / 1000000000 }
  , { publishedCoeff := (1074 : ℝ) / 1000
      start := 12895928
      piStart := 842958
      optimizer := 12895928
      piOptimizer := 842958
      repair := (1073999227 : ℝ) / 1000000000 }
  , { publishedCoeff := (1075 : ℝ) / 1000
      start := 8832927
      piStart := 592059
      optimizer := 8832927
      piOptimizer := 592059
      repair := (1074999064 : ℝ) / 1000000000 }
  , { publishedCoeff := (1076 : ℝ) / 1000
      start := 7299254
      piStart := 495628
      optimizer := 7299254
      piOptimizer := 495628
      repair := (1075999344 : ℝ) / 1000000000 }
  , { publishedCoeff := (1077 : ℝ) / 1000
      start := 7117256
      piStart := 484133
      optimizer := 7117303
      piOptimizer := 484136
      repair := (1076998803 : ℝ) / 1000000000 }
  , { publishedCoeff := (1078 : ℝ) / 1000
      start := 5465656
      piStart := 378613
      optimizer := 5465671
      piOptimizer := 378614
      repair := (1077999313 : ℝ) / 1000000000 }
  , { publishedCoeff := (1079 : ℝ) / 1000
      start := 4994010
      piStart := 348142
      optimizer := 4994010
      piOptimizer := 348142
      repair := (1078999622 : ℝ) / 1000000000 }
  , { publishedCoeff := (1080 : ℝ) / 1000
      start := 3462478
      piStart := 247718
      optimizer := 3462478
      piOptimizer := 247718
      repair := (1079996469 : ℝ) / 1000000000 }
  , { publishedCoeff := (1081 : ℝ) / 1000
      start := 3455648
      piStart := 247282
      optimizer := 3455648
      piOptimizer := 247282
      repair := (1080997538 : ℝ) / 1000000000 }
  , { publishedCoeff := (1082 : ℝ) / 1000
      start := 2279177
      piStart := 168114
      optimizer := 2279177
      piOptimizer := 168114
      repair := (1081994826 : ℝ) / 1000000000 }
  , { publishedCoeff := (1083 : ℝ) / 1000
      start := 1529630
      piStart := 116255
      optimizer := 1529630
      piOptimizer := 116255
      repair := (1082994823 : ℝ) / 1000000000 }
  , { publishedCoeff := (1084 : ℝ) / 1000
      start := 1525432
      piStart := 115969
      optimizer := 1525432
      piOptimizer := 115969
      repair := (1083997108 : ℝ) / 1000000000 }
  , { publishedCoeff := (1085 : ℝ) / 1000
      start := 1515074
      piStart := 115250
      optimizer := 1515074
      piOptimizer := 115250
      repair := (1084996533 : ℝ) / 1000000000 }
  , { publishedCoeff := (1086 : ℝ) / 1000
      start := 1200014
      piStart := 92939
      optimizer := 1200014
      piOptimizer := 92939
      repair := (1085998378 : ℝ) / 1000000000 }
  , { publishedCoeff := (1087 : ℝ) / 1000
      start := 1195296
      piStart := 92609
      optimizer := 1195296
      piOptimizer := 92609
      repair := (1086994716 : ℝ) / 1000000000 }
  , { publishedCoeff := (1088 : ℝ) / 1000
      start := 624878
      piStart := 50980
      optimizer := 624878
      piOptimizer := 50980
      repair := (1087995115 : ℝ) / 1000000000 }
  , { publishedCoeff := (1089 : ℝ) / 1000
      start := 618726
      piStart := 50523
      optimizer := 618726
      piOptimizer := 50523
      repair := (1088995383 : ℝ) / 1000000000 }
  , { publishedCoeff := (1090 : ℝ) / 1000
      start := 618058
      piStart := 50477
      optimizer := 618058
      piOptimizer := 50477
      repair := (1089988672 : ℝ) / 1000000000 }
  , { publishedCoeff := (1091 : ℝ) / 1000
      start := 445112
      piStart := 37357
      optimizer := 445112
      piOptimizer := 37357
      repair := (1090991674 : ℝ) / 1000000000 }
  , { publishedCoeff := (1092 : ℝ) / 1000
      start := 359804
      piStart := 30749
      optimizer := 359804
      piOptimizer := 30749
      repair := (1091991098 : ℝ) / 1000000000 }
  , { publishedCoeff := (1093 : ℝ) / 1000
      start := 356203
      piStart := 30470
      optimizer := 356203
      piOptimizer := 30470
      repair := (1092970546 : ℝ) / 1000000000 }
  , { publishedCoeff := (1094 : ℝ) / 1000
      start := 355990
      piStart := 30456
      optimizer := 355990
      piOptimizer := 30456
      repair := (1093992304 : ℝ) / 1000000000 }
  , { publishedCoeff := (1095 : ℝ) / 1000
      start := 355177
      piStart := 30395
      optimizer := 355177
      piOptimizer := 30395
      repair := (1094995652 : ℝ) / 1000000000 }
  , { publishedCoeff := (1096 : ℝ) / 1000
      start := 155935
      piStart := 14357
      optimizer := 155935
      piOptimizer := 14357
      repair := (1095942182 : ℝ) / 1000000000 }
  , { publishedCoeff := (1097 : ℝ) / 1000
      start := 155907
      piStart := 14356
      optimizer := 155907
      piOptimizer := 14356
      repair := (1096956443 : ℝ) / 1000000000 }
  , { publishedCoeff := (1098 : ℝ) / 1000
      start := 60297
      piStart := 6085
      optimizer := 60297
      piOptimizer := 6085
      repair := (1097916842 : ℝ) / 1000000000 }
  , { publishedCoeff := (1099 : ℝ) / 1000
      start := 60224
      piStart := 6079
      optimizer := 60224
      piOptimizer := 6079
      repair := (1098933642 : ℝ) / 1000000000 }
  ]

/-- Axler's score `A(x) = log x - x / pi(x)` on the reviewed real
prime-counting carrier. -/
def auditScore_claim976 (x : ℝ) : ℝ :=
  Real.log x - x / primeCountingReal x

/-- The exact count, sharp-coefficient, and unique-optimizer content attached
 to one row of the table.  The displayed decimal for `a*` is represented by
 its exact defining expression, since the source display is ellipsized. -/
def exactAuditRowData_claim976 (r : AuditRow) : Prop :=
  primeCountingReal (r.start : ℝ) = (r.piStart : ℝ) ∧
    primeCountingReal (r.optimizer : ℝ) = (r.piOptimizer : ℝ) ∧
    sharpCoefficient r =
      Real.log (r.optimizer : ℝ) - (r.optimizer : ℝ) / (r.piOptimizer : ℝ) ∧
    sharpCoefficient r = auditScore_claim976 (r.optimizer : ℝ) ∧
    (∀ x : ℝ, (r.start : ℝ) ≤ x →
      auditScore_claim976 x ≤ sharpCoefficient r ∧
        (auditScore_claim976 x = sharpCoefficient r ↔
          x = (r.optimizer : ℝ)))

/-- Claim 976: the exact 28-row published audit table. -/
def exactTwentyEightRowAuditData_claim976 : Prop :=
  auditRows = exactTwentyEightAuditRows_claim976 ∧
    auditRows.length = 28 ∧
    ∀ r ∈ auditRows, exactAuditRowData_claim976 r

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
