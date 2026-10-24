import TwelveHubCodes
import PairCodeOverlap

/-! The full upper main interval from order43, using existing explicit
families. Every finite parameter and interval overlap is kernel checked. -/
namespace Delivery.MainOverlapFortyThree
open Extremal

theorem maximum43 {m : Nat} (low : 129≤m) (high : m≤1720) :
    IsMaximum 43 m (1806-m) := by
  by_cases h0 : m≤258
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤774
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤774; omega)
  by_cases h2 : m≤1455
  · exact TwelveHubCodes.maximum (g:=8) (b:=23) (r:=2) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=9) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum44 {m : Nat} (low : 132≤m) (high : m≤1804) :
    IsMaximum 44 m (1892-m) := by
  by_cases h0 : m≤264
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤924
  · exact CircleConstruction.full_maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h2 : m≤1626
  · exact TwelveHubCodes.maximum (g:=8) (b:=24) (r:=6) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=9) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum45 {m : Nat} (low : 135≤m) (high : m≤1890) :
    IsMaximum 45 m (1980-m) := by
  by_cases h0 : m≤270
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤855
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤855; omega)
  by_cases h2 : m≤1664
  · exact TwelveHubCodes.maximum (g:=7) (b:=26) (r:=3) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=9) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum46 {m : Nat} (low : 138≤m) (high : m≤1978) :
    IsMaximum 46 m (2070-m) := by
  by_cases h0 : m≤276
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤874
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤874; omega)
  by_cases h2 : m≤1745
  · exact TwelveHubCodes.maximum (g:=7) (b:=27) (r:=3) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=9) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum47 {m : Nat} (low : 141≤m) (high : m≤2068) :
    IsMaximum 47 m (2162-m) := by
  by_cases h0 : m≤282
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤940
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤940; omega)
  by_cases h2 : m≤1856
  · exact TwelveHubCodes.maximum (g:=7) (b:=28) (r:=4) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=9) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum48 {m : Nat} (low : 144≤m) (high : m≤2160) :
    IsMaximum 48 m (2256-m) := by
  by_cases h0 : m≤288
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1104
  · exact CircleConstruction.full_maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h2 : m≤1962
  · exact TwelveHubCodes.maximum (g:=8) (b:=28) (r:=6) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=9) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum49 {m : Nat} (low : 147≤m) (high : m≤2254) :
    IsMaximum 49 m (2352-m) := by
  by_cases h0 : m≤294
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤931
  · exact CircleGuardedConstruction.maximum (h:=11) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤931; omega)
  by_cases h2 : m≤2000
  · exact TwelveHubCodes.maximum (g:=7) (b:=30) (r:=3) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=9) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum50 {m : Nat} (low : 150≤m) (high : m≤2350) :
    IsMaximum 50 m (2450-m) := by
  by_cases h0 : m≤350
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1050
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤1050; omega)
  by_cases h2 : m≤2120
  · exact TwelveHubCodes.maximum (g:=7) (b:=31) (r:=4) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=9) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum51 {m : Nat} (low : 153≤m) (high : m≤2448) :
    IsMaximum 51 m (2550-m) := by
  by_cases h0 : m≤357
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1122
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤1122; omega)
  by_cases h2 : m≤2212
  · exact TwelveHubCodes.maximum (g:=7) (b:=32) (r:=4) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=9) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum52 {m : Nat} (low : 156≤m) (high : m≤2548) :
    IsMaximum 52 m (2652-m) := by
  by_cases h0 : m≤364
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1300
  · exact CircleConstruction.full_maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h2 : m≤2306
  · exact TwelveHubCodes.maximum (g:=7) (b:=33) (r:=4) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=9) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum53 {m : Nat} (low : 159≤m) (high : m≤2650) :
    IsMaximum 53 m (2756-m) := by
  by_cases h0 : m≤371
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1219
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤1219; omega)
  by_cases h2 : m≤2402
  · exact TwelveHubCodes.maximum (g:=7) (b:=34) (r:=4) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=9) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum54 {m : Nat} (low : 162≤m) (high : m≤2754) :
    IsMaximum 54 m (2862-m) := by
  by_cases h0 : m≤378
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1242
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤1242; omega)
  by_cases h2 : m≤2500
  · exact TwelveHubCodes.maximum (g:=7) (b:=35) (r:=4) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=9) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum55 {m : Nat} (low : 165≤m) (high : m≤2860) :
    IsMaximum 55 m (2970-m) := by
  by_cases h0 : m≤385
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1320
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤1320; omega)
  by_cases h2 : m≤2592
  · exact TwelveHubCodes.maximum (g:=8) (b:=35) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum56 {m : Nat} (low : 168≤m) (high : m≤2968) :
    IsMaximum 56 m (3080-m) := by
  by_cases h0 : m≤392
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1512
  · exact CircleConstruction.full_maximum (h:=11) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h2 : m≤2694
  · exact TwelveHubCodes.maximum (g:=8) (b:=36) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum57 {m : Nat} (low : 171≤m) (high : m≤3078) :
    IsMaximum 57 m (3192-m) := by
  by_cases h0 : m≤456
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1425
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤1425; omega)
  by_cases h2 : m≤2798
  · exact TwelveHubCodes.maximum (g:=8) (b:=37) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum58 {m : Nat} (low : 174≤m) (high : m≤3190) :
    IsMaximum 58 m (3306-m) := by
  by_cases h0 : m≤464
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1450
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤1450; omega)
  by_cases h2 : m≤2904
  · exact TwelveHubCodes.maximum (g:=8) (b:=38) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum59 {m : Nat} (low : 177≤m) (high : m≤3304) :
    IsMaximum 59 m (3422-m) := by
  by_cases h0 : m≤472
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1534
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤1534; omega)
  by_cases h2 : m≤3012
  · exact TwelveHubCodes.maximum (g:=8) (b:=39) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum60 {m : Nat} (low : 180≤m) (high : m≤3420) :
    IsMaximum 60 m (3540-m) := by
  by_cases h0 : m≤480
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1740
  · exact CircleConstruction.full_maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h2 : m≤3122
  · exact TwelveHubCodes.maximum (g:=8) (b:=40) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum61 {m : Nat} (low : 183≤m) (high : m≤3538) :
    IsMaximum 61 m (3660-m) := by
  by_cases h0 : m≤488
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1647
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤1647; omega)
  by_cases h2 : m≤3234
  · exact TwelveHubCodes.maximum (g:=8) (b:=41) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum62 {m : Nat} (low : 186≤m) (high : m≤3658) :
    IsMaximum 62 m (3782-m) := by
  by_cases h0 : m≤496
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1674
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤1674; omega)
  by_cases h2 : m≤3348
  · exact TwelveHubCodes.maximum (g:=8) (b:=42) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum63 {m : Nat} (low : 189≤m) (high : m≤3780) :
    IsMaximum 63 m (3906-m) := by
  by_cases h0 : m≤504
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1638
  · exact CircleGuardedConstruction.maximum (h:=11) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤1638; omega)
  by_cases h2 : m≤3464
  · exact TwelveHubCodes.maximum (g:=8) (b:=43) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum64 {m : Nat} (low : 192≤m) (high : m≤3904) :
    IsMaximum 64 m (4032-m) := by
  by_cases h0 : m≤576
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1984
  · exact CircleConstruction.full_maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h2 : m≤3582
  · exact TwelveHubCodes.maximum (g:=8) (b:=44) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum65 {m : Nat} (low : 195≤m) (high : m≤4030) :
    IsMaximum 65 m (4160-m) := by
  by_cases h0 : m≤585
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1885
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤1885; omega)
  by_cases h2 : m≤3702
  · exact TwelveHubCodes.maximum (g:=8) (b:=45) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum66 {m : Nat} (low : 198≤m) (high : m≤4158) :
    IsMaximum 66 m (4290-m) := by
  by_cases h0 : m≤594
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤1914
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤1914; omega)
  by_cases h2 : m≤3824
  · exact TwelveHubCodes.maximum (g:=8) (b:=46) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum67 {m : Nat} (low : 201≤m) (high : m≤4288) :
    IsMaximum 67 m (4422-m) := by
  by_cases h0 : m≤603
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤2010
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤2010; omega)
  by_cases h2 : m≤3948
  · exact TwelveHubCodes.maximum (g:=8) (b:=47) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum68 {m : Nat} (low : 204≤m) (high : m≤4420) :
    IsMaximum 68 m (4556-m) := by
  by_cases h0 : m≤612
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤2244
  · exact CircleConstruction.full_maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum69 {m : Nat} (low : 207≤m) (high : m≤4554) :
    IsMaximum 69 m (4692-m) := by
  by_cases h0 : m≤621
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤2139
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤2139; omega)
  by_cases h2 : m≤4202
  · exact TwelveHubCodes.maximum (g:=8) (b:=49) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum70 {m : Nat} (low : 210≤m) (high : m≤4690) :
    IsMaximum 70 m (4830-m) := by
  by_cases h0 : m≤630
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤2030
  · exact CircleGuardedConstruction.maximum (h:=11) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤2030; omega)
  by_cases h2 : m≤4332
  · exact TwelveHubCodes.maximum (g:=8) (b:=50) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=10) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum71 {m : Nat} (low : 213≤m) (high : m≤4828) :
    IsMaximum 71 m (4970-m) := by
  by_cases h0 : m≤710
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤2272
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤2272; omega)
  by_cases h2 : m≤4464
  · exact TwelveHubCodes.maximum (g:=8) (b:=51) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=11) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum72 {m : Nat} (low : 216≤m) (high : m≤4968) :
    IsMaximum 72 m (5112-m) := by
  by_cases h0 : m≤720
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤2520
  · exact CircleConstruction.full_maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=11) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum73 {m : Nat} (low : 219≤m) (high : m≤5110) :
    IsMaximum 73 m (5256-m) := by
  by_cases h0 : m≤730
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤2409
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤2409; omega)
  by_cases h2 : m≤4734
  · exact TwelveHubCodes.maximum (g:=8) (b:=53) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=11) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum74 {m : Nat} (low : 222≤m) (high : m≤5254) :
    IsMaximum 74 m (5402-m) := by
  by_cases h0 : m≤740
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤2442
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤2442; omega)
  by_cases h2 : m≤4872
  · exact TwelveHubCodes.maximum (g:=8) (b:=54) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=11) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum75 {m : Nat} (low : 225≤m) (high : m≤5400) :
    IsMaximum 75 m (5550-m) := by
  by_cases h0 : m≤750
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤2550
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤2550; omega)
  by_cases h2 : m≤5012
  · exact TwelveHubCodes.maximum (g:=8) (b:=55) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=11) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum76 {m : Nat} (low : 228≤m) (high : m≤5548) :
    IsMaximum 76 m (5700-m) := by
  by_cases h0 : m≤760
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤2812
  · exact CircleConstruction.full_maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=11) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum77 {m : Nat} (low : 231≤m) (high : m≤5698) :
    IsMaximum 77 m (5852-m) := by
  by_cases h0 : m≤770
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤2387
  · exact CircleGuardedConstruction.maximum (h:=15) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤2387; omega)
  by_cases h2 : m≤5241
  · exact TwelveHubCodes.maximum (g:=8) (b:=57) (r:=4) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=11) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum78 {m : Nat} (low : 234≤m) (high : m≤5850) :
    IsMaximum 78 m (6006-m) := by
  by_cases h0 : m≤858
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤2730
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤2730; omega)
  by_cases h2 : m≤5386
  · exact TwelveHubCodes.maximum (g:=8) (b:=58) (r:=4) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=11) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem finite_maximum {n m : Nat} (large : 43≤n) (small : n≤78)
    (low : 3*n≤m) (high : m≤n*(n-3)) : IsMaximum n m (n*(n-1)-m) := by
  have cases : n=43 ∨ n=44 ∨ n=45 ∨ n=46 ∨ n=47 ∨ n=48 ∨ n=49 ∨ n=50 ∨ n=51 ∨ n=52 ∨ n=53 ∨ n=54 ∨ n=55 ∨ n=56 ∨ n=57 ∨ n=58 ∨ n=59 ∨ n=60 ∨ n=61 ∨ n=62 ∨ n=63 ∨ n=64 ∨ n=65 ∨ n=66 ∨ n=67 ∨ n=68 ∨ n=69 ∨ n=70 ∨ n=71 ∨ n=72 ∨ n=73 ∨ n=74 ∨ n=75 ∨ n=76 ∨ n=77 ∨ n=78 := by omega
  rcases cases with h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78
  · subst n; exact maximum43 low high
  · subst n; exact maximum44 low high
  · subst n; exact maximum45 low high
  · subst n; exact maximum46 low high
  · subst n; exact maximum47 low high
  · subst n; exact maximum48 low high
  · subst n; exact maximum49 low high
  · subst n; exact maximum50 low high
  · subst n; exact maximum51 low high
  · subst n; exact maximum52 low high
  · subst n; exact maximum53 low high
  · subst n; exact maximum54 low high
  · subst n; exact maximum55 low high
  · subst n; exact maximum56 low high
  · subst n; exact maximum57 low high
  · subst n; exact maximum58 low high
  · subst n; exact maximum59 low high
  · subst n; exact maximum60 low high
  · subst n; exact maximum61 low high
  · subst n; exact maximum62 low high
  · subst n; exact maximum63 low high
  · subst n; exact maximum64 low high
  · subst n; exact maximum65 low high
  · subst n; exact maximum66 low high
  · subst n; exact maximum67 low high
  · subst n; exact maximum68 low high
  · subst n; exact maximum69 low high
  · subst n; exact maximum70 low high
  · subst n; exact maximum71 low high
  · subst n; exact maximum72 low high
  · subst n; exact maximum73 low high
  · subst n; exact maximum74 low high
  · subst n; exact maximum75 low high
  · subst n; exact maximum76 low high
  · subst n; exact maximum77 low high
  · subst n; exact maximum78 low high

theorem maximum {n m : Nat} (large : 43≤n)
    (low : 3*n≤m) (high : m≤n*(n-3)) : IsMaximum n m (n*(n-1)-m) := by
  by_cases old : 79≤n
  · exact PairCodeOverlap.maximum old low high
  · exact finite_maximum large (by omega) low high

#print axioms maximum
end Delivery.MainOverlapFortyThree
