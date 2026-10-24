import MainOverlapFortyThree
import SixCircleFinite
import ProtectedFiniteConstruction

/-! The full upper main interval from order32, using existing explicit
families. Every finite parameter and interval overlap is kernel checked. -/
namespace Delivery.MainOverlapThirtyTwo
open Extremal

theorem maximum32 {m : Nat} (low : 96≤m) (high : m≤928) :
    IsMaximum 32 m (992-m) := by
  by_cases h0 : m≤256
  · exact ProtectedFiniteConstruction.finite_maximum (by decide) (by decide) (by omega) (by change m≤256; omega)
  by_cases h1 : m≤544
  · exact SixCircleFinite24.maximum (by omega) (by omega)
  by_cases h2 : m≤798
  · exact TwelveHubCodes.maximum (g:=6) (b:=14) (r:=2) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=8) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum33 {m : Nat} (low : 99≤m) (high : m≤990) :
    IsMaximum 33 m (1056-m) := by
  by_cases h0 : m≤264
  · exact ProtectedFiniteConstruction.finite_maximum (by decide) (by decide) (by omega) (by change m≤264; omega)
  by_cases h1 : m≤561
  · exact SixCircleFinite25.maximum (by omega) (by omega)
  by_cases h2 : m≤853
  · exact TwelveHubCodes.maximum (g:=6) (b:=15) (r:=2) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=8) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum34 {m : Nat} (low : 102≤m) (high : m≤1054) :
    IsMaximum 34 m (1122-m) := by
  by_cases h0 : m≤306
  · exact ProtectedFiniteConstruction.finite_maximum (by decide) (by decide) (by omega) (by change m≤306; omega)
  by_cases h1 : m≤612
  · exact SixCircleFinite26.maximum (by omega) (by omega)
  by_cases h2 : m≤926
  · exact TwelveHubCodes.maximum (g:=6) (b:=16) (r:=3) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=8) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum35 {m : Nat} (low : 105≤m) (high : m≤1120) :
    IsMaximum 35 m (1190-m) := by
  by_cases h0 : m≤350
  · exact ProtectedFiniteConstruction.finite_maximum (by decide) (by decide) (by omega) (by change m≤350; omega)
  by_cases h1 : m≤595
  · exact SixCircleFinite27.maximum (by omega) (by omega)
  by_cases h2 : m≤948
  · exact TwelveHubCodes.maximum (g:=7) (b:=16) (r:=2) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=8) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum36 {m : Nat} (low : 108≤m) (high : m≤1188) :
    IsMaximum 36 m (1260-m) := by
  by_cases h0 : m≤180
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤612
  · exact CircleConstruction.full_maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h2 : m≤648
  · exact SixCircleFinite28.maximum (by omega) (by omega)
  by_cases h3 : m≤1048
  · exact TwelveHubCodes.maximum (g:=6) (b:=18) (r:=3) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=8) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum37 {m : Nat} (low : 111≤m) (high : m≤1258) :
    IsMaximum 37 m (1332-m) := by
  by_cases h0 : m≤185
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤555
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤555; omega)
  by_cases h2 : m≤703
  · exact SixCircleFinite29.maximum (by omega) (by omega)
  by_cases h3 : m≤1124
  · exact TwelveHubCodes.maximum (g:=7) (b:=18) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=8) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum38 {m : Nat} (low : 114≤m) (high : m≤1330) :
    IsMaximum 38 m (1406-m) := by
  by_cases h0 : m≤190
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤570
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤570; omega)
  by_cases h2 : m≤760
  · exact SixCircleFinite30.maximum (by omega) (by omega)
  by_cases h3 : m≤1191
  · exact TwelveHubCodes.maximum (g:=7) (b:=19) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=8) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum39 {m : Nat} (low : 117≤m) (high : m≤1404) :
    IsMaximum 39 m (1482-m) := by
  by_cases h0 : m≤195
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤624
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤624; omega)
  by_cases h2 : m≤819
  · exact SixCircleFinite31.maximum (by omega) (by omega)
  by_cases h3 : m≤1260
  · exact TwelveHubCodes.maximum (g:=7) (b:=20) (r:=5) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=8) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum40 {m : Nat} (low : 120≤m) (high : m≤1480) :
    IsMaximum 40 m (1560-m) := by
  by_cases h0 : m≤200
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤760
  · exact CircleConstruction.full_maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h2 : m≤1310
  · exact TwelveHubCodes.maximum (g:=7) (b:=21) (r:=4) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=8) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum41 {m : Nat} (low : 123≤m) (high : m≤1558) :
    IsMaximum 41 m (1640-m) := by
  by_cases h0 : m≤205
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤697
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤697; omega)
  by_cases h2 : m≤861
  · exact SixCircleFinite33.maximum (by omega) (by omega)
  by_cases h3 : m≤1395
  · exact TwelveHubCodes.maximum (g:=8) (b:=21) (r:=6) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=9) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum42 {m : Nat} (low : 126≤m) (high : m≤1638) :
    IsMaximum 42 m (1722-m) := by
  by_cases h0 : m≤210
  · exact ProtectedParameters.maximum (by decide) (by omega) (by omega)
  by_cases h1 : m≤630
  · exact CircleGuardedConstruction.maximum (h:=11) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤630; omega)
  by_cases h2 : m≤924
  · exact SixCircleFinite34.maximum (by omega) (by omega)
  by_cases h3 : m≤1470
  · exact TwelveHubCodes.maximum (g:=8) (b:=22) (r:=6) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=9) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem finite_maximum {n m : Nat} (large : 32≤n) (small : n≤42)
    (low : 3*n≤m) (high : m≤n*(n-3)) : IsMaximum n m (n*(n-1)-m) := by
  have cases : n=32 ∨ n=33 ∨ n=34 ∨ n=35 ∨ n=36 ∨ n=37 ∨ n=38 ∨ n=39 ∨ n=40 ∨ n=41 ∨ n=42 := by omega
  rcases cases with h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42
  · subst n; exact maximum32 low high
  · subst n; exact maximum33 low high
  · subst n; exact maximum34 low high
  · subst n; exact maximum35 low high
  · subst n; exact maximum36 low high
  · subst n; exact maximum37 low high
  · subst n; exact maximum38 low high
  · subst n; exact maximum39 low high
  · subst n; exact maximum40 low high
  · subst n; exact maximum41 low high
  · subst n; exact maximum42 low high

theorem maximum {n m : Nat} (large : 32≤n)
    (low : 3*n≤m) (high : m≤n*(n-3)) : IsMaximum n m (n*(n-1)-m) := by
  by_cases old : 43≤n
  · exact MainOverlapFortyThree.maximum old low high
  · exact finite_maximum large (by omega) low high

#print axioms maximum
end Delivery.MainOverlapThirtyTwo
