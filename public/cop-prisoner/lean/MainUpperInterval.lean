import MainOverlapThirtyTwo
import ReducedTwelveHubCounts
import FourteenHubNineteen

/-! The full upper main interval from order25, using existing explicit
families. Every finite parameter and interval overlap is kernel checked. -/
namespace Delivery.MainUpperInterval
open Extremal

theorem maximum19 {m : Nat} (low : 95≤m) (high : m≤304) :
    IsMaximum 19 m (342-m) := by
  by_cases h0 : m≤133
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤133; omega)
  by_cases h1 : m≤171
  · exact SixCircleFinite03.maximum (by omega) (by omega)
  by_cases h2 : m≤228
  · exact SixCircleFinite04.maximum (by omega) (by omega)
  by_cases h3 : m≤268
  · exact ReducedTwelveHubCounts.maximum (g:=4) (b:=3) (r:=3) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h4 : m≤278
  · exact TwelveHubCodes.maximum (g:=4) (b:=3) (r:=3) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h5 : m≤285
  · exact FourteenHubNineteen.maximum (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=7) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum20 {m : Nat} (low : 100≤m) (high : m≤340) :
    IsMaximum 20 m (380-m) := by
  by_cases h0 : m≤180
  · exact CircleConstruction.full_maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h1 : m≤200
  · exact SixCircleFinite05.maximum (by omega) (by omega)
  by_cases h2 : m≤240
  · exact SixCircleFinite06.maximum (by omega) (by omega)
  by_cases h3 : m≤302
  · exact ReducedTwelveHubCounts.maximum (g:=4) (b:=4) (r:=3) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h4 : m≤310
  · exact TwelveHubCodes.maximum (g:=4) (b:=4) (r:=3) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=7) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum21 {m : Nat} (low : 126≤m) (high : m≤378) :
    IsMaximum 21 m (420-m) := by
  by_cases h0 : m≤210
  · exact SixCircleFinite07.maximum (by omega) (by omega)
  by_cases h1 : m≤252
  · exact SixCircleFinite08.maximum (by omega) (by omega)
  by_cases h2 : m≤333
  · exact ReducedTwelveHubCounts.maximum (g:=4) (b:=5) (r:=2) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h3 : m≤340
  · exact TwelveHubCodes.maximum (g:=5) (b:=4) (r:=4) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=7) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum22 {m : Nat} (low : 110≤m) (high : m≤418) :
    IsMaximum 22 m (462-m) := by
  by_cases h0 : m≤154
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤154; omega)
  by_cases h1 : m≤242
  · exact SixCircleFinite09.maximum (by omega) (by omega)
  by_cases h2 : m≤264
  · exact SixCircleFinite10.maximum (by omega) (by omega)
  by_cases h3 : m≤370
  · exact ReducedTwelveHubCounts.maximum (g:=4) (b:=6) (r:=2) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=7) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum23 {m : Nat} (low : 115≤m) (high : m≤460) :
    IsMaximum 23 m (506-m) := by
  by_cases h0 : m≤184
  · exact CircleGuardedConstruction.maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by omega) (by change m≤184; omega)
  by_cases h1 : m≤253
  · exact SixCircleFinite11.maximum (by omega) (by omega)
  by_cases h2 : m≤299
  · exact SixCircleFinite12.maximum (by omega) (by omega)
  by_cases h3 : m≤400
  · exact ReducedTwelveHubCounts.maximum (g:=5) (b:=6) (r:=3) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=7) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum24 {m : Nat} (low : 120≤m) (high : m≤504) :
    IsMaximum 24 m (552-m) := by
  by_cases h0 : m≤264
  · exact CircleConstruction.full_maximum (h:=7) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h1 : m≤288
  · exact SixCircleFinite13.maximum (by omega) (by omega)
  by_cases h2 : m≤312
  · exact SixCircleFinite14.maximum (by omega) (by omega)
  by_cases h3 : m≤441
  · exact ReducedTwelveHubCounts.maximum (g:=5) (b:=7) (r:=3) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=7) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum25 {m : Nat} (low : 75≤m) (high : m≤550) :
    IsMaximum 25 m (600-m) := by
  by_cases h0 : m≤175
  · exact ProtectedFiniteConstruction.finite_maximum (by decide) (by decide) (by omega) (by change m≤175; omega)
  by_cases h1 : m≤325
  · exact SixCircleFinite15.maximum (by omega) (by omega)
  by_cases h2 : m≤484
  · exact ReducedTwelveHubCounts.maximum (g:=5) (b:=8) (r:=3) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=7) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum26 {m : Nat} (low : 78≤m) (high : m≤598) :
    IsMaximum 26 m (650-m) := by
  by_cases h0 : m≤182
  · exact ProtectedFiniteConstruction.finite_maximum (by decide) (by decide) (by omega) (by change m≤182; omega)
  by_cases h1 : m≤364
  · exact SixCircleFinite17.maximum (by omega) (by omega)
  by_cases h2 : m≤529
  · exact ReducedTwelveHubCounts.maximum (g:=5) (b:=9) (r:=3) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=7) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum27 {m : Nat} (low : 81≤m) (high : m≤648) :
    IsMaximum 27 m (702-m) := by
  by_cases h0 : m≤189
  · exact ProtectedFiniteConstruction.finite_maximum (by decide) (by decide) (by omega) (by change m≤189; omega)
  by_cases h1 : m≤351
  · exact SixCircleFinite18.maximum (by omega) (by omega)
  by_cases h2 : m≤576
  · exact ReducedTwelveHubCounts.maximum (g:=5) (b:=10) (r:=3) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=7) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum28 {m : Nat} (low : 84≤m) (high : m≤700) :
    IsMaximum 28 m (756-m) := by
  by_cases h0 : m≤196
  · exact ProtectedFiniteConstruction.finite_maximum (by decide) (by decide) (by omega) (by change m≤196; omega)
  by_cases h1 : m≤420
  · exact SixCircleFinite20.maximum (by omega) (by omega)
  by_cases h2 : m≤614
  · exact ReducedTwelveHubCounts.maximum (g:=6) (b:=10) (r:=4) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=7) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum29 {m : Nat} (low : 87≤m) (high : m≤754) :
    IsMaximum 29 m (812-m) := by
  by_cases h0 : m≤203
  · exact ProtectedFiniteConstruction.finite_maximum (by decide) (by decide) (by omega) (by change m≤203; omega)
  by_cases h1 : m≤435
  · exact SixCircleFinite21.maximum (by omega) (by omega)
  by_cases h2 : m≤665
  · exact ReducedTwelveHubCounts.maximum (g:=6) (b:=11) (r:=4) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=8) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum30 {m : Nat} (low : 90≤m) (high : m≤810) :
    IsMaximum 30 m (870-m) := by
  by_cases h0 : m≤240
  · exact ProtectedFiniteConstruction.finite_maximum (by decide) (by decide) (by omega) (by change m≤240; omega)
  by_cases h1 : m≤480
  · exact SixCircleFinite22.maximum (by omega) (by omega)
  by_cases h2 : m≤718
  · exact ReducedTwelveHubCounts.maximum (g:=6) (b:=12) (r:=4) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=8) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem maximum31 {m : Nat} (low : 93≤m) (high : m≤868) :
    IsMaximum 31 m (930-m) := by
  by_cases h0 : m≤248
  · exact ProtectedFiniteConstruction.finite_maximum (by decide) (by decide) (by omega) (by change m≤248; omega)
  by_cases h1 : m≤496
  · exact SixCircleFinite23.maximum (by omega) (by omega)
  by_cases h2 : m≤773
  · exact ReducedTwelveHubCounts.maximum (g:=6) (b:=13) (r:=4) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  exact PairCodeConstruction.maximum (k:=8) (by decide) (by decide) (by decide) (by omega) (by omega)

theorem finite_maximum {n m : Nat} (large : 25≤n) (small : n≤31)
    (low : 3*n≤m) (high : m≤n*(n-3)) : IsMaximum n m (n*(n-1)-m) := by
  have cases : n=25 ∨ n=26 ∨ n=27 ∨ n=28 ∨ n=29 ∨ n=30 ∨ n=31 := by omega
  rcases cases with h25 | h26 | h27 | h28 | h29 | h30 | h31
  · subst n; exact maximum25 low high
  · subst n; exact maximum26 low high
  · subst n; exact maximum27 low high
  · subst n; exact maximum28 low high
  · subst n; exact maximum29 low high
  · subst n; exact maximum30 low high
  · subst n; exact maximum31 low high

theorem maximum {n m : Nat} (large : 25≤n)
    (low : 3*n≤m) (high : m≤n*(n-3)) : IsMaximum n m (n*(n-1)-m) := by
  by_cases old : 32≤n
  · exact MainOverlapThirtyTwo.maximum old low high
  · exact finite_maximum large (by omega) low high

#print axioms maximum
end Delivery.MainUpperInterval
