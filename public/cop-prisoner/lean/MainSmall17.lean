import MainSmallFamilies
import MainSmall17Stage00
import MainSmall17Stage01
import MainSmall17Stage02
import MainSmall17Stage03
import MainSmall17Stage04
import MainSmall17Stage05
import MainSmall17Stage06
import MainSmall17Stage07
import MainSmall17Stage08
import MainSmall17Stage09
import MainSmall17Stage10
import MainSmall17Stage11
import MainSmall17Stage12
import MainSmall17Stage13
import MainSmall17Stage14
import MainSmall17Stage15
import MainSmall17Stage16
import MainSmall17Stage17
import MainSmall17Stage18
import MainSmall17Stage19
import MainSmall17Stage20
import MainSmall17Stage21
set_option maxRecDepth 100000
namespace Delivery.MainSmall17
open Extremal
theorem maximum {m : Nat} (low : 34≤m) (high : m≤238) :
    IsMaximum 17 m (272-m) := by
  by_cases h00 : m≤37
  · exact MainSmall17Stage00.maximum (by omega) h00
  by_cases h01 : m≤40
  · exact MainSmall17Stage01.maximum (by omega) h01
  by_cases h02 : m≤46
  · exact MainSmall17Stage02.maximum (by omega) h02
  by_cases h03 : m≤55
  · exact MainSmall17Stage03.maximum (by omega) h03
  by_cases h04 : m≤57
  · exact MainSmall17Stage04.maximum (by omega) h04
  by_cases h05 : m≤59
  · exact MainSmall17Stage05.maximum (by omega) h05
  by_cases h06 : m≤65
  · exact MainSmall17Stage06.maximum (by omega) h06
  by_cases h07 : m≤67
  · exact MainSmall17Stage07.maximum (by omega) h07
  by_cases h08 : m≤73
  · exact MainSmall17Stage08.maximum (by omega) h08
  by_cases h09 : m≤77
  · exact MainSmall17Stage09.maximum (by omega) h09
  by_cases h10 : m≤84
  · exact MainSmall17Stage10.maximum (by omega) h10
  by_cases h11 : m≤102
  · exact MainSmallFamilies.circle17 (by omega) h11
  by_cases h12 : m≤114
  · exact MainSmall17Stage11.maximum (by omega) h12
  by_cases h13 : m≤122
  · exact MainSmall17Stage12.maximum (by omega) h13
  by_cases h14 : m≤137
  · exact MainSmall17Stage13.maximum (by omega) h14
  by_cases h15 : m≤141
  · exact MainSmall17Stage14.maximum (by omega) h15
  by_cases h16 : m≤145
  · exact MainSmall17Stage15.maximum (by omega) h16
  by_cases h17 : m≤160
  · exact MainSmall17Stage16.maximum (by omega) h17
  by_cases h18 : m≤173
  · exact MainSmall17Stage17.maximum (by omega) h18
  by_cases h19 : m≤189
  · exact MainSmall17Stage18.maximum (by omega) h19
  by_cases h20 : m≤200
  · exact MainSmall17Stage19.maximum (by omega) h20
  by_cases h21 : m≤212
  · exact MainSmall17Stage20.maximum (by omega) h21
  by_cases h22 : m≤216
  · exact MainSmall17Stage21.maximum (by omega) h22
  by_cases h23 : m≤222
  · exact TwelveHubCodes.maximum (g:=3) (b:=2) (r:=2) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h24 : m≤238
  · exact PairCodeConstruction.maximum (k:=6) (by decide) (by decide) (by decide) (by omega) (by omega)
  omega
#print axioms maximum
end Delivery.MainSmall17
