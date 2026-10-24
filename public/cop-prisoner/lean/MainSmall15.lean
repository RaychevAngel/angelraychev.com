import MainSmallFamilies
import MainSmall15Stage00
import MainSmall15Stage01
import MainSmall15Stage02
import MainSmall15Stage03
import MainSmall15Stage04
import MainSmall15Stage05
import MainSmall15Stage06
import MainSmall15Stage07
import MainSmall15Stage08
import MainSmall15Stage09
import MainSmall15Stage10
import MainSmall15Stage11
import MainSmall15Stage12
import MainSmall15Stage13
import MainSmall15Stage14
import MainSmall15Stage15
import MainSmall15Stage16
import MainSmall15Stage17
import MainSmall15Stage18
import MainSmall15Stage19
namespace Delivery.MainSmall15
open Extremal
theorem maximum {m : Nat} (low : 30≤m) (high : m≤180) :
    IsMaximum 15 m (210-m) := by
  by_cases h00 : m≤32
  · exact MainSmall15Stage00.maximum (by omega) h00
  by_cases h01 : m≤34
  · exact MainSmall15Stage01.maximum (by omega) h01
  by_cases h02 : m≤38
  · exact MainSmall15Stage02.maximum (by omega) h02
  by_cases h03 : m≤42
  · exact MainSmall15Stage03.maximum (by omega) h03
  by_cases h04 : m≤46
  · exact MainSmall15Stage04.maximum (by omega) h04
  by_cases h05 : m≤52
  · exact MainSmall15Stage05.maximum (by omega) h05
  by_cases h06 : m≤54
  · exact MainSmall15Stage06.maximum (by omega) h06
  by_cases h07 : m≤57
  · exact MainSmall15Stage07.maximum (by omega) h07
  by_cases h08 : m≤67
  · exact MainSmall15Stage08.maximum (by omega) h08
  by_cases h09 : m≤75
  · exact MainSmall15Stage09.maximum (by omega) h09
  by_cases h10 : m≤78
  · exact MainSmall15Stage10.maximum (by omega) h10
  by_cases h11 : m≤89
  · exact MainSmall15Stage11.maximum (by omega) h11
  by_cases h12 : m≤109
  · exact MainSmall15Stage12.maximum (by omega) h12
  by_cases h13 : m≤118
  · exact MainSmall15Stage13.maximum (by omega) h13
  by_cases h14 : m≤125
  · exact MainSmall15Stage14.maximum (by omega) h14
  by_cases h15 : m≤135
  · exact MainSmall15Stage15.maximum (by omega) h15
  by_cases h16 : m≤143
  · exact MainSmall15Stage16.maximum (by omega) h16
  by_cases h17 : m≤154
  · exact MainSmall15Stage17.maximum (by omega) h17
  by_cases h18 : m≤165
  · exact MainSmall15Stage18.maximum (by omega) h18
  by_cases h19 : m≤170
  · exact MainSmall15Stage19.maximum (by omega) h19
  by_cases h20 : m≤173
  · exact TwelveHubCodes.maximum (g:=2) (b:=1) (r:=2) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
  by_cases h21 : m≤180
  · exact PairCodeConstruction.maximum (k:=6) (by decide) (by decide) (by decide) (by omega) (by omega)
  omega
#print axioms maximum
end Delivery.MainSmall15
