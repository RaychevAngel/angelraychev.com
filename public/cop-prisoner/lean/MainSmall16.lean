import MainSmallFamilies
import MainSmall16Stage00
import MainSmall16Stage01
import MainSmall16Stage02
import MainSmall16Stage03
import MainSmall16Stage04
import MainSmall16Stage05
import MainSmall16Stage06
import MainSmall16Stage07
import MainSmall16Stage08
import MainSmall16Stage09
import MainSmall16Stage10
import MainSmall16Stage11
import MainSmall16Stage12
import MainSmall16Stage13
import MainSmall16Stage14
import MainSmall16Stage15
import MainSmall16Stage16
import MainSmall16Stage17
import MainSmall16Stage18
import MainSmall16Stage19
import MainSmall16Stage20
import MainSmall16Stage21
set_option maxRecDepth 100000
namespace Delivery.MainSmall16
open Extremal
theorem maximum {m : Nat} (low : 32≤m) (high : m≤208) :
    IsMaximum 16 m (240-m) := by
  by_cases h00 : m≤33
  · exact MainSmall16Stage00.maximum (by omega) h00
  by_cases h01 : m≤36
  · exact MainSmall16Stage01.maximum (by omega) h01
  by_cases h02 : m≤40
  · exact MainSmall16Stage02.maximum (by omega) h02
  by_cases h03 : m≤50
  · exact MainSmall16Stage03.maximum (by omega) h03
  by_cases h04 : m≤53
  · exact MainSmall16Stage04.maximum (by omega) h04
  by_cases h05 : m≤58
  · exact MainSmall16Stage05.maximum (by omega) h05
  by_cases h06 : m≤62
  · exact MainSmall16Stage06.maximum (by omega) h06
  by_cases h07 : m≤70
  · exact MainSmall16Stage07.maximum (by omega) h07
  by_cases h08 : m≤72
  · exact MainSmall16Stage08.maximum (by omega) h08
  by_cases h09 : m≤75
  · exact MainSmall16Stage09.maximum (by omega) h09
  by_cases h10 : m≤78
  · exact MainSmall16Stage10.maximum (by omega) h10
  by_cases h11 : m≤86
  · exact MainSmall16Stage11.maximum (by omega) h11
  by_cases h12 : m≤112
  · exact MainSmallFamilies.circle16 (by omega) h12
  by_cases h13 : m≤116
  · exact MainSmall16Stage12.maximum (by omega) h13
  by_cases h14 : m≤127
  · exact MainSmall16Stage13.maximum (by omega) h14
  by_cases h15 : m≤131
  · exact MainSmall16Stage14.maximum (by omega) h15
  by_cases h16 : m≤141
  · exact MainSmall16Stage15.maximum (by omega) h16
  by_cases h17 : m≤149
  · exact MainSmall16Stage16.maximum (by omega) h17
  by_cases h18 : m≤160
  · exact MainSmall16Stage17.maximum (by omega) h18
  by_cases h19 : m≤162
  · exact MainSmall16Stage18.maximum (by omega) h19
  by_cases h20 : m≤175
  · exact MainSmall16Stage19.maximum (by omega) h20
  by_cases h21 : m≤189
  · exact MainSmall16Stage20.maximum (by omega) h21
  by_cases h22 : m≤194
  · exact MainSmall16Stage21.maximum (by omega) h22
  by_cases h23 : m≤208
  · exact SmallDenseEnvelopeMaxima.maximum ⟨0,by decide⟩ m (by change 192≤m; omega) (by change m≤208; omega)
  omega
#print axioms maximum
end Delivery.MainSmall16
