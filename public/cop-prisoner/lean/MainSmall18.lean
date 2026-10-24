import MainSmallFamilies
import MainSmall18Stage00
import MainSmall18Stage01
import MainSmall18Stage02
import MainSmall18Stage03
import MainSmall18Stage04
import MainSmall18Stage05
import MainSmall18Stage06
import MainSmall18Stage07
import MainSmall18Stage08
import MainSmall18Stage09
import MainSmall18Stage10
import MainSmall18Stage11
import MainSmall18Stage12
import MainSmall18Stage13
import MainSmall18Stage14
import MainSmall18Stage15
import MainSmall18Stage16
import MainSmall18Stage17
import MainSmall18Stage18
import MainSmall18Stage19
import MainSmall18Stage20
import MainSmall18Stage21
import MainSmall18Stage22
import MainSmall18Stage23
import MainSmall18Stage24
import MainSmall18Stage25
import MainSmall18Stage26
import MainSmall18Stage27
import MainSmall18Stage28
set_option maxRecDepth 100000
namespace Delivery.MainSmall18
open Extremal
theorem maximum {m : Nat} (low : 36≤m) (high : m≤270) :
    IsMaximum 18 m (306-m) := by
  by_cases h00 : m≤38
  · exact MainSmall18Stage00.maximum (by omega) h00
  by_cases h01 : m≤41
  · exact MainSmall18Stage01.maximum (by omega) h01
  by_cases h02 : m≤44
  · exact MainSmall18Stage02.maximum (by omega) h02
  by_cases h03 : m≤50
  · exact MainSmall18Stage03.maximum (by omega) h03
  by_cases h04 : m≤52
  · exact MainSmall18Stage04.maximum (by omega) h04
  by_cases h05 : m≤53
  · exact MainSmall18Stage05.maximum (by omega) h05
  by_cases h06 : m≤62
  · exact MainSmall18Stage06.maximum (by omega) h06
  by_cases h07 : m≤65
  · exact MainSmall18Stage07.maximum (by omega) h07
  by_cases h08 : m≤67
  · exact MainSmall18Stage08.maximum (by omega) h08
  by_cases h09 : m≤71
  · exact MainSmall18Stage09.maximum (by omega) h09
  by_cases h10 : m≤74
  · exact MainSmall18Stage10.maximum (by omega) h10
  by_cases h11 : m≤78
  · exact MainSmall18Stage11.maximum (by omega) h11
  by_cases h12 : m≤80
  · exact MainSmall18Stage12.maximum (by omega) h12
  by_cases h13 : m≤84
  · exact MainSmall18Stage13.maximum (by omega) h13
  by_cases h14 : m≤89
  · exact MainSmall18Stage14.maximum (by omega) h14
  by_cases h15 : m≤108
  · exact MainSmallFamilies.circle18 (by omega) h15
  by_cases h16 : m≤110
  · exact MainSmall18Stage15.maximum (by omega) h16
  by_cases h17 : m≤127
  · exact MainSmall18Stage16.maximum (by omega) h17
  by_cases h18 : m≤134
  · exact MainSmall18Stage17.maximum (by omega) h18
  by_cases h19 : m≤140
  · exact MainSmall18Stage18.maximum (by omega) h19
  by_cases h20 : m≤147
  · exact MainSmall18Stage19.maximum (by omega) h20
  by_cases h21 : m≤154
  · exact MainSmall18Stage20.maximum (by omega) h21
  by_cases h22 : m≤171
  · exact MainSmall18Stage21.maximum (by omega) h22
  by_cases h23 : m≤183
  · exact MainSmall18Stage22.maximum (by omega) h23
  by_cases h24 : m≤194
  · exact MainSmall18Stage23.maximum (by omega) h24
  by_cases h25 : m≤199
  · exact MainSmall18Stage24.maximum (by omega) h25
  by_cases h26 : m≤207
  · exact MainSmall18Stage25.maximum (by omega) h26
  by_cases h27 : m≤213
  · exact MainSmall18Stage26.maximum (by omega) h27
  by_cases h28 : m≤222
  · exact MainSmall18Stage27.maximum (by omega) h28
  by_cases h29 : m≤239
  · exact MainSmall18Stage28.maximum (by omega) h29
  by_cases h30 : m≤270
  · exact PairCodeConstruction.maximum (k:=6) (by decide) (by decide) (by decide) (by omega) (by omega)
  omega
#print axioms maximum
end Delivery.MainSmall18
