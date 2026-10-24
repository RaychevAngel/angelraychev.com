import MainSmallFamilies
import MainSmall14Stage00
import MainSmall14Stage01
import MainSmall14Stage02
import MainSmall14Stage03
import MainSmall14Stage04
import MainSmall14Stage05
import MainSmall14Stage06
import MainSmall14Stage07
import MainSmall14Stage08
import MainSmall14Stage09
import MainSmall14Stage10
import MainSmall14Stage11
import MainSmall14Stage12
import MainSmall14Stage13
import MainSmall14Stage14
import MainSmall14Stage15
import MainSmall14Stage16
import MainSmall14Stage17
import MainSmall14Stage18
import MainSmall14Stage19
import MainSmall14Stage20
import MainSmall14Stage21
import MainSmall14Stage22
import MainSmall14Stage23
import MainSmall14Stage24
import MainSmall14Stage25
namespace Delivery.MainSmall14
open Extremal
theorem maximum {m : Nat} (low : 28≤m) (high : m≤154) :
    IsMaximum 14 m (182-m) := by
  by_cases h00 : m≤30
  · exact MainSmall14Stage00.maximum (by omega) h00
  by_cases h01 : m≤32
  · exact MainSmall14Stage01.maximum (by omega) h01
  by_cases h02 : m≤39
  · exact MainSmall14Stage02.maximum (by omega) h02
  by_cases h03 : m≤43
  · exact MainSmall14Stage03.maximum (by omega) h03
  by_cases h04 : m≤48
  · exact MainSmall14Stage04.maximum (by omega) h04
  by_cases h05 : m≤51
  · exact MainSmall14Stage05.maximum (by omega) h05
  by_cases h06 : m≤60
  · exact MainSmall14Stage06.maximum (by omega) h06
  by_cases h07 : m≤67
  · exact MainSmall14Stage07.maximum (by omega) h07
  by_cases h08 : m≤69
  · exact MainSmall14Stage08.maximum (by omega) h08
  by_cases h09 : m≤72
  · exact MainSmall14Stage09.maximum (by omega) h09
  by_cases h10 : m≤77
  · exact MainSmall14Stage10.maximum (by omega) h10
  by_cases h11 : m≤79
  · exact MainSmall14Stage11.maximum (by omega) h11
  by_cases h12 : m≤82
  · exact MainSmall14Stage12.maximum (by omega) h12
  by_cases h13 : m≤84
  · exact MainSmall14Stage13.maximum (by omega) h13
  by_cases h14 : m≤88
  · exact MainSmall14Stage14.maximum (by omega) h14
  by_cases h15 : m≤91
  · exact MainSmall14Stage15.maximum (by omega) h15
  by_cases h16 : m≤94
  · exact MainSmall14Stage16.maximum (by omega) h16
  by_cases h17 : m≤99
  · exact MainSmall14Stage17.maximum (by omega) h17
  by_cases h18 : m≤103
  · exact MainSmall14Stage18.maximum (by omega) h18
  by_cases h19 : m≤114
  · exact MainSmall14Stage19.maximum (by omega) h19
  by_cases h20 : m≤120
  · exact MainSmall14Stage20.maximum (by omega) h20
  by_cases h21 : m≤123
  · exact MainSmall14Stage21.maximum (by omega) h21
  by_cases h22 : m≤126
  · exact MainSmall14Stage22.maximum (by omega) h22
  by_cases h23 : m≤130
  · exact MainSmall14Stage23.maximum (by omega) h23
  by_cases h24 : m≤143
  · exact MainSmall14Stage24.maximum (by omega) h24
  by_cases h25 : m≤146
  · exact MainSmall14Stage25.maximum (by omega) h25
  by_cases h26 : m≤154
  · exact MainTiny14.maximum (by omega) h26
  omega
#print axioms maximum
end Delivery.MainSmall14
