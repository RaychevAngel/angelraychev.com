import MainSmallFamilies
import MainSmall13Stage00
import MainSmall13Stage01
import MainSmall13Stage02
import MainSmall13Stage03
import MainSmall13Stage04
import MainSmall13Stage05
import MainSmall13Stage06
import MainSmall13Stage07
import MainSmall13Stage08
import MainSmall13Stage09
import MainSmall13Stage10
import MainSmall13Stage11
import MainSmall13Stage12
import MainSmall13Stage13
import MainSmall13Stage14
import MainSmall13Stage15
import MainSmall13Stage16
import MainSmall13Stage17
import MainSmall13Stage18
import MainSmall13Stage19
import MainSmall13Stage20
import MainSmall13Stage21
import MainSmall13Stage22
import MainSmall13Stage23
import MainSmall13Stage24
import MainSmall13Stage25
namespace Delivery.MainSmall13
open Extremal
theorem maximum {m : Nat} (low : 26≤m) (high : m≤130) :
    IsMaximum 13 m (156-m) := by
  by_cases h00 : m≤27
  · exact MainSmall13Stage00.maximum (by omega) h00
  by_cases h01 : m≤30
  · exact MainSmall13Stage01.maximum (by omega) h01
  by_cases h02 : m≤32
  · exact MainSmall13Stage02.maximum (by omega) h02
  by_cases h03 : m≤35
  · exact MainSmall13Stage03.maximum (by omega) h03
  by_cases h04 : m≤38
  · exact MainSmall13Stage04.maximum (by omega) h04
  by_cases h05 : m≤41
  · exact MainSmall13Stage05.maximum (by omega) h05
  by_cases h06 : m≤43
  · exact MainSmall13Stage06.maximum (by omega) h06
  by_cases h07 : m≤46
  · exact MainSmall13Stage07.maximum (by omega) h07
  by_cases h08 : m≤48
  · exact MainSmall13Stage08.maximum (by omega) h08
  by_cases h09 : m≤51
  · exact MainSmall13Stage09.maximum (by omega) h09
  by_cases h10 : m≤53
  · exact MainSmall13Stage10.maximum (by omega) h10
  by_cases h11 : m≤56
  · exact MainSmall13Stage11.maximum (by omega) h11
  by_cases h12 : m≤58
  · exact MainSmall13Stage12.maximum (by omega) h12
  by_cases h13 : m≤61
  · exact MainSmall13Stage13.maximum (by omega) h13
  by_cases h14 : m≤65
  · exact MainSmall13Stage14.maximum (by omega) h14
  by_cases h15 : m≤68
  · exact MainSmall13Stage15.maximum (by omega) h15
  by_cases h16 : m≤75
  · exact MainSmall13Stage16.maximum (by omega) h16
  by_cases h17 : m≤78
  · exact MainSmall13Stage17.maximum (by omega) h17
  by_cases h18 : m≤86
  · exact MainSmall13Stage18.maximum (by omega) h18
  by_cases h19 : m≤92
  · exact MainSmall13Stage19.maximum (by omega) h19
  by_cases h20 : m≤101
  · exact MainSmall13Stage20.maximum (by omega) h20
  by_cases h21 : m≤108
  · exact MainSmall13Stage21.maximum (by omega) h21
  by_cases h22 : m≤111
  · exact MainSmall13Stage22.maximum (by omega) h22
  by_cases h23 : m≤118
  · exact MainSmall13Stage23.maximum (by omega) h23
  by_cases h24 : m≤124
  · exact MainSmall13Stage24.maximum (by omega) h24
  by_cases h25 : m≤128
  · exact MainSmall13Stage25.maximum (by omega) h25
  by_cases h26 : m≤130
  · exact MainTiny13.maximum (by omega) h26
  omega
#print axioms maximum
end Delivery.MainSmall13
