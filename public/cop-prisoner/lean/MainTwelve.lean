import MainTwelveStage00
import MainTwelveStage01
import MainTwelveStage02
import MainTwelveStage03
import MainTwelveStage04
import MainTwelveStage05
import MainTwelveStage06
import MainTwelveStage07
import MainTwelveStage08
import MainTwelveStage09
import MainTwelveStage10
import MainTwelveStage11
import MainTwelveStage12
import MainTwelveStage13
import MainTwelveStage14
import MainTwelveStage15
import MainTwelveStage16
import MainTwelveStage17
import MainTwelveStage18
import MainTwelveStage19
import MainTwelveStage20
import MainTwelveStage21
import MainTwelveStage22
import MainTwelveStage23
import MainTwelveStage24
import MainTwelveStage25
import MainTwelveStage26
import MainTwelveStage27
import MainTwelveStage28
import MainTwelveStage29
import PairCodeConstruction

/-! All main-interval budgets at order twelve, from literal certified stages. -/
namespace Delivery.MainTwelve
open Extremal

theorem maximum {m : Nat} (low : 24≤m) (high : m≤108) : IsMaximum 12 m (132-m) := by
  by_cases h00 : m≤25
  · exact MainTwelveStage00.maximum (by omega) h00
  by_cases h01 : m≤27
  · exact MainTwelveStage01.maximum (by omega) h01
  by_cases h02 : m≤29
  · exact MainTwelveStage02.maximum (by omega) h02
  by_cases h03 : m≤30
  · exact MainTwelveStage03.maximum (by omega) h03
  by_cases h04 : m≤31
  · exact MainTwelveStage04.maximum (by omega) h04
  by_cases h05 : m≤36
  · exact MainTwelveStage05.maximum (by omega) h05
  by_cases h06 : m≤38
  · exact MainTwelveStage06.maximum (by omega) h06
  by_cases h07 : m≤40
  · exact MainTwelveStage07.maximum (by omega) h07
  by_cases h08 : m≤43
  · exact MainTwelveStage08.maximum (by omega) h08
  by_cases h09 : m≤46
  · exact MainTwelveStage09.maximum (by omega) h09
  by_cases h10 : m≤49
  · exact MainTwelveStage10.maximum (by omega) h10
  by_cases h11 : m≤54
  · exact MainTwelveStage11.maximum (by omega) h11
  by_cases h12 : m≤58
  · exact MainTwelveStage12.maximum (by omega) h12
  by_cases h13 : m≤65
  · exact MainTwelveStage13.maximum (by omega) h13
  by_cases h14 : m≤68
  · exact MainTwelveStage14.maximum (by omega) h14
  by_cases h15 : m≤69
  · exact MainTwelveStage15.maximum (by omega) h15
  by_cases h16 : m≤71
  · exact MainTwelveStage16.maximum (by omega) h16
  by_cases h17 : m≤72
  · exact MainTwelveStage17.maximum (by omega) h17
  by_cases h18 : m≤74
  · exact MainTwelveStage18.maximum (by omega) h18
  by_cases h19 : m≤77
  · exact MainTwelveStage19.maximum (by omega) h19
  by_cases h20 : m≤79
  · exact MainTwelveStage20.maximum (by omega) h20
  by_cases h21 : m≤81
  · exact MainTwelveStage21.maximum (by omega) h21
  by_cases h22 : m≤86
  · exact MainTwelveStage22.maximum (by omega) h22
  by_cases h23 : m≤87
  · exact MainTwelveStage23.maximum (by omega) h23
  by_cases h24 : m≤91
  · exact MainTwelveStage24.maximum (by omega) h24
  by_cases h25 : m≤95
  · exact MainTwelveStage25.maximum (by omega) h25
  by_cases h26 : m≤99
  · exact MainTwelveStage26.maximum (by omega) h26
  by_cases h27 : m≤100
  · exact MainTwelveStage27.maximum (by omega) h27
  by_cases h28 : m≤103
  · exact MainTwelveStage28.maximum (by omega) h28
  by_cases h29 : m≤107
  · exact MainTwelveStage29.maximum (by omega) h29
  have equal : m=108 := by omega
  subst m
  exact PairCodeConstruction.maximum (k:=6) (by decide) (by decide) (by decide) (by decide) (by decide)

#print axioms maximum
end Delivery.MainTwelve
