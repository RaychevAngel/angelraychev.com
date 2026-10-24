import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0266
import IrregularNine14P06C0267
import IrregularNine14P06C0268

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33120 : Route 9 := (fun mask => (mask,id))

def c33120 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33120 : Upper (D 6) (R 6) [10,132,33,257,68] 13 := by
  apply FastRouting.sound _ _ [10,132,33,257,68] 13 (by decide) (choices 1) [2,16,64] r33120 c33120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15987
  · exact u15988
  · exact u15989

def r33121 : Route 9 := (fun mask => (mask,id))

def c33121 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33121 : Upper (D 6) (R 6) [10,132,33,257,96] 13 := by
  apply FastRouting.sound _ _ [10,132,33,257,96] 13 (by decide) (choices 1) [2,4,16,64] r33121 c33121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15990
  · exact u15991
  · exact u15992
  · exact u15993

def b33122 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 100, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 134 37 268 19 112 112 240 368), lower := (rows 11 134 37 268 19 32 64 128 256), losses := [] }

theorem u33122 : Upper (D 6) (R 6) [10,132,33,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33123 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 16, targets := 66 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 11 134 37 268 49 114 82 210 338), lower := (rows 11 134 37 268 49 32 64 128 256), losses := [] }

theorem u33123 : Upper (D 6) (R 6) [10,132,33,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33124 : Route 9 := (fun mask => (mask,id))

def c33124 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33124 : Upper (D 6) (R 6) [10,132,33,260,34] 13 := by
  apply FastRouting.sound _ _ [10,132,33,260,34] 13 (by decide) (choices 1) [1,16,64] r33124 c33124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15994
  · exact u15995
  · exact u15996

def r33125 : Route 9 := (fun mask => (mask,id))

def c33125 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33125 : Upper (D 6) (R 6) [10,132,33,260,65] 13 := by
  apply FastRouting.sound _ _ [10,132,33,260,65] 13 (by decide) (choices 1) [2,16,64] r33125 c33125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15997
  · exact u15998
  · exact u15999

def r33126 : Route 9 := (fun mask => (mask,id))

def c33126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33126 : Upper (D 6) (R 6) [10,132,33,260,66] 13 := by
  apply FastRouting.sound _ _ [10,132,33,260,66] 13 (by decide) (choices 1) [1,16,64] r33126 c33126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16000
  · exact u16001
  · exact u16002

def r33127 : Route 9 := (fun mask => (mask,id))

def c33127 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33127 : Upper (D 6) (R 6) [10,132,33,260,96] 13 := by
  apply FastRouting.sound _ _ [10,132,33,260,96] 13 (by decide) (choices 1) [1,2,16,64] r33127 c33127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16003
  · exact u16004
  · exact u16005
  · exact u16006

def b33128 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 37 280 19 100 100 228 356), lower := (rows 11 134 37 280 19 32 64 128 256), losses := [] }

theorem u33128 : Upper (D 6) (R 6) [10,132,33,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33129 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 134 37 280 21 98 98 226 354), lower := (rows 11 134 37 280 21 32 64 128 256), losses := [] }

theorem u33129 : Upper (D 6) (R 6) [10,132,33,272,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33130 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 37 280 22 97 97 225 353), lower := (rows 11 134 37 280 22 32 64 128 256), losses := [] }

theorem u33130 : Upper (D 6) (R 6) [10,132,33,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33131 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 16, targets := 66 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 11 134 37 280 49 102 70 198 326), lower := (rows 11 134 37 280 49 32 64 128 256), losses := [] }

theorem u33131 : Upper (D 6) (R 6) [10,132,33,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33132 : Route 9 := (fun mask => (mask,id))

def c33132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33132 : Upper (D 6) (R 6) [10,132,33,272,34] 13 := by
  apply FastRouting.sound _ _ [10,132,33,272,34] 13 (by decide) (choices 1) [1,4,64] r33132 c33132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16007
  · exact u16008
  · exact u16009

def b33133 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 37 280 52 99 67 195 323), lower := (rows 11 134 37 280 52 32 64 128 256), losses := [] }

theorem u33133 : Upper (D 6) (R 6) [10,132,33,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33134 : Route 9 := (fun mask => (mask,id))

def c33134 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33134 : Upper (D 6) (R 6) [10,132,33,272,65] 13 := by
  apply FastRouting.sound _ _ [10,132,33,272,65] 13 (by decide) (choices 1) [2,4,64] r33134 c33134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16010
  · exact u16011
  · exact u16012

def r33135 : Route 9 := (fun mask => (mask,id))

def c33135 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33135 : Upper (D 6) (R 6) [10,132,33,272,66] 13 := by
  apply FastRouting.sound _ _ [10,132,33,272,66] 13 (by decide) (choices 1) [1,4,64] r33135 c33135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16013
  · exact u16014
  · exact u16015

def r33136 : Route 9 := (fun mask => (mask,id))

def c33136 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33136 : Upper (D 6) (R 6) [10,132,33,272,68] 13 := by
  apply FastRouting.sound _ _ [10,132,33,272,68] 13 (by decide) (choices 1) [1,2,64] r33136 c33136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16016
  · exact u16017
  · exact u16018

def r33137 : Route 9 := (fun mask => (mask,id))

def c33137 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33137 : Upper (D 6) (R 6) [10,132,33,272,96] 13 := by
  apply FastRouting.sound _ _ [10,132,33,272,96] 13 (by decide) (choices 1) [1,2,4,64] r33137 c33137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16019
  · exact u16020
  · exact u16021
  · exact u16022

def b33138 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 37 296 19 116 84 212 340), lower := (rows 11 134 37 296 19 32 64 128 256), losses := [] }

theorem u33138 : Upper (D 6) (R 6) [10,132,33,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33139 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 16, targets := 66 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 11 134 37 296 21 114 82 210 338), lower := (rows 11 134 37 296 21 32 64 128 256), losses := [] }

theorem u33139 : Upper (D 6) (R 6) [10,132,33,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33140 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 37 296 22 113 81 209 337), lower := (rows 11 134 37 296 22 32 64 128 256), losses := [] }

theorem u33140 : Upper (D 6) (R 6) [10,132,33,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33141 : Route 9 := (fun mask => (mask,id))

def c33141 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33141 : Upper (D 6) (R 6) [10,132,33,288,65] 13 := by
  apply FastRouting.sound _ _ [10,132,33,288,65] 13 (by decide) (choices 1) [2,4,16,64] r33141 c33141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16023
  · exact u16024
  · exact u16025
  · exact u16026

def r33142 : Route 9 := (fun mask => (mask,id))

def c33142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33142 : Upper (D 6) (R 6) [10,132,33,288,66] 13 := by
  apply FastRouting.sound _ _ [10,132,33,288,66] 13 (by decide) (choices 1) [1,4,16,64] r33142 c33142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16027
  · exact u16028
  · exact u16029
  · exact u16030

def r33143 : Route 9 := (fun mask => (mask,id))

def c33143 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33143 : Upper (D 6) (R 6) [10,132,33,288,68] 13 := by
  apply FastRouting.sound _ _ [10,132,33,288,68] 13 (by decide) (choices 1) [1,2,16,64] r33143 c33143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16031
  · exact u16032
  · exact u16033
  · exact u16034

def b33144 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 37 328 19 116 116 244 372), lower := (rows 11 134 37 328 19 32 64 128 256), losses := [] }

theorem u33144 : Upper (D 6) (R 6) [10,132,33,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33145 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 134 37 328 21 114 114 242 370), lower := (rows 11 134 37 328 21 32 64 128 256), losses := [] }

theorem u33145 : Upper (D 6) (R 6) [10,132,33,320,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33146 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 37 328 22 113 113 241 369), lower := (rows 11 134 37 328 22 32 64 128 256), losses := [] }

theorem u33146 : Upper (D 6) (R 6) [10,132,33,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33147 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 16, targets := 66 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 11 134 37 328 49 118 86 214 342), lower := (rows 11 134 37 328 49 32 64 128 256), losses := [] }

theorem u33147 : Upper (D 6) (R 6) [10,132,33,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33148 : Route 9 := (fun mask => (mask,id))

def c33148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33148 : Upper (D 6) (R 6) [10,132,33,320,34] 13 := by
  apply FastRouting.sound _ _ [10,132,33,320,34] 13 (by decide) (choices 1) [1,4,16,64] r33148 c33148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16035
  · exact u16036
  · exact u16037
  · exact u16038

def b33149 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 37 328 52 115 83 211 339), lower := (rows 11 134 37 328 52 32 64 128 256), losses := [] }

theorem u33149 : Upper (D 6) (R 6) [10,132,33,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33150 : Route 9 := (fun mask => (mask,id))

def c33150 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33150 : Upper (D 6) (R 6) [10,132,33,320,65] 13 := by
  apply FastRouting.sound _ _ [10,132,33,320,65] 13 (by decide) (choices 1) [2,4,16] r33150 c33150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16039
  · exact u16040
  · exact u16041

def r33151 : Route 9 := (fun mask => (mask,id))

def c33151 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33151 : Upper (D 6) (R 6) [10,132,33,320,66] 13 := by
  apply FastRouting.sound _ _ [10,132,33,320,66] 13 (by decide) (choices 1) [1,4,16] r33151 c33151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16042
  · exact u16043
  · exact u16044

def r33152 : Route 9 := (fun mask => (mask,id))

def c33152 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33152 : Upper (D 6) (R 6) [10,132,33,320,68] 13 := by
  apply FastRouting.sound _ _ [10,132,33,320,68] 13 (by decide) (choices 1) [1,2,16] r33152 c33152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16045
  · exact u16046
  · exact u16047

def r33153 : Route 9 := (fun mask => (mask,id))

def c33153 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33153 : Upper (D 6) (R 6) [10,132,33,320,96] 13 := by
  apply FastRouting.sound _ _ [10,132,33,320,96] 13 (by decide) (choices 1) [1,2,4,16] r33153 c33153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16048
  · exact u16049
  · exact u16050
  · exact u16051

def b33154 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 38 25 21 352 352 480 352), lower := (rows 11 134 38 25 21 32 64 128 256), losses := [] }

theorem u33154 : Upper (D 6) (R 6) [10,132,34,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33155 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 134 38 25 49 356 324 452 324), lower := (rows 11 134 38 25 49 32 64 128 256), losses := [] }

theorem u33155 : Upper (D 6) (R 6) [10,132,34,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33156 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 134 38 25 52 353 321 449 321), lower := (rows 11 134 38 25 52 32 64 128 256), losses := [] }

theorem u33156 : Upper (D 6) (R 6) [10,132,34,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33157 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 134 38 25 81 356 356 484 356), lower := (rows 11 134 38 25 81 32 64 128 256), losses := [] }

theorem u33157 : Upper (D 6) (R 6) [10,132,34,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33158 : Route 9 := (fun mask => (mask,id))

def c33158 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33158 : Upper (D 6) (R 6) [10,132,34,17,68] 13 := by
  apply FastRouting.sound _ _ [10,132,34,17,68] 13 (by decide) (choices 1) [1,64,256] r33158 c33158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16052
  · exact u16053
  · exact u16054

def r33159 : Route 9 := (fun mask => (mask,id))

def c33159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33159 : Upper (D 6) (R 6) [10,132,34,17,96] 13 := by
  apply FastRouting.sound _ _ [10,132,34,17,96] 13 (by decide) (choices 1) [1,4,64,256] r33159 c33159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16055
  · exact u16056
  · exact u16057
  · exact u16058

def b33160 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 134 38 25 273 100 100 228 356), lower := (rows 11 134 38 25 273 32 64 128 256), losses := [] }

theorem u33160 : Upper (D 6) (R 6) [10,132,34,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33161 : Route 9 := (fun mask => (mask,id))

def c33161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33161 : Upper (D 6) (R 6) [10,132,34,17,260] 13 := by
  apply FastRouting.sound _ _ [10,132,34,17,260] 13 (by decide) (choices 1) [1,64] r33161 c33161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16059
  · exact u16060

def r33162 : Route 9 := (fun mask => (mask,id))

def c33162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33162 : Upper (D 6) (R 6) [10,132,34,17,288] 13 := by
  apply FastRouting.sound _ _ [10,132,34,17,288] 13 (by decide) (choices 1) [1,4,64] r33162 c33162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16061
  · exact u16062
  · exact u16063

def r33163 : Route 9 := (fun mask => (mask,id))

def c33163 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33163 : Upper (D 6) (R 6) [10,132,34,17,320] 13 := by
  apply FastRouting.sound _ _ [10,132,34,17,320] 13 (by decide) (choices 1) [1,4,64] r33163 c33163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16064
  · exact u16065
  · exact u16066

def b33164 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 134 38 28 49 353 321 449 321), lower := (rows 11 134 38 28 49 32 64 128 256), losses := [] }

theorem u33164 : Upper (D 6) (R 6) [10,132,34,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33165 : Route 9 := (fun mask => (mask,id))

def c33165 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33165 : Upper (D 6) (R 6) [10,132,34,20,65] 13 := by
  apply FastRouting.sound _ _ [10,132,34,20,65] 13 (by decide) (choices 1) [1,64,256] r33165 c33165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16067
  · exact u16068
  · exact u16069

def b33166 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 3, region := 451, targets := 32 }], pairs := [(0,5),(4,1),(4,2)], upper := (rows 11 134 38 28 112 353 321 449 321), lower := (rows 11 134 38 28 112 32 64 128 256), losses := [] }

theorem u33166 : Upper (D 6) (R 6) [10,132,34,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33167 : Route 9 := (fun mask => (mask,id))

def c33167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33167 : Upper (D 6) (R 6) [10,132,34,20,257] 13 := by
  apply FastRouting.sound _ _ [10,132,34,20,257] 13 (by decide) (choices 1) [1,64] r33167 c33167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16070
  · exact u16071

def b33168 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(4,1),(4,2)], upper := (rows 11 134 38 28 304 97 65 193 321), lower := (rows 11 134 38 28 304 32 64 128 256), losses := [] }

theorem u33168 : Upper (D 6) (R 6) [10,132,34,20,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33169 : Route 9 := (fun mask => (mask,id))

def c33169 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33169 : Upper (D 6) (R 6) [10,132,34,20,320] 13 := by
  apply FastRouting.sound _ _ [10,132,34,20,320] 13 (by decide) (choices 1) [1,64] r33169 c33169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16072
  · exact u16073

def b33170 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 134 38 56 21 353 321 449 321), lower := (rows 11 134 38 56 21 32 64 128 256), losses := [] }

theorem u33170 : Upper (D 6) (R 6) [10,132,34,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33171 : Route 9 := (fun mask => (mask,id))

def c33171 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33171 : Upper (D 6) (R 6) [10,132,34,48,65] 13 := by
  apply FastRouting.sound _ _ [10,132,34,48,65] 13 (by decide) (choices 1) [1,4,64,256] r33171 c33171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16074
  · exact u16075
  · exact u16076
  · exact u16077

def r33172 : Route 9 := (fun mask => (mask,id))

def c33172 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33172 : Upper (D 6) (R 6) [10,132,34,48,68] 13 := by
  apply FastRouting.sound _ _ [10,132,34,48,68] 13 (by decide) (choices 1) [1,64,256] r33172 c33172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16078
  · exact u16079
  · exact u16080

def r33173 : Route 9 := (fun mask => (mask,id))

def c33173 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33173 : Upper (D 6) (R 6) [10,132,34,48,257] 13 := by
  apply FastRouting.sound _ _ [10,132,34,48,257] 13 (by decide) (choices 1) [1,4,64] r33173 c33173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16081
  · exact u16082
  · exact u16083

def r33174 : Route 9 := (fun mask => (mask,id))

def c33174 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33174 : Upper (D 6) (R 6) [10,132,34,48,260] 13 := by
  apply FastRouting.sound _ _ [10,132,34,48,260] 13 (by decide) (choices 1) [1,64] r33174 c33174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16084
  · exact u16085

def r33175 : Route 9 := (fun mask => (mask,id))

def c33175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33175 : Upper (D 6) (R 6) [10,132,34,48,320] 13 := by
  apply FastRouting.sound _ _ [10,132,34,48,320] 13 (by decide) (choices 1) [1,4,64] r33175 c33175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16086
  · exact u16087
  · exact u16088

def b33176 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 134 38 73 21 368 368 496 368), lower := (rows 11 134 38 73 21 32 64 128 256), losses := [] }

theorem u33176 : Upper (D 6) (R 6) [10,132,34,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33177 : Route 9 := (fun mask => (mask,id))

def c33177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u33177 : Upper (D 6) (R 6) [10,132,34,65,33] 13 := by
  apply FastRouting.sound _ _ [10,132,34,65,33] 13 (by decide) (choices 1) [4,16,64,256] r33177 c33177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16089
  · exact u16090
  · exact u16091
  · exact u16092

def b33178 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 38 73 52 369 337 465 337), lower := (rows 11 134 38 73 52 32 64 128 256), losses := [] }

theorem u33178 : Upper (D 6) (R 6) [10,132,34,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33179 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 134 38 73 81 308 372 436 308), lower := (rows 11 134 38 73 81 32 64 128 256), losses := [] }

theorem u33179 : Upper (D 6) (R 6) [10,132,34,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u33179
end Delivery.IrregularNine14.P06
