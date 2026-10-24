import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0367
import IrregularNine14P06C0368
import IrregularNine14P06C0369

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b37140 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 76 28 82 293 357 421 293), lower := (rows 35 131 76 28 82 32 64 128 256), losses := [] }

theorem u37140 : Upper (D 6) (R 6) [34,129,72,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37141 : PairBound 9 := { available := 291, camps := [{ cop := 6, region := 28, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 76 28 84 291 355 419 291), lower := (rows 35 131 76 28 84 32 64 128 256), losses := [] }

theorem u37141 : Upper (D 6) (R 6) [34,129,72,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37142 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 76 28 112 295 327 391 263), lower := (rows 35 131 76 28 112 32 64 128 256), losses := [] }

theorem u37142 : Upper (D 6) (R 6) [34,129,72,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37143 : Route 9 := (fun mask => (mask,id))

def c37143 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37143 : Upper (D 6) (R 6) [34,129,72,20,257] 13 := by
  apply FastRouting.sound _ _ [34,129,72,20,257] 13 (by decide) (choices 1) [2,4,64] r37143 c37143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22055
  · exact u22056
  · exact u22057

def r37144 : Route 9 := (fun mask => (mask,id))

def c37144 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37144 : Upper (D 6) (R 6) [34,129,72,20,258] 13 := by
  apply FastRouting.sound _ _ [34,129,72,20,258] 13 (by decide) (choices 1) [1,4,64] r37144 c37144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22058
  · exact u22059
  · exact u22060

def b37145 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 76 28 276 99 99 227 355), lower := (rows 35 131 76 28 276 32 64 128 256), losses := [] }

theorem u37145 : Upper (D 6) (R 6) [34,129,72,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37146 : Route 9 := (fun mask => (mask,id))

def c37146 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37146 : Upper (D 6) (R 6) [34,129,72,20,288] 13 := by
  apply FastRouting.sound _ _ [34,129,72,20,288] 13 (by decide) (choices 1) [1,2,4,64] r37146 c37146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22061
  · exact u22062
  · exact u22063
  · exact u22064

def b37147 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 76 28 336 39 103 167 295), lower := (rows 35 131 76 28 336 32 64 128 256), losses := [] }

theorem u37147 : Upper (D 6) (R 6) [34,129,72,20,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37148 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 44 19 372 340 468 340), lower := (rows 35 131 76 44 19 32 64 128 256), losses := [] }

theorem u37148 : Upper (D 6) (R 6) [34,129,72,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37149 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 483, targets := 4 },{ cop := 4, region := 450, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 131 76 44 21 370 338 466 338), lower := (rows 35 131 76 44 21 32 64 128 256), losses := [] }

theorem u37149 : Upper (D 6) (R 6) [34,129,72,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37150 : Route 9 := (fun mask => (mask,id))

def c37150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u37150 : Upper (D 6) (R 6) [34,129,72,36,6] 13 := by
  apply FastRouting.sound _ _ [34,129,72,36,6] 13 (by decide) (choices 1) [1,16,64,256] r37150 c37150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22065
  · exact u22066
  · exact u22067
  · exact u22068

def r37151 : Route 9 := (fun mask => (mask,id))

def c37151 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37151 : Upper (D 6) (R 6) [34,129,72,36,65] 13 := by
  apply FastRouting.sound _ _ [34,129,72,36,65] 13 (by decide) (choices 1) [2,4,16,256] r37151 c37151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22069
  · exact u22070
  · exact u22071
  · exact u22072

def r37152 : Route 9 := (fun mask => (mask,id))

def c37152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37152 : Upper (D 6) (R 6) [34,129,72,36,66] 13 := by
  apply FastRouting.sound _ _ [34,129,72,36,66] 13 (by decide) (choices 1) [1,4,16,256] r37152 c37152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22073
  · exact u22074
  · exact u22075
  · exact u22076

def b37153 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 76 44 84 307 339 403 275), lower := (rows 35 131 76 44 84 32 64 128 256), losses := [] }

theorem u37153 : Upper (D 6) (R 6) [34,129,72,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37154 : Route 9 := (fun mask => (mask,id))

def c37154 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37154 : Upper (D 6) (R 6) [34,129,72,36,257] 13 := by
  apply FastRouting.sound _ _ [34,129,72,36,257] 13 (by decide) (choices 1) [2,4,16,64] r37154 c37154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22077
  · exact u22078
  · exact u22079
  · exact u22080

def r37155 : Route 9 := (fun mask => (mask,id))

def c37155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37155 : Upper (D 6) (R 6) [34,129,72,36,258] 13 := by
  apply FastRouting.sound _ _ [34,129,72,36,258] 13 (by decide) (choices 1) [1,4,16,64] r37155 c37155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22081
  · exact u22082
  · exact u22083
  · exact u22084

def r37156 : Route 9 := (fun mask => (mask,id))

def c37156 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37156 : Upper (D 6) (R 6) [34,129,72,36,260] 13 := by
  apply FastRouting.sound _ _ [34,129,72,36,260] 13 (by decide) (choices 1) [1,2,16,64] r37156 c37156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22085
  · exact u22086
  · exact u22087
  · exact u22088

def r37157 : Route 9 := (fun mask => (mask,id))

def c37157 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37157 : Upper (D 6) (R 6) [34,129,72,36,320] 13 := by
  apply FastRouting.sound _ _ [34,129,72,36,320] 13 (by decide) (choices 1) [1,2,4,16] r37157 c37157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22089
  · exact u22090
  · exact u22091
  · exact u22092

def b37158 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 131 76 56 19 356 324 452 324), lower := (rows 35 131 76 56 19 32 64 128 256), losses := [] }

theorem u37158 : Upper (D 6) (R 6) [34,129,72,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37159 : Route 9 := (fun mask => (mask,id))

def c37159 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37159 : Upper (D 6) (R 6) [34,129,72,48,5] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48,5] 13 (by decide) (choices 1) [2,4,64,256] r37159 c37159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22093
  · exact u22094
  · exact u22095
  · exact u22096

def r37160 : Route 9 := (fun mask => (mask,id))

def c37160 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u37160 : Upper (D 6) (R 6) [34,129,72,48,6] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48,6] 13 (by decide) (choices 1) [1,4,64,256] r37160 c37160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22097
  · exact u22098
  · exact u22099
  · exact u22100

def r37161 : Route 9 := (fun mask => (mask,id))

def c37161 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37161 : Upper (D 6) (R 6) [34,129,72,48,65] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48,65] 13 (by decide) (choices 1) [2,4,256] r37161 c37161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22101
  · exact u22102
  · exact u22103

def r37162 : Route 9 := (fun mask => (mask,id))

def c37162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u37162 : Upper (D 6) (R 6) [34,129,72,48,66] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48,66] 13 (by decide) (choices 1) [1,4,256] r37162 c37162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22104
  · exact u22105
  · exact u22106

def b37163 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 76 56 84 295 327 391 263), lower := (rows 35 131 76 56 84 32 64 128 256), losses := [] }

theorem u37163 : Upper (D 6) (R 6) [34,129,72,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37164 : Route 9 := (fun mask => (mask,id))

def c37164 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37164 : Upper (D 6) (R 6) [34,129,72,48,257] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48,257] 13 (by decide) (choices 1) [2,4,64] r37164 c37164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22107
  · exact u22108
  · exact u22109

def r37165 : Route 9 := (fun mask => (mask,id))

def c37165 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37165 : Upper (D 6) (R 6) [34,129,72,48,258] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48,258] 13 (by decide) (choices 1) [1,4,64] r37165 c37165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22110
  · exact u22111
  · exact u22112

def r37166 : Route 9 := (fun mask => (mask,id))

def c37166 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37166 : Upper (D 6) (R 6) [34,129,72,48,260] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48,260] 13 (by decide) (choices 1) [1,2,4,64] r37166 c37166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22113
  · exact u22114
  · exact u22115
  · exact u22116

def r37167 : Route 9 := (fun mask => (mask,id))

def c37167 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37167 : Upper (D 6) (R 6) [34,129,72,48,320] 13 := by
  apply FastRouting.sound _ _ [34,129,72,48,320] 13 (by decide) (choices 1) [1,2,4] r37167 c37167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22117
  · exact u22118
  · exact u22119

def r37168 : Route 9 := (fun mask => (mask,id))

def c37168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37168 : Upper (D 6) (R 6) [34,129,72,257,6] 13 := by
  apply FastRouting.sound _ _ [34,129,72,257,6] 13 (by decide) (choices 1) [4,16,64] r37168 c37168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22120
  · exact u22121
  · exact u22122

def b37169 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 131 76 265 50 116 84 212 340), lower := (rows 35 131 76 265 50 32 64 128 256), losses := [] }

theorem u37169 : Upper (D 6) (R 6) [34,129,72,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37170 : Route 9 := (fun mask => (mask,id))

def c37170 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37170 : Upper (D 6) (R 6) [34,129,72,257,36] 13 := by
  apply FastRouting.sound _ _ [34,129,72,257,36] 13 (by decide) (choices 1) [2,4,16,64] r37170 c37170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22123
  · exact u22124
  · exact u22125
  · exact u22126

def r37171 : Route 9 := (fun mask => (mask,id))

def c37171 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37171 : Upper (D 6) (R 6) [34,129,72,257,66] 13 := by
  apply FastRouting.sound _ _ [34,129,72,257,66] 13 (by decide) (choices 1) [4,16] r37171 c37171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22127
  · exact u22128

def b37172 : PairBound 9 := { available := 54, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 76 265 84 54 118 182 310), lower := (rows 35 131 76 265 84 32 64 128 256), losses := [] }

theorem u37172 : Upper (D 6) (R 6) [34,129,72,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37173 : Route 9 := (fun mask => (mask,id))

def c37173 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37173 : Upper (D 6) (R 6) [34,129,72,257,96] 13 := by
  apply FastRouting.sound _ _ [34,129,72,257,96] 13 (by decide) (choices 1) [2,4,16] r37173 c37173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22129
  · exact u22130
  · exact u22131

def r37174 : Route 9 := (fun mask => (mask,id))

def c37174 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37174 : Upper (D 6) (R 6) [34,129,72,258,5] 13 := by
  apply FastRouting.sound _ _ [34,129,72,258,5] 13 (by decide) (choices 1) [4,16,64] r37174 c37174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22132
  · exact u22133
  · exact u22134

def b37175 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 131 76 266 49 116 84 212 340), lower := (rows 35 131 76 266 49 32 64 128 256), losses := [] }

theorem u37175 : Upper (D 6) (R 6) [34,129,72,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37176 : Route 9 := (fun mask => (mask,id))

def c37176 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37176 : Upper (D 6) (R 6) [34,129,72,258,36] 13 := by
  apply FastRouting.sound _ _ [34,129,72,258,36] 13 (by decide) (choices 1) [1,4,16,64] r37176 c37176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22135
  · exact u22136
  · exact u22137
  · exact u22138

def r37177 : Route 9 := (fun mask => (mask,id))

def c37177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37177 : Upper (D 6) (R 6) [34,129,72,258,65] 13 := by
  apply FastRouting.sound _ _ [34,129,72,258,65] 13 (by decide) (choices 1) [4,16] r37177 c37177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22139
  · exact u22140

def b37178 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 76 266 84 53 117 181 309), lower := (rows 35 131 76 266 84 32 64 128 256), losses := [] }

theorem u37178 : Upper (D 6) (R 6) [34,129,72,258,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37179 : Route 9 := (fun mask => (mask,id))

def c37179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37179 : Upper (D 6) (R 6) [34,129,72,258,96] 13 := by
  apply FastRouting.sound _ _ [34,129,72,258,96] 13 (by decide) (choices 1) [1,4,16] r37179 c37179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22141
  · exact u22142
  · exact u22143

def b37180 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 268 19 116 116 244 372), lower := (rows 35 131 76 268 19 32 64 128 256), losses := [] }

theorem u37180 : Upper (D 6) (R 6) [34,129,72,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37181 : Route 9 := (fun mask => (mask,id))

def c37181 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37181 : Upper (D 6) (R 6) [34,129,72,260,5] 13 := by
  apply FastRouting.sound _ _ [34,129,72,260,5] 13 (by decide) (choices 1) [2,16,64] r37181 c37181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22144
  · exact u22145
  · exact u22146

def r37182 : Route 9 := (fun mask => (mask,id))

def c37182 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37182 : Upper (D 6) (R 6) [34,129,72,260,6] 13 := by
  apply FastRouting.sound _ _ [34,129,72,260,6] 13 (by decide) (choices 1) [1,16,64] r37182 c37182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22147
  · exact u22148
  · exact u22149

def b37183 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 131 76 268 49 118 86 214 342), lower := (rows 35 131 76 268 49 32 64 128 256), losses := [] }

theorem u37183 : Upper (D 6) (R 6) [34,129,72,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37184 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 131 76 268 50 117 85 213 341), lower := (rows 35 131 76 268 50 32 64 128 256), losses := [] }

theorem u37184 : Upper (D 6) (R 6) [34,129,72,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37185 : Route 9 := (fun mask => (mask,id))

def c37185 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37185 : Upper (D 6) (R 6) [34,129,72,260,36] 13 := by
  apply FastRouting.sound _ _ [34,129,72,260,36] 13 (by decide) (choices 1) [1,2,16,64] r37185 c37185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22150
  · exact u22151
  · exact u22152
  · exact u22153

def r37186 : Route 9 := (fun mask => (mask,id))

def c37186 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37186 : Upper (D 6) (R 6) [34,129,72,260,65] 13 := by
  apply FastRouting.sound _ _ [34,129,72,260,65] 13 (by decide) (choices 1) [2,4,16] r37186 c37186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22154
  · exact u22155
  · exact u22156

def r37187 : Route 9 := (fun mask => (mask,id))

def c37187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37187 : Upper (D 6) (R 6) [34,129,72,260,66] 13 := by
  apply FastRouting.sound _ _ [34,129,72,260,66] 13 (by decide) (choices 1) [1,4,16] r37187 c37187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22157
  · exact u22158
  · exact u22159

def b37188 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 76 268 84 51 115 179 307), lower := (rows 35 131 76 268 84 32 64 128 256), losses := [] }

theorem u37188 : Upper (D 6) (R 6) [34,129,72,260,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37189 : Route 9 := (fun mask => (mask,id))

def c37189 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37189 : Upper (D 6) (R 6) [34,129,72,260,96] 13 := by
  apply FastRouting.sound _ _ [34,129,72,260,96] 13 (by decide) (choices 1) [1,2,4,16] r37189 c37189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22160
  · exact u22161
  · exact u22162
  · exact u22163

def b37190 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 76 280 19 100 100 228 356), lower := (rows 35 131 76 280 19 32 64 128 256), losses := [] }

theorem u37190 : Upper (D 6) (R 6) [34,129,72,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37191 : Route 9 := (fun mask => (mask,id))

def c37191 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37191 : Upper (D 6) (R 6) [34,129,72,272,5] 13 := by
  apply FastRouting.sound _ _ [34,129,72,272,5] 13 (by decide) (choices 1) [2,4,64] r37191 c37191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22164
  · exact u22165
  · exact u22166

def r37192 : Route 9 := (fun mask => (mask,id))

def c37192 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37192 : Upper (D 6) (R 6) [34,129,72,272,6] 13 := by
  apply FastRouting.sound _ _ [34,129,72,272,6] 13 (by decide) (choices 1) [1,4,64] r37192 c37192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22167
  · exact u22168
  · exact u22169

def b37193 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 131 76 280 49 102 70 198 326), lower := (rows 35 131 76 280 49 32 64 128 256), losses := [] }

theorem u37193 : Upper (D 6) (R 6) [34,129,72,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37194 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 131 76 280 50 101 69 197 325), lower := (rows 35 131 76 280 50 32 64 128 256), losses := [] }

theorem u37194 : Upper (D 6) (R 6) [34,129,72,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37195 : Route 9 := (fun mask => (mask,id))

def c37195 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37195 : Upper (D 6) (R 6) [34,129,72,272,36] 13 := by
  apply FastRouting.sound _ _ [34,129,72,272,36] 13 (by decide) (choices 1) [1,2,4,64] r37195 c37195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22170
  · exact u22171
  · exact u22172
  · exact u22173

def r37196 : Route 9 := (fun mask => (mask,id))

def c37196 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37196 : Upper (D 6) (R 6) [34,129,72,272,65] 13 := by
  apply FastRouting.sound _ _ [34,129,72,272,65] 13 (by decide) (choices 1) [2,4] r37196 c37196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22174
  · exact u22175

def r37197 : Route 9 := (fun mask => (mask,id))

def c37197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37197 : Upper (D 6) (R 6) [34,129,72,272,66] 13 := by
  apply FastRouting.sound _ _ [34,129,72,272,66] 13 (by decide) (choices 1) [1,4] r37197 c37197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22176
  · exact u22177

def b37198 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 76 280 84 39 103 167 295), lower := (rows 35 131 76 280 84 32 64 128 256), losses := [] }

theorem u37198 : Upper (D 6) (R 6) [34,129,72,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37199 : Route 9 := (fun mask => (mask,id))

def c37199 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37199 : Upper (D 6) (R 6) [34,129,72,272,96] 13 := by
  apply FastRouting.sound _ _ [34,129,72,272,96] 13 (by decide) (choices 1) [1,2,4] r37199 c37199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22178
  · exact u22179
  · exact u22180

#print axioms u37199
end Delivery.IrregularNine14.P06
