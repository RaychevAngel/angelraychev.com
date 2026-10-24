import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0018

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4140 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 52, targets := 65 },{ cop := 2, region := 211, targets := 256 }], pairs := [(0,8),(2,0),(2,6),(4,0),(4,6)], upper := (rows 35 67 44 392 148 288 81 209 337), lower := (rows 35 67 44 392 148 288 64 128 256), losses := [] }

theorem u4140 : Upper (D 9) (R 9) [34,65,40,384,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4140 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4141 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 472, targets := 33 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,5)], upper := (rows 35 67 44 392 208 33 340 404 276), lower := (rows 35 67 44 392 208 33 64 128 256), losses := [] }

theorem u4141 : Upper (D 9) (R 9) [34,65,40,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4141 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4142 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 36, targets := 449 }], pairs := [(2,0),(2,6),(2,7),(2,8)], upper := (rows 35 67 44 392 208 36 337 401 273), lower := (rows 35 67 44 392 208 36 64 128 256), losses := [] }

theorem u4142 : Upper (D 9) (R 9) [34,65,40,384,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4142 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4143 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 392 208 48 325 389 261), lower := (rows 35 67 44 392 208 48 64 128 256), losses := [] }

theorem u4143 : Upper (D 9) (R 9) [34,65,40,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4143 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4144 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 211, targets := 256 },{ cop := 3, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(4,8)], upper := (rows 35 67 44 392 208 288 85 149 277), lower := (rows 35 67 44 392 208 288 64 128 256), losses := [] }

theorem u4144 : Upper (D 9) (R 9) [34,65,40,384,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4144 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4145 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 76 137 176 36 336 400 272), lower := (rows 35 67 76 137 176 36 64 128 256), losses := [] }

theorem u4145 : Upper (D 9) (R 9) [34,65,72,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4145 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4146 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 7, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 67 76 137 176 48 324 388 260), lower := (rows 35 67 76 137 176 48 64 128 256), losses := [] }

theorem u4146 : Upper (D 9) (R 9) [34,65,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4146 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4147 : Route 9 := (fun mask => (mask,id))

def c4147 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4147 : Upper (D 9) (R 9) [34,65,72,129,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,160,256] 13 (by decide) (choices 1) [4,16,256] r4147 c4147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1081
  · exact u1082
  · exact u1083

def b4148 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 0, region := 392, targets := 64 },{ cop := 2, region := 432, targets := 64 }], pairs := [(2,0),(3,6),(4,0),(4,6)], upper := (rows 35 67 76 137 276 48 480 416 416), lower := (rows 35 67 76 137 276 48 64 128 256), losses := [] }

theorem u4148 : Upper (D 9) (R 9) [34,65,72,129,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4148 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4149 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 2, region := 432, targets := 64 }], pairs := [(0,8),(1,8),(2,0),(4,0),(4,6)], upper := (rows 35 67 76 137 276 160 368 432 304), lower := (rows 35 67 76 137 276 160 64 128 256), losses := [{ target := 8, region := (rows 5 6 4 8 16 168 64 128 0), good := (rows 35 67 111 169 23 160 64 160 0) }] }

theorem u4149 : Upper (D 9) (R 9) [34,65,72,129,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4149 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4150 : Route 9 := (fun mask => (mask,id))

def c4150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4150 : Upper (D 9) (R 9) [34,65,72,129,260,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,260,256] 13 (by decide) (choices 1) [16,32,128] r4150 c4150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1084
  · exact u1085
  · exact u1086

def b4151 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 76 137 304 36 464 400 400), lower := (rows 35 67 76 137 304 36 64 128 256), losses := [] }

theorem u4151 : Upper (D 9) (R 9) [34,65,72,129,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4151 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4152 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 67 76 137 304 48 452 388 388), lower := (rows 35 67 76 137 304 48 64 128 256), losses := [] }

theorem u4152 : Upper (D 9) (R 9) [34,65,72,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4152 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4153 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 2, region := 432, targets := 64 }], pairs := [(0,8),(1,8),(2,0),(4,0),(4,6)], upper := (rows 35 67 76 137 304 160 340 404 276), lower := (rows 35 67 76 137 304 160 64 128 256), losses := [{ target := 8, region := (rows 5 6 4 8 16 168 64 128 0), good := (rows 35 67 111 169 48 160 64 160 0) }] }

theorem u4153 : Upper (D 9) (R 9) [34,65,72,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4153 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4154 : PairBound 9 := { available := 148, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 67 76 137 304 288 212 148 404), lower := (rows 35 67 76 137 304 288 64 128 256), losses := [] }

theorem u4154 : Upper (D 9) (R 9) [34,65,72,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4154 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4155 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 76 137 400 36 368 432 304), lower := (rows 35 67 76 137 400 36 64 128 256), losses := [] }

theorem u4155 : Upper (D 9) (R 9) [34,65,72,129,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4155 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4156 : Route 9 := (fun mask => (mask,id))

def c4156 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4156 : Upper (D 9) (R 9) [34,65,72,129,384,16] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,384,16] 13 (by decide) (choices 1) [4,32,256] r4156 c4156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1087
  · exact u1088
  · exact u1089

def r4157 : Route 9 := (fun mask => (mask,id))

def c4157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4157 : Upper (D 9) (R 9) [34,65,72,129,384,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,384,256] 13 (by decide) (choices 1) [4,16,32] r4157 c4157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1090
  · exact u1091
  · exact u1092

def b4158 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 4, region := 332, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 76 140 176 33 336 400 272), lower := (rows 35 67 76 140 176 33 64 128 256), losses := [] }

theorem u4158 : Upper (D 9) (R 9) [34,65,72,132,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4158 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4159 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 67 76 140 176 48 321 385 257), lower := (rows 35 67 76 140 176 48 64 128 256), losses := [] }

theorem u4159 : Upper (D 9) (R 9) [34,65,72,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4159 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4160 : Route 9 := (fun mask => (mask,id))

def c4160 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4160 : Upper (D 9) (R 9) [34,65,72,132,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,132,160,256] 13 (by decide) (choices 1) [1,16,256] r4160 c4160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1093
  · exact u1094
  · exact u1095

def b4161 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 460, targets := 1 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,6)], upper := (rows 35 67 76 140 273 48 480 416 416), lower := (rows 35 67 76 140 273 48 64 128 256), losses := [] }

theorem u4161 : Upper (D 9) (R 9) [34,65,72,132,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4161 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4162 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,6),(4,7)], upper := (rows 35 67 76 140 273 160 368 432 304), lower := (rows 35 67 76 140 273 160 64 128 256), losses := [] }

theorem u4162 : Upper (D 9) (R 9) [34,65,72,132,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4162 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4163 : Route 9 := (fun mask => (mask,id))

def c4163 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4163 : Upper (D 9) (R 9) [34,65,72,132,257,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,132,257,256] 13 (by decide) (choices 1) [16,32,128] r4163 c4163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1096
  · exact u1097
  · exact u1098

def b4164 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 4, region := 204, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 76 140 304 33 464 400 400), lower := (rows 35 67 76 140 304 33 64 128 256), losses := [] }

theorem u4164 : Upper (D 9) (R 9) [34,65,72,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4164 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4165 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 67 76 140 304 48 449 385 385), lower := (rows 35 67 76 140 304 48 64 128 256), losses := [] }

theorem u4165 : Upper (D 9) (R 9) [34,65,72,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4165 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4166 : PairBound 9 := { available := 273, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,6),(4,7)], upper := (rows 35 67 76 140 304 160 337 401 273), lower := (rows 35 67 76 140 304 160 64 128 256), losses := [] }

theorem u4166 : Upper (D 9) (R 9) [34,65,72,132,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4166 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4167 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 67 76 140 304 288 209 145 401), lower := (rows 35 67 76 140 304 288 64 128 256), losses := [] }

theorem u4167 : Upper (D 9) (R 9) [34,65,72,132,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4167 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4168 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 476, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 76 140 400 33 368 432 304), lower := (rows 35 67 76 140 400 33 64 128 256), losses := [] }

theorem u4168 : Upper (D 9) (R 9) [34,65,72,132,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4168 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4169 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 67 76 140 400 48 353 417 289), lower := (rows 35 67 76 140 400 48 64 128 256), losses := [] }

theorem u4169 : Upper (D 9) (R 9) [34,65,72,132,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4169 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4170 : Route 9 := (fun mask => (mask,id))

def c4170 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4170 : Upper (D 9) (R 9) [34,65,72,132,384,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,132,384,256] 13 (by decide) (choices 1) [1,16,32] r4170 c4170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1099
  · exact u1100
  · exact u1101

def b4171 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 76 152 273 36 480 416 416), lower := (rows 35 67 76 152 273 36 64 128 256), losses := [] }

theorem u4171 : Upper (D 9) (R 9) [34,65,72,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4171 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4172 : Route 9 := (fun mask => (mask,id))

def c4172 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4172 : Upper (D 9) (R 9) [34,65,72,144,257,128] 13 := by
  apply FastRouting.sound _ _ [34,65,72,144,257,128] 13 (by decide) (choices 1) [4,32,256] r4172 c4172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1102
  · exact u1103
  · exact u1104

def r4173 : Route 9 := (fun mask => (mask,id))

def c4173 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4173 : Upper (D 9) (R 9) [34,65,72,144,257,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,144,257,256] 13 (by decide) (choices 1) [4,32,128] r4173 c4173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1105
  · exact u1106
  · exact u1107

def b4174 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 476, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 76 152 276 33 480 416 416), lower := (rows 35 67 76 152 276 33 64 128 256), losses := [] }

theorem u4174 : Upper (D 9) (R 9) [34,65,72,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4174 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4175 : PairBound 9 := { available := 289, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 76 152 276 160 353 417 289), lower := (rows 35 67 76 152 276 160 64 128 256), losses := [{ target := 8, region := (rows 5 6 4 8 16 168 64 128 0), good := (rows 35 67 111 184 23 160 64 160 0) }] }

theorem u4175 : Upper (D 9) (R 9) [34,65,72,144,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4175 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4176 : Route 9 := (fun mask => (mask,id))

def c4176 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4176 : Upper (D 9) (R 9) [34,65,72,144,260,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,144,260,256] 13 (by decide) (choices 1) [1,32,128] r4176 c4176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1108
  · exact u1109
  · exact u1110

def b4177 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 4, region := 204, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 76 152 304 33 452 388 388), lower := (rows 35 67 76 152 304 33 64 128 256), losses := [] }

theorem u4177 : Upper (D 9) (R 9) [34,65,72,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4177 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4178 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 76 152 304 36 449 385 385), lower := (rows 35 67 76 152 304 36 64 128 256), losses := [] }

theorem u4178 : Upper (D 9) (R 9) [34,65,72,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4178 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4179 : Route 9 := (fun mask => (mask,id))

def c4179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4179 : Upper (D 9) (R 9) [34,65,72,144,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,72,144,288,128] 13 (by decide) (choices 1) [1,4,256] r4179 c4179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1111
  · exact u1112
  · exact u1113

def b4180 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 67 76 152 304 288 197 133 389), lower := (rows 35 67 76 152 304 288 64 128 256), losses := [] }

theorem u4180 : Upper (D 9) (R 9) [34,65,72,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4180 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4181 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 76 168 145 36 336 400 272), lower := (rows 35 67 76 168 145 36 64 128 256), losses := [] }

theorem u4181 : Upper (D 9) (R 9) [34,65,72,160,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4181 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4182 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 0, region := 460, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7)], upper := (rows 35 67 76 168 145 48 324 388 260), lower := (rows 35 67 76 168 145 48 64 128 256), losses := [] }

theorem u4182 : Upper (D 9) (R 9) [34,65,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4182 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4183 : Route 9 := (fun mask => (mask,id))

def c4183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4183 : Upper (D 9) (R 9) [34,65,72,160,129,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,129,256] 13 (by decide) (choices 1) [4,16,256] r4183 c4183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1114
  · exact u1115
  · exact u1116

def b4184 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 3, region := 340, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 76 168 148 33 336 400 272), lower := (rows 35 67 76 168 148 33 64 128 256), losses := [] }

theorem u4184 : Upper (D 9) (R 9) [34,65,72,160,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4184 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4185 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 67 76 168 148 48 321 385 257), lower := (rows 35 67 76 168 148 48 64 128 256), losses := [] }

theorem u4185 : Upper (D 9) (R 9) [34,65,72,160,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4185 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4186 : Route 9 := (fun mask => (mask,id))

def c4186 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4186 : Upper (D 9) (R 9) [34,65,72,160,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,132,256] 13 (by decide) (choices 1) [1,16,256] r4186 c4186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1117
  · exact u1118
  · exact u1119

def b4187 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 76 168 273 36 464 400 400), lower := (rows 35 67 76 168 273 36 64 128 256), losses := [] }

theorem u4187 : Upper (D 9) (R 9) [34,65,72,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4187 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4188 : Route 9 := (fun mask => (mask,id))

def c4188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4188 : Upper (D 9) (R 9) [34,65,72,160,257,16] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,257,16] 13 (by decide) (choices 1) [4,128,256] r4188 c4188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1120
  · exact u1121
  · exact u1122

def b4189 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 67 76 168 273 160 340 404 276), lower := (rows 35 67 76 168 273 160 64 128 256), losses := [] }

theorem u4189 : Upper (D 9) (R 9) [34,65,72,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4189 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4190 : Route 9 := (fun mask => (mask,id))

def c4190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4190 : Upper (D 9) (R 9) [34,65,72,160,257,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,257,256] 13 (by decide) (choices 1) [4,16,128] r4190 c4190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1123
  · exact u1124
  · exact u1125

def b4191 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 3, region := 340, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 76 168 276 33 464 400 400), lower := (rows 35 67 76 168 276 33 64 128 256), losses := [] }

theorem u4191 : Upper (D 9) (R 9) [34,65,72,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4191 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4192 : Route 9 := (fun mask => (mask,id))

def c4192 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u4192 : Upper (D 9) (R 9) [34,65,72,160,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,260,16] 13 (by decide) (choices 1) [1,128,256] r4192 c4192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1126
  · exact u1127
  · exact u1128

def b4193 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 67 76 168 276 160 337 401 273), lower := (rows 35 67 76 168 276 160 64 128 256), losses := [] }

theorem u4193 : Upper (D 9) (R 9) [34,65,72,160,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4193 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4194 : Route 9 := (fun mask => (mask,id))

def c4194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4194 : Upper (D 9) (R 9) [34,65,72,160,260,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,260,256] 13 (by decide) (choices 1) [1,16,128] r4194 c4194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1129
  · exact u1130
  · exact u1131

def b4195 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 3, region := 340, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 76 168 400 33 340 404 276), lower := (rows 35 67 76 168 400 33 64 128 256), losses := [] }

theorem u4195 : Upper (D 9) (R 9) [34,65,72,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4195 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4196 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 76 168 400 36 337 401 273), lower := (rows 35 67 76 168 400 36 64 128 256), losses := [] }

theorem u4196 : Upper (D 9) (R 9) [34,65,72,160,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4196 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4197 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 67 76 168 400 48 325 389 261), lower := (rows 35 67 76 168 400 48 64 128 256), losses := [] }

theorem u4197 : Upper (D 9) (R 9) [34,65,72,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4197 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4198 : Route 9 := (fun mask => (mask,id))

def c4198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4198 : Upper (D 9) (R 9) [34,65,72,160,384,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,384,256] 13 (by decide) (choices 1) [1,4,16] r4198 c4198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1132
  · exact u1133
  · exact u1134

def b4199 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 76 392 145 36 368 432 304), lower := (rows 35 67 76 392 145 36 64 128 256), losses := [] }

theorem u4199 : Upper (D 9) (R 9) [34,65,72,384,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4199 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u4199
end Delivery.IrregularNine14.P09
