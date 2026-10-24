import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0018
import IrregularNine14P09C0019

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r4200 : Route 9 := (fun mask => (mask,id))

def c4200 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4200 : Upper (D 9) (R 9) [34,65,72,384,129,16] 13 := by
  apply FastRouting.sound _ _ [34,65,72,384,129,16] 13 (by decide) (choices 1) [4,32,256] r4200 c4200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1135
  · exact u1136
  · exact u1137

def r4201 : Route 9 := (fun mask => (mask,id))

def c4201 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4201 : Upper (D 9) (R 9) [34,65,72,384,129,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,384,129,256] 13 (by decide) (choices 1) [4,16,32] r4201 c4201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1138
  · exact u1139
  · exact u1140

def b4202 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 0, region := 476, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 76 392 148 33 368 432 304), lower := (rows 35 67 76 392 148 33 64 128 256), losses := [] }

theorem u4202 : Upper (D 9) (R 9) [34,65,72,384,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4202 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4203 : Route 9 := (fun mask => (mask,id))

def c4203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4203 : Upper (D 9) (R 9) [34,65,72,384,132,16] 13 := by
  apply FastRouting.sound _ _ [34,65,72,384,132,16] 13 (by decide) (choices 1) [1,32,256] r4203 c4203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1141
  · exact u1142
  · exact u1143

def r4204 : Route 9 := (fun mask => (mask,id))

def c4204 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4204 : Upper (D 9) (R 9) [34,65,72,384,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,384,132,256] 13 (by decide) (choices 1) [1,16,32] r4204 c4204
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1144
  · exact u1145
  · exact u1146

def b4205 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 35, targets := 384 },{ cop := 4, region := 332, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 76 392 176 33 340 404 276), lower := (rows 35 67 76 392 176 33 64 128 256), losses := [] }

theorem u4205 : Upper (D 9) (R 9) [34,65,72,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4205 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4206 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 76 392 176 36 337 401 273), lower := (rows 35 67 76 392 176 36 64 128 256), losses := [] }

theorem u4206 : Upper (D 9) (R 9) [34,65,72,384,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4206 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4207 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 67 76 392 176 48 325 389 261), lower := (rows 35 67 76 392 176 48 64 128 256), losses := [] }

theorem u4207 : Upper (D 9) (R 9) [34,65,72,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4207 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4208 : Route 9 := (fun mask => (mask,id))

def c4208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4208 : Upper (D 9) (R 9) [34,65,72,384,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,72,384,160,256] 13 (by decide) (choices 1) [1,4,16] r4208 c4208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1147
  · exact u1148
  · exact u1149

def b4209 : PairBound 9 := { available := 400, camps := [{ cop := 6, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 100 140 280 33 464 400 400), lower := (rows 35 67 100 140 280 33 64 128 256), losses := [] }

theorem u4209 : Upper (D 9) (R 9) [34,65,96,132,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4209 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4210 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 100 140 280 48 449 385 385), lower := (rows 35 67 100 140 280 48 64 128 256), losses := [] }

theorem u4210 : Upper (D 9) (R 9) [34,65,96,132,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4210 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4211 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 67 100 140 280 160 337 401 273), lower := (rows 35 67 100 140 280 160 64 128 256), losses := [{ target := 7, region := (rows 5 14 4 8 24 32 72 0 264), good := (rows 35 67 103 351 346 32 64 0 256) }] }

theorem u4211 : Upper (D 9) (R 9) [34,65,96,132,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4211 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4212 : Route 9 := (fun mask => (mask,id))

def c4212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4212 : Upper (D 9) (R 9) [34,65,96,132,264,256] 13 := by
  apply FastRouting.sound _ _ [34,65,96,132,264,256] 13 (by decide) (choices 1) [1,16,128] r4212 c4212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1150
  · exact u1151
  · exact u1152

def b4213 : PairBound 9 := { available := 280, camps := [{ cop := 6, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 100 140 400 33 344 408 280), lower := (rows 35 67 100 140 400 33 64 128 256), losses := [] }

theorem u4213 : Upper (D 9) (R 9) [34,65,96,132,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4213 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4214 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 100 140 400 40 337 401 273), lower := (rows 35 67 100 140 400 40 64 128 256), losses := [] }

theorem u4214 : Upper (D 9) (R 9) [34,65,96,132,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4214 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4215 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 100 140 400 48 329 393 265), lower := (rows 35 67 100 140 400 48 64 128 256), losses := [] }

theorem u4215 : Upper (D 9) (R 9) [34,65,96,132,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4215 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4216 : Route 9 := (fun mask => (mask,id))

def c4216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4216 : Upper (D 9) (R 9) [34,65,96,132,384,256] 13 := by
  apply FastRouting.sound _ _ [34,65,96,132,384,256] 13 (by decide) (choices 1) [1,8,16] r4216 c4216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1153
  · exact u1154
  · exact u1155

def b4217 : PairBound 9 := { available := 388, camps := [{ cop := 6, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 100 152 280 33 452 388 388), lower := (rows 35 67 100 152 280 33 64 128 256), losses := [] }

theorem u4217 : Upper (D 9) (R 9) [34,65,96,144,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4217 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4218 : PairBound 9 := { available := 385, camps := [{ cop := 6, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 100 152 280 36 449 385 385), lower := (rows 35 67 100 152 280 36 64 128 256), losses := [] }

theorem u4218 : Upper (D 9) (R 9) [34,65,96,144,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4218 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4219 : PairBound 9 := { available := 261, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 3, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 100 152 280 160 325 389 261), lower := (rows 35 67 100 152 280 160 64 128 256), losses := [] }

theorem u4219 : Upper (D 9) (R 9) [34,65,96,144,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4219 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4220 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 376, targets := 1 },{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 133 152 276 40 352 480 352), lower := (rows 35 67 133 152 276 40 64 128 256), losses := [] }

theorem u4220 : Upper (D 9) (R 9) [34,65,129,144,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4220 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4221 : PairBound 9 := { available := 296, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 133 152 276 96 360 424 296), lower := (rows 35 67 133 152 276 96 64 128 256), losses := [] }

theorem u4221 : Upper (D 9) (R 9) [34,65,129,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4221 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4222 : Route 9 := (fun mask => (mask,id))

def c4222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4222 : Upper (D 9) (R 9) [34,65,129,144,260,256] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,260,256] 13 (by decide) (choices 1) [8,32] r4222 c4222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1156
  · exact u1157

def b4223 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 133 152 280 36 352 480 352), lower := (rows 35 67 133 152 280 36 64 128 256), losses := [] }

theorem u4223 : Upper (D 9) (R 9) [34,65,129,144,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4223 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4224 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 388, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 133 152 280 96 356 420 292), lower := (rows 35 67 133 152 280 96 64 128 256), losses := [] }

theorem u4224 : Upper (D 9) (R 9) [34,65,129,144,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4224 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4225 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 2, region := 376, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,0)], upper := (rows 35 67 133 152 280 288 100 228 356), lower := (rows 35 67 133 152 280 288 64 128 256), losses := [] }

theorem u4225 : Upper (D 9) (R 9) [34,65,129,144,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4225 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4226 : Route 9 := (fun mask => (mask,id))

def c4226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u4226 : Upper (D 9) (R 9) [34,65,129,144,288,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,288,4] 13 (by decide) (choices 1) [8,256] r4226 c4226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1158
  · exact u1159

def b4227 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 376, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,0)], upper := (rows 35 67 133 152 304 40 324 452 324), lower := (rows 35 67 133 152 304 40 64 128 256), losses := [] }

theorem u4227 : Upper (D 9) (R 9) [34,65,129,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4227 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4228 : PairBound 9 := { available := 268, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 133 152 304 96 332 396 268), lower := (rows 35 67 133 152 304 96 64 128 256), losses := [] }

theorem u4228 : Upper (D 9) (R 9) [34,65,129,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4228 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4229 : PairBound 9 := { available := 76, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 67 133 152 304 288 76 204 332), lower := (rows 35 67 133 152 304 288 64 128 256), losses := [] }

theorem u4229 : Upper (D 9) (R 9) [34,65,129,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4229 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4230 : Route 9 := (fun mask => (mask,id))

def c4230 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4230 : Upper (D 9) (R 9) [34,65,129,144,320,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,320,4] 13 (by decide) (choices 1) [8,32,256] r4230 c4230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1160
  · exact u1161
  · exact u1162

def r4231 : Route 9 := (fun mask => (mask,id))

def c4231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4231 : Upper (D 9) (R 9) [34,65,129,144,320,8] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,320,8] 13 (by decide) (choices 1) [4,32,256] r4231 c4231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1163
  · exact u1164
  · exact u1165

def r4232 : Route 9 := (fun mask => (mask,id))

def c4232 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4232 : Upper (D 9) (R 9) [34,65,129,144,320,256] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,320,256] 13 (by decide) (choices 1) [4,8,32] r4232 c4232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1166
  · exact u1167
  · exact u1168

def b4233 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 7, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 35 67 133 168 276 40 336 464 336), lower := (rows 35 67 133 168 276 40 64 128 256), losses := [] }

theorem u4233 : Upper (D 9) (R 9) [34,65,129,160,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4233 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4234 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 376, targets := 1 },{ cop := 3, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 133 168 276 48 328 456 328), lower := (rows 35 67 133 168 276 48 64 128 256), losses := [] }

theorem u4234 : Upper (D 9) (R 9) [34,65,129,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4234 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4235 : PairBound 9 := { available := 280, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 133 168 276 96 344 408 280), lower := (rows 35 67 133 168 276 96 64 128 256), losses := [] }

theorem u4235 : Upper (D 9) (R 9) [34,65,129,160,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4235 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4236 : Route 9 := (fun mask => (mask,id))

def c4236 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4236 : Upper (D 9) (R 9) [34,65,129,160,260,256] 13 := by
  apply FastRouting.sound _ _ [34,65,129,160,260,256] 13 (by decide) (choices 1) [8,16] r4236 c4236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1169
  · exact u1170

def b4237 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 339, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,7)], upper := (rows 35 67 133 168 280 36 336 464 336), lower := (rows 35 67 133 168 280 36 64 128 256), losses := [] }

theorem u4237 : Upper (D 9) (R 9) [34,65,129,160,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4237 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4238 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 376, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,0)], upper := (rows 35 67 133 168 280 48 324 452 324), lower := (rows 35 67 133 168 280 48 64 128 256), losses := [] }

theorem u4238 : Upper (D 9) (R 9) [34,65,129,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4238 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4239 : PairBound 9 := { available := 276, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 133 168 280 96 340 404 276), lower := (rows 35 67 133 168 280 96 64 128 256), losses := [] }

theorem u4239 : Upper (D 9) (R 9) [34,65,129,160,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4239 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4240 : Route 9 := (fun mask => (mask,id))

def c4240 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4240 : Upper (D 9) (R 9) [34,65,129,160,264,256] 13 := by
  apply FastRouting.sound _ _ [34,65,129,160,264,256] 13 (by decide) (choices 1) [4,16] r4240 c4240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1171
  · exact u1172

def b4241 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 339, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,7)], upper := (rows 35 67 133 168 336 36 344 408 280), lower := (rows 35 67 133 168 336 36 64 128 256), losses := [] }

theorem u4241 : Upper (D 9) (R 9) [34,65,129,160,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4241 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4242 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 7, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 35 67 133 168 336 40 340 404 276), lower := (rows 35 67 133 168 336 40 64 128 256), losses := [] }

theorem u4242 : Upper (D 9) (R 9) [34,65,129,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4242 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4243 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 35, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 133 168 336 48 332 396 268), lower := (rows 35 67 133 168 336 48 64 128 256), losses := [] }

theorem u4243 : Upper (D 9) (R 9) [34,65,129,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4243 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4244 : Route 9 := (fun mask => (mask,id))

def c4244 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4244 : Upper (D 9) (R 9) [34,65,129,160,320,256] 13 := by
  apply FastRouting.sound _ _ [34,65,129,160,320,256] 13 (by decide) (choices 1) [4,8,16] r4244 c4244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1173
  · exact u1174
  · exact u1175

def b4245 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 0, region := 404, targets := 64 }], pairs := [(0,8),(1,8),(2,6),(2,8)], upper := (rows 35 67 133 200 276 40 368 432 304), lower := (rows 35 67 133 200 276 40 64 128 256), losses := [] }

theorem u4245 : Upper (D 9) (R 9) [34,65,129,192,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4245 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4246 : Route 9 := (fun mask => (mask,id))

def c4246 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4246 : Upper (D 9) (R 9) [34,65,129,192,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,260,16] 13 (by decide) (choices 1) [8,32,256] r4246 c4246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1176
  · exact u1177
  · exact u1178

def r4247 : Route 9 := (fun mask => (mask,id))

def c4247 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4247 : Upper (D 9) (R 9) [34,65,129,192,260,256] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,260,256] 13 (by decide) (choices 1) [8,16,32] r4247 c4247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1179
  · exact u1180
  · exact u1181

def b4248 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 67 133 200 280 36 368 432 304), lower := (rows 35 67 133 200 280 36 64 128 256), losses := [] }

theorem u4248 : Upper (D 9) (R 9) [34,65,129,192,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4248 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4249 : Route 9 := (fun mask => (mask,id))

def c4249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4249 : Upper (D 9) (R 9) [34,65,129,192,264,16] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,264,16] 13 (by decide) (choices 1) [4,32,256] r4249 c4249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1182
  · exact u1183
  · exact u1184

def r4250 : Route 9 := (fun mask => (mask,id))

def c4250 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4250 : Upper (D 9) (R 9) [34,65,129,192,264,256] 13 := by
  apply FastRouting.sound _ _ [34,65,129,192,264,256] 13 (by decide) (choices 1) [4,16,32] r4250 c4250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1185
  · exact u1186
  · exact u1187

def b4251 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 67 133 200 304 36 344 408 280), lower := (rows 35 67 133 200 304 36 64 128 256), losses := [] }

theorem u4251 : Upper (D 9) (R 9) [34,65,129,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4251 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4252 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 0, region := 404, targets := 64 }], pairs := [(0,8),(1,8),(2,6),(2,8)], upper := (rows 35 67 133 200 304 40 340 404 276), lower := (rows 35 67 133 200 304 40 64 128 256), losses := [] }

theorem u4252 : Upper (D 9) (R 9) [34,65,129,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4252 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4253 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 67 133 200 304 48 332 396 268), lower := (rows 35 67 133 200 304 48 64 128 256), losses := [] }

theorem u4253 : Upper (D 9) (R 9) [34,65,129,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4253 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4254 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 67 133 200 304 288 92 156 284), lower := (rows 35 67 133 200 304 288 64 128 256), losses := [] }

theorem u4254 : Upper (D 9) (R 9) [34,65,129,192,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4254 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4255 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 199, targets := 256 },{ cop := 2, region := 376, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 67 133 268 304 40 208 208 464), lower := (rows 35 67 133 268 304 40 64 128 256), losses := [] }

theorem u4255 : Upper (D 9) (R 9) [34,65,129,260,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4255 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4256 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 67 133 268 304 48 200 200 456), lower := (rows 35 67 133 268 304 48 64 128 256), losses := [] }

theorem u4256 : Upper (D 9) (R 9) [34,65,129,260,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4256 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4257 : PairBound 9 := { available := 152, camps := [{ cop := 5, region := 3, targets := 384 },{ cop := 0, region := 412, targets := 64 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,6)], upper := (rows 35 67 133 268 304 96 216 152 408), lower := (rows 35 67 133 268 304 96 64 128 256), losses := [] }

theorem u4257 : Upper (D 9) (R 9) [34,65,129,260,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4257 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r4258 : Route 9 := (fun mask => (mask,id))

def c4258 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4258 : Upper (D 9) (R 9) [34,65,129,260,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260,288,128] 13 (by decide) (choices 1) [8,16] r4258 c4258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1188
  · exact u1189

def r4259 : Route 9 := (fun mask => (mask,id))

def c4259 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4259 : Upper (D 9) (R 9) [34,65,129,260,320,8] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260,320,8] 13 (by decide) (choices 1) [16,32,128] r4259 c4259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1190
  · exact u1191
  · exact u1192

#print axioms u4259
end Delivery.IrregularNine14.P09
