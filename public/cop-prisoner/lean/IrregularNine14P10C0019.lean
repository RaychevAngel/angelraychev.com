import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0005

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m1140_128 : Upper (D 10) (R 10) [6,9,96,160,288,128] 13 :=
  permutation_upper _ _ _ [6,9,96,160,288,64] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u308

def r1140 : Route 9 := (fun mask => (mask,id))

def c1140 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1140 : Upper (D 10) (R 10) [6,9,96,160,288] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,288] 13 (by decide) (choices 1) [16,64,128,256] r1140 c1140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u307
  · exact u308
  · exact m1140_128
  · exact u309

def r1141 : Route 9 := (fun mask => (mask,id))

def c1141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1141 : Upper (D 10) (R 10) [6,9,96,160,320] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,320] 13 (by decide) (choices 1) [16,128,256] r1141 c1141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u310
  · exact u311
  · exact u312

def b1142 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 4, region := 324, targets := 128 }], pairs := [(2,7),(4,6)], upper := (rows 7 11 100 200 176 304 368 432 304), lower := (rows 7 11 100 200 176 32 64 128 256), losses := [] }

theorem u1142 : Upper (D 10) (R 10) [6,9,96,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1142 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1143 : Route 9 := (fun mask => (mask,id))

def c1143 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1143 : Upper (D 10) (R 10) [6,9,96,192,288] 13 := by
  apply FastRouting.sound _ _ [6,9,96,192,288] 13 (by decide) (choices 1) [16,128,256] r1143 c1143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u313
  · exact u314
  · exact u315

def b1144 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 4, region := 100, targets := 128 }], pairs := [(2,7),(4,6)], upper := (rows 7 11 100 200 400 304 368 432 304), lower := (rows 7 11 100 200 400 32 64 128 256), losses := [] }

theorem u1144 : Upper (D 10) (R 10) [6,9,96,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1144 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1145 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 16, targets := 384 }], pairs := [(4,7),(4,8)], upper := (rows 7 11 100 392 112 432 496 432 432), lower := (rows 7 11 100 392 112 32 64 128 256), losses := [] }

theorem u1145 : Upper (D 10) (R 10) [6,9,96,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1145 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1146 : Route 9 := (fun mask => (mask,id))

def c1146 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1146 : Upper (D 10) (R 10) [6,9,96,384,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,160] 13 (by decide) (choices 1) [16,64,256] r1146 c1146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u316
  · exact u317
  · exact u318

def b1147 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 296, targets := 64 },{ cop := 4, region := 292, targets := 128 }], pairs := [(2,7),(3,6)], upper := (rows 7 11 100 392 208 304 368 432 304), lower := (rows 7 11 100 392 208 32 64 128 256), losses := [] }

theorem u1147 : Upper (D 10) (R 10) [6,9,96,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1147 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1148 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 11 100 392 400 112 112 240 368), lower := (rows 7 11 100 392 400 32 64 128 256), losses := [] }

theorem u1148 : Upper (D 10) (R 10) [6,9,96,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1148 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1149 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 11, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 11 196 200 304 304 368 432 304), lower := (rows 7 11 196 200 304 32 64 128 256), losses := [] }

theorem u1149 : Upper (D 10) (R 10) [6,9,192,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1149 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1150 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 4, region := 328, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 7 11 196 328 176 304 368 432 304), lower := (rows 7 11 196 328 176 32 64 128 256), losses := [] }

theorem u1150 : Upper (D 10) (R 10) [6,9,192,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1150 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1151 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 7 11 196 328 400 48 112 176 304), lower := (rows 7 11 196 328 400 32 64 128 256), losses := [] }

theorem u1151 : Upper (D 10) (R 10) [6,9,192,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1151 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1152 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 23, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 26 37 104 112 416 448 384 384), lower := (rows 7 26 37 104 112 32 64 128 256), losses := [] }

theorem u1152 : Upper (D 10) (R 10) [6,24,33,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1152 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m1153_128 : Upper (D 10) (R 10) [6,24,33,96,160,128] 13 :=
  permutation_upper _ _ _ [6,24,33,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u319

def r1153 : Route 9 := (fun mask => (mask,id))

def c1153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1153 : Upper (D 10) (R 10) [6,24,33,96,160] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,160] 13 (by decide) (choices 1) [64,128,256] r1153 c1153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u319
  · exact m1153_128
  · exact u320

def b1154 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 26 37 104 208 416 480 416 416), lower := (rows 7 26 37 104 208 32 64 128 256), losses := [] }

theorem u1154 : Upper (D 10) (R 10) [6,24,33,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1154 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1155 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1155 : Upper (D 10) (R 10) [6,24,33,96,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,384] 13 (by decide) (choices 1) [64,128] r1155 c1155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u321
  · exact u322

def b1156 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 18, targets := 288 }], pairs := [(1,5),(1,8)], upper := (rows 7 26 37 200 208 288 352 416 288), lower := (rows 7 26 37 200 208 32 64 128 256), losses := [] }

theorem u1156 : Upper (D 10) (R 10) [6,24,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1156 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1157 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 26 37 200 336 416 480 416 416), lower := (rows 7 26 37 200 336 32 64 128 256), losses := [] }

theorem u1157 : Upper (D 10) (R 10) [6,24,33,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1157 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1158 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 402, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 26 69 104 176 416 480 416 416), lower := (rows 7 26 69 104 176 32 64 128 256), losses := [] }

theorem u1158 : Upper (D 10) (R 10) [6,24,65,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1158 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1159 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 402, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 26 69 104 400 416 480 416 416), lower := (rows 7 26 69 104 400 32 64 128 256), losses := [] }

theorem u1159 : Upper (D 10) (R 10) [6,24,65,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1159 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1160 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 18, targets := 320 }], pairs := [(1,6),(1,8)], upper := (rows 7 26 69 168 176 352 352 480 352), lower := (rows 7 26 69 168 176 32 64 128 256), losses := [] }

theorem u1160 : Upper (D 10) (R 10) [6,24,65,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1160 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1161 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 26 69 168 208 288 352 416 288), lower := (rows 7 26 69 168 208 32 64 128 256), losses := [] }

theorem u1161 : Upper (D 10) (R 10) [6,24,65,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1161 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m1162_256 : Upper (D 10) (R 10) [6,24,65,160,288,256] 13 :=
  permutation_upper _ _ _ [6,24,65,160,288,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u324

def r1162 : Route 9 := (fun mask => (mask,id))

def c1162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1162 : Upper (D 10) (R 10) [6,24,65,160,288] 13 := by
  apply FastRouting.sound _ _ [6,24,65,160,288] 13 (by decide) (choices 1) [64,128,256] r1162 c1162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u323
  · exact u324
  · exact m1162_256

def b1163 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 7 26 69 168 336 416 480 416 416), lower := (rows 7 26 69 168 336 32 64 128 256), losses := [] }

theorem u1163 : Upper (D 10) (R 10) [6,24,65,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1163 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1164 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 26 69 168 400 352 352 480 352), lower := (rows 7 26 69 168 400 32 64 128 256), losses := [] }

theorem u1164 : Upper (D 10) (R 10) [6,24,65,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1164 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1165 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 26 69 200 400 288 352 416 288), lower := (rows 7 26 69 200 400 32 64 128 256), losses := [] }

theorem u1165 : Upper (D 10) (R 10) [6,24,65,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1165 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1166 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 18, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 7 26 69 392 400 96 96 224 352), lower := (rows 7 26 69 392 400 32 64 128 256), losses := [] }

theorem u1166 : Upper (D 10) (R 10) [6,24,65,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1166 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1167 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 27, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 26 100 41 112 416 448 384 384), lower := (rows 7 26 100 41 112 32 64 128 256), losses := [] }

theorem u1167 : Upper (D 10) (R 10) [6,24,96,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1167 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1168 : Route 9 := (fun mask => (mask,id))

def c1168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1168 : Upper (D 10) (R 10) [6,24,96,33,160] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,160] 13 (by decide) (choices 1) [64,128,256] r1168 c1168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u325
  · exact u326
  · exact u327

def r1169 : Route 9 := (fun mask => (mask,id))

def c1169 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1169 : Upper (D 10) (R 10) [6,24,96,33,192] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,192] 13 (by decide) (choices 1) [128,256] r1169 c1169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u328
  · exact u329

def r1170 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1170 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1170 : Upper (D 10) (R 10) [6,24,96,33,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,384] 13 (by decide) (choices 1) [64,128] r1170 c1170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u330
  · exact u331

def b1171 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 26 100 73 176 416 480 416 416), lower := (rows 7 26 100 73 176 32 64 128 256), losses := [] }

theorem u1171 : Upper (D 10) (R 10) [6,24,96,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1171 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1172 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 26 100 73 400 416 480 416 416), lower := (rows 7 26 100 73 400 32 64 128 256), losses := [] }

theorem u1172 : Upper (D 10) (R 10) [6,24,96,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1172 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1173 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 26 100 104 145 416 480 416 416), lower := (rows 7 26 100 104 145 32 64 128 256), losses := [] }

theorem u1173 : Upper (D 10) (R 10) [6,24,96,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1173 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1174 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 26 100 104 176 417 449 385 385), lower := (rows 7 26 100 104 176 32 64 128 256), losses := [] }

theorem u1174 : Upper (D 10) (R 10) [6,24,96,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1174 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1175 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 26 100 104 400 417 481 417 417), lower := (rows 7 26 100 104 400 32 64 128 256), losses := [] }

theorem u1175 : Upper (D 10) (R 10) [6,24,96,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1175 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1176 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 26 100 137 176 352 352 480 352), lower := (rows 7 26 100 137 176 32 64 128 256), losses := [] }

theorem u1176 : Upper (D 10) (R 10) [6,24,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1176 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1177 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 26 100 137 208 288 352 416 288), lower := (rows 7 26 100 137 208 32 64 128 256), losses := [] }

theorem u1177 : Upper (D 10) (R 10) [6,24,96,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1177 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1178 : Route 9 := (fun mask => (mask,id))

def c1178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1178 : Upper (D 10) (R 10) [6,24,96,129,288] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288] 13 (by decide) (choices 1) [64,128,256] r1178 c1178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u332
  · exact u333
  · exact u334

def r1179 : Route 9 := (fun mask => (mask,id))

def c1179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1179 : Upper (D 10) (R 10) [6,24,96,129,320] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,320] 13 (by decide) (choices 1) [128,256] r1179 c1179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u335
  · exact u336

def b1180 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 26 100 137 400 352 352 480 352), lower := (rows 7 26 100 137 400 32 64 128 256), losses := [] }

theorem u1180 : Upper (D 10) (R 10) [6,24,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1180 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1181 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 18, targets := 320 }], pairs := [(1,6),(1,8)], upper := (rows 7 26 100 168 176 353 321 449 321), lower := (rows 7 26 100 168 176 32 64 128 256), losses := [] }

theorem u1181 : Upper (D 10) (R 10) [6,24,96,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1181 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1182 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 26 100 168 208 289 353 417 289), lower := (rows 7 26 100 168 208 32 64 128 256), losses := [] }

theorem u1182 : Upper (D 10) (R 10) [6,24,96,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1182 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m1183_256 : Upper (D 10) (R 10) [6,24,96,160,288,256] 13 :=
  permutation_upper _ _ _ [6,24,96,160,288,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u339

def r1183 : Route 9 := (fun mask => (mask,id))

def c1183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1183 : Upper (D 10) (R 10) [6,24,96,160,288] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,288] 13 (by decide) (choices 1) [1,64,128,256] r1183 c1183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u337
  · exact u338
  · exact u339
  · exact m1183_256

def r1184 : Route 9 := (fun mask => (mask,id))

def c1184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1184 : Upper (D 10) (R 10) [6,24,96,160,320] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,320] 13 (by decide) (choices 1) [1,128,256] r1184 c1184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u340
  · exact u341
  · exact u342

def b1185 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 26 100 168 400 353 353 481 353), lower := (rows 7 26 100 168 400 32 64 128 256), losses := [] }

theorem u1185 : Upper (D 10) (R 10) [6,24,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1185 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1186 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 26 100 200 400 289 353 417 289), lower := (rows 7 26 100 200 400 32 64 128 256), losses := [] }

theorem u1186 : Upper (D 10) (R 10) [6,24,96,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1186 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1187 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 18, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 7 26 100 392 400 97 97 225 353), lower := (rows 7 26 100 392 400 32 64 128 256), losses := [] }

theorem u1187 : Upper (D 10) (R 10) [6,24,96,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1187 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1188 : Route 9 := (fun mask => (mask,id))

def c1188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1188 : Upper (D 10) (R 10) [6,24,192,33,96] 13 := by
  apply FastRouting.sound _ _ [6,24,192,33,96] 13 (by decide) (choices 1) [128,256] r1188 c1188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u343
  · exact u344

def b1189 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 16, targets := 288 }], pairs := [(4,5),(4,8)], upper := (rows 7 26 196 41 208 288 352 416 288), lower := (rows 7 26 196 41 208 32 64 128 256), losses := [] }

theorem u1189 : Upper (D 10) (R 10) [6,24,192,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1189 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1190 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1190 : Upper (D 10) (R 10) [6,24,192,33,288] 13 := by
  apply FastRouting.sound _ _ [6,24,192,33,288] 13 (by decide) (choices 1) [64,256] r1190 c1190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u345
  · exact u346

def r1191 : Route 9 := (fun mask => (mask,id))

def c1191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1191 : Upper (D 10) (R 10) [6,24,192,33,320] 13 := by
  apply FastRouting.sound _ _ [6,24,192,33,320] 13 (by decide) (choices 1) [128,256] r1191 c1191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u347
  · exact u348

def b1192 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 26 196 73 176 288 352 416 288), lower := (rows 7 26 196 73 176 32 64 128 256), losses := [] }

theorem u1192 : Upper (D 10) (R 10) [6,24,192,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1192 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1193 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 26 196 73 304 416 480 416 416), lower := (rows 7 26 196 73 304 32 64 128 256), losses := [] }

theorem u1193 : Upper (D 10) (R 10) [6,24,192,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1193 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1194 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 26 196 73 400 288 352 416 288), lower := (rows 7 26 196 73 400 32 64 128 256), losses := [] }

theorem u1194 : Upper (D 10) (R 10) [6,24,192,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1194 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1195 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 0, region := 360, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 7 26 196 104 176 289 353 417 289), lower := (rows 7 26 196 104 176 32 64 128 256), losses := [] }

theorem u1195 : Upper (D 10) (R 10) [6,24,192,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1195 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1196 : Route 9 := (fun mask => (mask,id))

def c1196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1196 : Upper (D 10) (R 10) [6,24,192,96,257] 13 := by
  apply FastRouting.sound _ _ [6,24,192,96,257] 13 (by decide) (choices 1) [128,256] r1196 c1196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u349
  · exact u350

def r1197 : Route 9 := (fun mask => (mask,id))

def c1197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1197 : Upper (D 10) (R 10) [6,24,192,96,288] 13 := by
  apply FastRouting.sound _ _ [6,24,192,96,288] 13 (by decide) (choices 1) [1,128,256] r1197 c1197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u351
  · exact u352
  · exact u353

def b1198 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 0, region := 360, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 7 26 196 104 400 289 353 417 289), lower := (rows 7 26 196 104 400 32 64 128 256), losses := [] }

theorem u1198 : Upper (D 10) (R 10) [6,24,192,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1198 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1199 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 8, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 7 26 196 200 273 288 352 416 288), lower := (rows 7 26 196 200 273 32 64 128 256), losses := [] }

theorem u1199 : Upper (D 10) (R 10) [6,24,192,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1199 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u1199
end Delivery.IrregularNine14.P10
