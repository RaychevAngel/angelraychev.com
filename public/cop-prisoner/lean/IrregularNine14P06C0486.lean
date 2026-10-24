import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0175
import IrregularNine14P06C0176

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29160 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 42 196 26 84 289 353 417 289), lower := (rows 7 42 196 26 84 32 64 128 256), losses := [] }

theorem u29160 : Upper (D 6) (R 6) [6,40,192,18,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29160
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29161 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 26 112 293 325 389 261), lower := (rows 7 42 196 26 112 32 64 128 256), losses := [] }

theorem u29161 : Upper (D 6) (R 6) [6,40,192,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29161
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29162 : Route 9 := (fun mask => (mask,id))

def c29162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29162 : Upper (D 6) (R 6) [6,40,192,18,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,257] 13 (by decide) (choices 1) [1,4,64] r29162 c29162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10529
  · exact u10530
  · exact u10531

def r29163 : Route 9 := (fun mask => (mask,id))

def c29163 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29163 : Upper (D 6) (R 6) [6,40,192,18,260] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,260] 13 (by decide) (choices 1) [1,64] r29163 c29163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10532
  · exact u10533

def b29164 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 196 26 304 101 69 197 325), lower := (rows 7 42 196 26 304 32 64 128 256), losses := [] }

theorem u29164 : Upper (D 6) (R 6) [6,40,192,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29164
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29165 : Route 9 := (fun mask => (mask,id))

def c29165 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29165 : Upper (D 6) (R 6) [6,40,192,18,320] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,320] 13 (by decide) (choices 1) [1,4] r29165 c29165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10534
  · exact u10535

def b29166 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 42 196 28 19 353 353 481 353), lower := (rows 7 42 196 28 19 32 64 128 256), losses := [] }

theorem u29166 : Upper (D 6) (R 6) [6,40,192,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29166
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29167 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(2,5),(4,2)], upper := (rows 7 42 196 28 49 355 323 451 323), lower := (rows 7 42 196 28 49 32 64 128 256), losses := [] }

theorem u29167 : Upper (D 6) (R 6) [6,40,192,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29167
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29168 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 196 28 50 353 321 449 321), lower := (rows 7 42 196 28 50 32 64 128 256), losses := [] }

theorem u29168 : Upper (D 6) (R 6) [6,40,192,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29168
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29169 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 291, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 196 28 81 291 355 419 291), lower := (rows 7 42 196 28 81 32 64 128 256), losses := [] }

theorem u29169 : Upper (D 6) (R 6) [6,40,192,20,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29169
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29170 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 291, targets := 64 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 7 42 196 28 82 289 353 417 289), lower := (rows 7 42 196 28 82 32 64 128 256), losses := [] }

theorem u29170 : Upper (D 6) (R 6) [6,40,192,20,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29170
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29171 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 3, region := 291, targets := 64 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 42 196 28 112 291 323 387 259), lower := (rows 7 42 196 28 112 32 64 128 256), losses := [] }

theorem u29171 : Upper (D 6) (R 6) [6,40,192,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29171
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29172 : Route 9 := (fun mask => (mask,id))

def c29172 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29172 : Upper (D 6) (R 6) [6,40,192,20,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,20,257] 13 (by decide) (choices 1) [1,2,64] r29172 c29172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10536
  · exact u10537
  · exact u10538

def r29173 : Route 9 := (fun mask => (mask,id))

def c29173 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29173 : Upper (D 6) (R 6) [6,40,192,20,258] 13 := by
  apply FastRouting.sound _ _ [6,40,192,20,258] 13 (by decide) (choices 1) [1,64] r29173 c29173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10539
  · exact u10540

def b29174 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(2,5),(4,2)], upper := (rows 7 42 196 28 304 99 67 195 323), lower := (rows 7 42 196 28 304 32 64 128 256), losses := [] }

theorem u29174 : Upper (D 6) (R 6) [6,40,192,20,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29174
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29175 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 196 28 336 35 99 163 291), lower := (rows 7 42 196 28 336 32 64 128 256), losses := [] }

theorem u29175 : Upper (D 6) (R 6) [6,40,192,20,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29175
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29176 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 7 42 196 73 19 308 372 436 308), lower := (rows 7 42 196 73 19 32 64 128 256), losses := [] }

theorem u29176 : Upper (D 6) (R 6) [6,40,192,65,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29176
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29177 : PairBound 9 := { available := 306, camps := [{ cop := 0, region := 16, targets := 34 },{ cop := 4, region := 362, targets := 4 }], pairs := [(1,2),(4,1),(4,5)], upper := (rows 7 42 196 73 21 306 370 434 306), lower := (rows 7 42 196 73 21 32 64 128 256), losses := [] }

theorem u29177 : Upper (D 6) (R 6) [6,40,192,65,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29177
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29178 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 7 42 196 73 22 305 369 433 305), lower := (rows 7 42 196 73 22 32 64 128 256), losses := [] }

theorem u29178 : Upper (D 6) (R 6) [6,40,192,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29178
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29179 : Route 9 := (fun mask => (mask,id))

def c29179 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29179 : Upper (D 6) (R 6) [6,40,192,65,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,33] 13 (by decide) (choices 1) [2,4,16,256] r29179 c29179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10541
  · exact u10542
  · exact u10543
  · exact u10544

def b29180 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 196 73 50 309 341 405 277), lower := (rows 7 42 196 73 50 32 64 128 256), losses := [] }

theorem u29180 : Upper (D 6) (R 6) [6,40,192,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29180
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29181 : Route 9 := (fun mask => (mask,id))

def c29181 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29181 : Upper (D 6) (R 6) [6,40,192,65,36] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,36] 13 (by decide) (choices 1) [1,2,16,256] r29181 c29181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10545
  · exact u10546
  · exact u10547
  · exact u10548

def r29182 : Route 9 := (fun mask => (mask,id))

def c29182 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29182 : Upper (D 6) (R 6) [6,40,192,65,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,257] 13 (by decide) (choices 1) [2,4,16] r29182 c29182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10549
  · exact u10550
  · exact u10551

def r29183 : Route 9 := (fun mask => (mask,id))

def c29183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29183 : Upper (D 6) (R 6) [6,40,192,65,258] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,258] 13 (by decide) (choices 1) [1,4,16] r29183 c29183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10552
  · exact u10553
  · exact u10554

def r29184 : Route 9 := (fun mask => (mask,id))

def c29184 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29184 : Upper (D 6) (R 6) [6,40,192,65,260] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,260] 13 (by decide) (choices 1) [1,2,16] r29184 c29184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10555
  · exact u10556
  · exact u10557

def r29185 : Route 9 := (fun mask => (mask,id))

def c29185 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29185 : Upper (D 6) (R 6) [6,40,192,65,288] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,288] 13 (by decide) (choices 1) [1,2,4,16] r29185 c29185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10558
  · exact u10559
  · exact u10560
  · exact u10561

def b29186 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 7 42 196 88 19 293 357 421 293), lower := (rows 7 42 196 88 19 32 64 128 256), losses := [] }

theorem u29186 : Upper (D 6) (R 6) [6,40,192,80,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29186
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29187 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 16, targets := 34 },{ cop := 4, region := 362, targets := 4 }], pairs := [(1,2),(4,1),(4,5)], upper := (rows 7 42 196 88 21 291 355 419 291), lower := (rows 7 42 196 88 21 32 64 128 256), losses := [] }

theorem u29187 : Upper (D 6) (R 6) [6,40,192,80,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29187
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29188 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 484, targets := 2 },{ cop := 0, region := 16, targets := 32 }], pairs := [(2,1),(4,0),(4,5)], upper := (rows 7 42 196 88 22 289 353 417 289), lower := (rows 7 42 196 88 22 32 64 128 256), losses := [] }

theorem u29188 : Upper (D 6) (R 6) [6,40,192,80,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29188
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29189 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 304, targets := 64 }], pairs := [(0,5),(2,5),(4,6)], upper := (rows 7 42 196 88 49 295 327 391 263), lower := (rows 7 42 196 88 49 32 64 128 256), losses := [] }

theorem u29189 : Upper (D 6) (R 6) [6,40,192,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29189
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29190 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 196 88 50 293 325 389 261), lower := (rows 7 42 196 88 50 32 64 128 256), losses := [] }

theorem u29190 : Upper (D 6) (R 6) [6,40,192,80,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29190
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29191 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 304, targets := 64 }], pairs := [(0,5),(2,5),(4,6)], upper := (rows 7 42 196 88 52 291 323 387 259), lower := (rows 7 42 196 88 52 32 64 128 256), losses := [] }

theorem u29191 : Upper (D 6) (R 6) [6,40,192,80,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29191
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29192 : Route 9 := (fun mask => (mask,id))

def c29192 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29192 : Upper (D 6) (R 6) [6,40,192,80,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,257] 13 (by decide) (choices 1) [1,2,4] r29192 c29192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10562
  · exact u10563
  · exact u10564

def r29193 : Route 9 := (fun mask => (mask,id))

def c29193 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29193 : Upper (D 6) (R 6) [6,40,192,80,258] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,258] 13 (by decide) (choices 1) [1,4] r29193 c29193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10565
  · exact u10566

def r29194 : Route 9 := (fun mask => (mask,id))

def c29194 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29194 : Upper (D 6) (R 6) [6,40,192,80,260] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,260] 13 (by decide) (choices 1) [1,2] r29194 c29194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10567
  · exact u10568

def b29195 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 0, region := 304, targets := 64 }], pairs := [(0,5),(2,5),(4,6)], upper := (rows 7 42 196 88 304 39 71 135 263), lower := (rows 7 42 196 88 304 32 64 128 256), losses := [] }

theorem u29195 : Upper (D 6) (R 6) [6,40,192,80,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29195
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29196 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 7 42 196 265 19 116 116 244 372), lower := (rows 7 42 196 265 19 32 64 128 256), losses := [] }

theorem u29196 : Upper (D 6) (R 6) [6,40,192,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29196
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29197 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 42 196 265 21 114 114 242 370), lower := (rows 7 42 196 265 21 32 64 128 256), losses := [] }

theorem u29197 : Upper (D 6) (R 6) [6,40,192,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29197
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29198 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 42 196 265 22 113 113 241 369), lower := (rows 7 42 196 265 22 32 64 128 256), losses := [] }

theorem u29198 : Upper (D 6) (R 6) [6,40,192,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29198
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29199 : Route 9 := (fun mask => (mask,id))

def c29199 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29199 : Upper (D 6) (R 6) [6,40,192,257,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,33] 13 (by decide) (choices 1) [2,4,16,64] r29199 c29199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10569
  · exact u10570
  · exact u10571
  · exact u10572

def b29200 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 196 265 50 117 85 213 341), lower := (rows 7 42 196 265 50 32 64 128 256), losses := [] }

theorem u29200 : Upper (D 6) (R 6) [6,40,192,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29200
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29201 : Route 9 := (fun mask => (mask,id))

def c29201 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29201 : Upper (D 6) (R 6) [6,40,192,257,36] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,36] 13 (by decide) (choices 1) [1,2,16,64] r29201 c29201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10573
  · exact u10574
  · exact u10575
  · exact u10576

def r29202 : Route 9 := (fun mask => (mask,id))

def c29202 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29202 : Upper (D 6) (R 6) [6,40,192,257,65] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,65] 13 (by decide) (choices 1) [2,4,16] r29202 c29202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10577
  · exact u10578
  · exact u10579

def r29203 : Route 9 := (fun mask => (mask,id))

def c29203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29203 : Upper (D 6) (R 6) [6,40,192,257,66] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,66] 13 (by decide) (choices 1) [1,4,16] r29203 c29203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10580
  · exact u10581
  · exact u10582

def b29204 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 42 196 265 84 51 115 179 307), lower := (rows 7 42 196 265 84 32 64 128 256), losses := [] }

theorem u29204 : Upper (D 6) (R 6) [6,40,192,257,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29204
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29205 : Route 9 := (fun mask => (mask,id))

def c29205 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29205 : Upper (D 6) (R 6) [6,40,192,257,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,96] 13 (by decide) (choices 1) [1,2,4,16] r29205 c29205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10583
  · exact u10584
  · exact u10585
  · exact u10586

def b29206 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 16, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 42 196 266 21 113 113 241 369), lower := (rows 7 42 196 266 21 32 64 128 256), losses := [] }

theorem u29206 : Upper (D 6) (R 6) [6,40,192,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29206
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29207 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 196, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 7 42 196 266 49 117 85 213 341), lower := (rows 7 42 196 266 49 32 64 128 256), losses := [] }

theorem u29207 : Upper (D 6) (R 6) [6,40,192,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29207
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29208 : Route 9 := (fun mask => (mask,id))

def c29208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29208 : Upper (D 6) (R 6) [6,40,192,258,36] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258,36] 13 (by decide) (choices 1) [1,16,64] r29208 c29208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10587
  · exact u10588
  · exact u10589

def r29209 : Route 9 := (fun mask => (mask,id))

def c29209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29209 : Upper (D 6) (R 6) [6,40,192,258,65] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258,65] 13 (by decide) (choices 1) [1,4,16] r29209 c29209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10590
  · exact u10591
  · exact u10592

def b29210 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 42 196 266 84 49 113 177 305), lower := (rows 7 42 196 266 84 32 64 128 256), losses := [] }

theorem u29210 : Upper (D 6) (R 6) [6,40,192,258,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29210
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29211 : Route 9 := (fun mask => (mask,id))

def c29211 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29211 : Upper (D 6) (R 6) [6,40,192,258,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258,96] 13 (by decide) (choices 1) [1,4,16] r29211 c29211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10593
  · exact u10594
  · exact u10595

def b29212 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 7 42 196 268 19 113 113 241 369), lower := (rows 7 42 196 268 19 32 64 128 256), losses := [] }

theorem u29212 : Upper (D 6) (R 6) [6,40,192,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29212
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29213 : Route 9 := (fun mask => (mask,id))

def c29213 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29213 : Upper (D 6) (R 6) [6,40,192,260,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,260,33] 13 (by decide) (choices 1) [1,2,16,64] r29213 c29213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10596
  · exact u10597
  · exact u10598
  · exact u10599

def b29214 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 196 268 50 113 81 209 337), lower := (rows 7 42 196 268 50 32 64 128 256), losses := [] }

theorem u29214 : Upper (D 6) (R 6) [6,40,192,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29214
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29215 : Route 9 := (fun mask => (mask,id))

def c29215 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29215 : Upper (D 6) (R 6) [6,40,192,260,65] 13 := by
  apply FastRouting.sound _ _ [6,40,192,260,65] 13 (by decide) (choices 1) [1,2,16] r29215 c29215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10600
  · exact u10601
  · exact u10602

def r29216 : Route 9 := (fun mask => (mask,id))

def c29216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29216 : Upper (D 6) (R 6) [6,40,192,260,66] 13 := by
  apply FastRouting.sound _ _ [6,40,192,260,66] 13 (by decide) (choices 1) [1,16] r29216 c29216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10603
  · exact u10604

def r29217 : Route 9 := (fun mask => (mask,id))

def c29217 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29217 : Upper (D 6) (R 6) [6,40,192,260,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,260,96] 13 (by decide) (choices 1) [1,2,16] r29217 c29217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10605
  · exact u10606
  · exact u10607

def b29218 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 7 42 196 280 19 101 101 229 357), lower := (rows 7 42 196 280 19 32 64 128 256), losses := [] }

theorem u29218 : Upper (D 6) (R 6) [6,40,192,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29218
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29219 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 42 196 280 21 99 99 227 355), lower := (rows 7 42 196 280 21 32 64 128 256), losses := [] }

theorem u29219 : Upper (D 6) (R 6) [6,40,192,272,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29219
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u29219
end Delivery.IrregularNine14.P06
