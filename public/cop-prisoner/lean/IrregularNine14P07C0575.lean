import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0319
import IrregularNine14P07C0320
import IrregularNine14P07C0321
import IrregularNine14P07C0322

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34500 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 133 42 280 241 209 209 465), lower := (rows 35 70 133 42 280 32 64 128 256), losses := [] }

theorem u34500 : Upper (D 7) (R 7) [34,68,129,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34501 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 133 42 336 185 217 153 409), lower := (rows 35 70 133 42 336 32 64 128 256), losses := [] }

theorem u34501 : Upper (D 7) (R 7) [34,68,129,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34502 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 133 42 400 121 89 217 345), lower := (rows 35 70 133 42 400 32 64 128 256), losses := [] }

theorem u34502 : Upper (D 7) (R 7) [34,68,129,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34503 : Route 9 := (fun mask => (mask,id))

def c34503 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34503 : Upper (D 7) (R 7) [34,68,129,48,65] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,65] 13 (by decide) (choices 1) [2,8,128,256] r34503 c34503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19198
  · exact u19199
  · exact u19200
  · exact u19201

def b34504 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 425, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 133 56 82 425 457 393 393), lower := (rows 35 70 133 56 82 32 64 128 256), losses := [] }

theorem u34504 : Upper (D 7) (R 7) [34,68,129,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34505 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(2,6)], upper := (rows 35 70 133 56 88 419 451 387 387), lower := (rows 35 70 133 56 88 32 64 128 256), losses := [] }

theorem u34505 : Upper (D 7) (R 7) [34,68,129,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34506 : PairBound 9 := { available := 330, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 35 70 133 56 145 362 330 458 330), lower := (rows 35 70 133 56 145 32 64 128 256), losses := [] }

theorem u34506 : Upper (D 7) (R 7) [34,68,129,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34507 : Route 9 := (fun mask => (mask,id))

def c34507 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34507 : Upper (D 7) (R 7) [34,68,129,48,130] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,130] 13 (by decide) (choices 1) [1,8,64,256] r34507 c34507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19202
  · exact u19203
  · exact u19204
  · exact u19205

def b34508 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,5)], upper := (rows 35 70 133 56 152 355 323 451 323), lower := (rows 35 70 133 56 152 32 64 128 256), losses := [] }

theorem u34508 : Upper (D 7) (R 7) [34,68,129,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34509 : Route 9 := (fun mask => (mask,id))

def c34509 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34509 : Upper (D 7) (R 7) [34,68,129,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,192] 13 (by decide) (choices 1) [1,2,8,256] r34509 c34509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19206
  · exact u19207
  · exact u19208
  · exact u19209

def r34510 : Route 9 := (fun mask => (mask,id))

def c34510 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34510 : Upper (D 7) (R 7) [34,68,129,48,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,257] 13 (by decide) (choices 1) [2,8,64,128] r34510 c34510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19210
  · exact u19211
  · exact u19212
  · exact u19213

def r34511 : Route 9 := (fun mask => (mask,id))

def c34511 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34511 : Upper (D 7) (R 7) [34,68,129,48,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,258] 13 (by decide) (choices 1) [1,8,64,128] r34511 c34511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19214
  · exact u19215
  · exact u19216
  · exact u19217

def r34512 : Route 9 := (fun mask => (mask,id))

def c34512 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34512 : Upper (D 7) (R 7) [34,68,129,48,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,264] 13 (by decide) (choices 1) [1,2,64,128] r34512 c34512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19218
  · exact u19219
  · exact u19220
  · exact u19221

def r34513 : Route 9 := (fun mask => (mask,id))

def c34513 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34513 : Upper (D 7) (R 7) [34,68,129,48,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,320] 13 (by decide) (choices 1) [1,2,8,128] r34513 c34513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19222
  · exact u19223
  · exact u19224
  · exact u19225

def r34514 : Route 9 := (fun mask => (mask,id))

def c34514 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34514 : Upper (D 7) (R 7) [34,68,129,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,384] 13 (by decide) (choices 1) [1,2,8,64] r34514 c34514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19226
  · exact u19227
  · exact u19228
  · exact u19229

def r34515 : Route 9 := (fun mask => (mask,id))

def c34515 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34515 : Upper (D 7) (R 7) [34,68,129,65,130] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,130] 13 (by decide) (choices 1) [8,16,256] r34515 c34515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19230
  · exact u19231
  · exact u19232

def r34516 : Route 9 := (fun mask => (mask,id))

def c34516 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34516 : Upper (D 7) (R 7) [34,68,129,65,136] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,136] 13 (by decide) (choices 1) [2,16,256] r34516 c34516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19233
  · exact u19234
  · exact u19235

def r34517 : Route 9 := (fun mask => (mask,id))

def c34517 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34517 : Upper (D 7) (R 7) [34,68,129,65,160] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,160] 13 (by decide) (choices 1) [2,8,16,256] r34517 c34517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19236
  · exact u19237
  · exact u19238
  · exact u19239

def r34518 : Route 9 := (fun mask => (mask,id))

def c34518 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34518 : Upper (D 7) (R 7) [34,68,129,65,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,258] 13 (by decide) (choices 1) [8,16,128] r34518 c34518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19240
  · exact u19241
  · exact u19242

def r34519 : Route 9 := (fun mask => (mask,id))

def c34519 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34519 : Upper (D 7) (R 7) [34,68,129,65,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,264] 13 (by decide) (choices 1) [2,16,128] r34519 c34519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19243
  · exact u19244
  · exact u19245

def r34520 : Route 9 := (fun mask => (mask,id))

def c34520 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34520 : Upper (D 7) (R 7) [34,68,129,65,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,288] 13 (by decide) (choices 1) [2,8,16,128] r34520 c34520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19246
  · exact u19247
  · exact u19248
  · exact u19249

def r34521 : Route 9 := (fun mask => (mask,id))

def c34521 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34521 : Upper (D 7) (R 7) [34,68,129,65,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65,384] 13 (by decide) (choices 1) [2,8,16] r34521 c34521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19250
  · exact u19251
  · exact u19252

def b34522 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 133 74 152 305 369 433 305), lower := (rows 35 70 133 74 152 32 64 128 256), losses := [] }

theorem u34522 : Upper (D 7) (R 7) [34,68,129,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34523 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 133 74 176 313 345 409 281), lower := (rows 35 70 133 74 176 32 64 128 256), losses := [] }

theorem u34523 : Upper (D 7) (R 7) [34,68,129,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34524 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 133 74 273 184 248 184 440), lower := (rows 35 70 133 74 273 32 64 128 256), losses := [] }

theorem u34524 : Upper (D 7) (R 7) [34,68,129,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34525 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 133 74 280 177 241 177 433), lower := (rows 35 70 133 74 280 32 64 128 256), losses := [] }

theorem u34525 : Upper (D 7) (R 7) [34,68,129,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34526 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 133 74 304 185 217 153 409), lower := (rows 35 70 133 74 304 32 64 128 256), losses := [] }

theorem u34526 : Upper (D 7) (R 7) [34,68,129,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34527 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 133 74 400 57 121 185 313), lower := (rows 35 70 133 74 400 32 64 128 256), losses := [] }

theorem u34527 : Upper (D 7) (R 7) [34,68,129,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34528 : PairBound 9 := { available := 298, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 35 70 133 88 145 298 362 426 298), lower := (rows 35 70 133 88 145 32 64 128 256), losses := [] }

theorem u34528 : Upper (D 7) (R 7) [34,68,129,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34529 : Route 9 := (fun mask => (mask,id))

def c34529 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34529 : Upper (D 7) (R 7) [34,68,129,80,130] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,130] 13 (by decide) (choices 1) [1,8,256] r34529 c34529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19253
  · exact u19254
  · exact u19255

def b34530 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(2,6)], upper := (rows 35 70 133 88 152 291 355 419 291), lower := (rows 35 70 133 88 152 32 64 128 256), losses := [] }

theorem u34530 : Upper (D 7) (R 7) [34,68,129,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34531 : Route 9 := (fun mask => (mask,id))

def c34531 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34531 : Upper (D 7) (R 7) [34,68,129,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,160] 13 (by decide) (choices 1) [1,2,8,256] r34531 c34531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19256
  · exact u19257
  · exact u19258
  · exact u19259

def r34532 : Route 9 := (fun mask => (mask,id))

def c34532 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34532 : Upper (D 7) (R 7) [34,68,129,80,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,257] 13 (by decide) (choices 1) [2,8,128] r34532 c34532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19260
  · exact u19261
  · exact u19262

def r34533 : Route 9 := (fun mask => (mask,id))

def c34533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34533 : Upper (D 7) (R 7) [34,68,129,80,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,258] 13 (by decide) (choices 1) [1,8,128] r34533 c34533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19263
  · exact u19264
  · exact u19265

def r34534 : Route 9 := (fun mask => (mask,id))

def c34534 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34534 : Upper (D 7) (R 7) [34,68,129,80,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,264] 13 (by decide) (choices 1) [1,2,128] r34534 c34534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19266
  · exact u19267
  · exact u19268

def r34535 : Route 9 := (fun mask => (mask,id))

def c34535 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34535 : Upper (D 7) (R 7) [34,68,129,80,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,288] 13 (by decide) (choices 1) [1,2,8,128] r34535 c34535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19269
  · exact u19270
  · exact u19271
  · exact u19272

def r34536 : Route 9 := (fun mask => (mask,id))

def c34536 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34536 : Upper (D 7) (R 7) [34,68,129,80,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,384] 13 (by decide) (choices 1) [1,2,8] r34536 c34536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19273
  · exact u19274
  · exact u19275

def b34537 : PairBound 9 := { available := 282, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 35 70 133 104 145 314 346 410 282), lower := (rows 35 70 133 104 145 32 64 128 256), losses := [] }

theorem u34537 : Upper (D 7) (R 7) [34,68,129,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34538 : Route 9 := (fun mask => (mask,id))

def c34538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34538 : Upper (D 7) (R 7) [34,68,129,96,130] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,130] 13 (by decide) (choices 1) [1,8,16,256] r34538 c34538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19276
  · exact u19277
  · exact u19278
  · exact u19279

def r34539 : Route 9 := (fun mask => (mask,id))

def c34539 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34539 : Upper (D 7) (R 7) [34,68,129,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,136] 13 (by decide) (choices 1) [1,2,16,256] r34539 c34539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19280
  · exact u19281
  · exact u19282
  · exact u19283

def r34540 : Route 9 := (fun mask => (mask,id))

def c34540 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34540 : Upper (D 7) (R 7) [34,68,129,96,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,257] 13 (by decide) (choices 1) [2,8,16,128] r34540 c34540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19284
  · exact u19285
  · exact u19286
  · exact u19287

def r34541 : Route 9 := (fun mask => (mask,id))

def c34541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34541 : Upper (D 7) (R 7) [34,68,129,96,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,258] 13 (by decide) (choices 1) [1,8,16,128] r34541 c34541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19288
  · exact u19289
  · exact u19290
  · exact u19291

def r34542 : Route 9 := (fun mask => (mask,id))

def c34542 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34542 : Upper (D 7) (R 7) [34,68,129,96,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,264] 13 (by decide) (choices 1) [1,2,16,128] r34542 c34542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19292
  · exact u19293
  · exact u19294
  · exact u19295

def r34543 : Route 9 := (fun mask => (mask,id))

def c34543 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34543 : Upper (D 7) (R 7) [34,68,129,96,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,384] 13 (by decide) (choices 1) [1,2,8,16] r34543 c34543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19296
  · exact u19297
  · exact u19298
  · exact u19299

def b34544 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 98 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,6)], upper := (rows 35 70 133 137 274 120 120 248 376), lower := (rows 35 70 133 137 274 32 64 128 256), losses := [] }

theorem u34544 : Upper (D 7) (R 7) [34,68,129,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34545 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 8, targets := 98 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,6)], upper := (rows 35 70 133 137 280 114 114 242 370), lower := (rows 35 70 133 137 280 32 64 128 256), losses := [] }

theorem u34545 : Upper (D 7) (R 7) [34,68,129,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34546 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 8, targets := 98 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,6)], upper := (rows 35 70 133 137 304 122 90 218 346), lower := (rows 35 70 133 137 304 32 64 128 256), losses := [] }

theorem u34546 : Upper (D 7) (R 7) [34,68,129,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34547 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 8, targets := 98 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,6)], upper := (rows 35 70 133 137 336 58 122 186 314), lower := (rows 35 70 133 137 336 32 64 128 256), losses := [] }

theorem u34547 : Upper (D 7) (R 7) [34,68,129,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34548 : Route 9 := (fun mask => (mask,id))

def c34548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34548 : Upper (D 7) (R 7) [34,68,129,130,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,130,257] 13 (by decide) (choices 1) [8,16,64] r34548 c34548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19300
  · exact u19301
  · exact u19302

def r34549 : Route 9 := (fun mask => (mask,id))

def c34549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34549 : Upper (D 7) (R 7) [34,68,129,130,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,130,264] 13 (by decide) (choices 1) [1,16,64] r34549 c34549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19303
  · exact u19304
  · exact u19305

def r34550 : Route 9 := (fun mask => (mask,id))

def c34550 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34550 : Upper (D 7) (R 7) [34,68,129,130,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,130,288] 13 (by decide) (choices 1) [1,8,16,64] r34550 c34550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19306
  · exact u19307
  · exact u19308
  · exact u19309

def r34551 : Route 9 := (fun mask => (mask,id))

def c34551 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34551 : Upper (D 7) (R 7) [34,68,129,130,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,130,320] 13 (by decide) (choices 1) [1,8,16] r34551 c34551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19310
  · exact u19311
  · exact u19312

def r34552 : Route 9 := (fun mask => (mask,id))

def c34552 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34552 : Upper (D 7) (R 7) [34,68,129,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,257] 13 (by decide) (choices 1) [2,8,64] r34552 c34552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19313
  · exact u19314
  · exact u19315

def r34553 : Route 9 := (fun mask => (mask,id))

def c34553 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34553 : Upper (D 7) (R 7) [34,68,129,144,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,258] 13 (by decide) (choices 1) [1,8,64] r34553 c34553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19316
  · exact u19317
  · exact u19318

def r34554 : Route 9 := (fun mask => (mask,id))

def c34554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34554 : Upper (D 7) (R 7) [34,68,129,144,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,264] 13 (by decide) (choices 1) [1,2,64] r34554 c34554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19319
  · exact u19320
  · exact u19321

def r34555 : Route 9 := (fun mask => (mask,id))

def c34555 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34555 : Upper (D 7) (R 7) [34,68,129,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,288] 13 (by decide) (choices 1) [1,2,8,64] r34555 c34555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19322
  · exact u19323
  · exact u19324
  · exact u19325

def r34556 : Route 9 := (fun mask => (mask,id))

def c34556 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34556 : Upper (D 7) (R 7) [34,68,129,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,320] 13 (by decide) (choices 1) [1,2,8] r34556 c34556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19326
  · exact u19327
  · exact u19328

def r34557 : Route 9 := (fun mask => (mask,id))

def c34557 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34557 : Upper (D 7) (R 7) [34,68,129,160,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,257] 13 (by decide) (choices 1) [2,8,16,64] r34557 c34557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19329
  · exact u19330
  · exact u19331
  · exact u19332

def r34558 : Route 9 := (fun mask => (mask,id))

def c34558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34558 : Upper (D 7) (R 7) [34,68,129,160,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,258] 13 (by decide) (choices 1) [1,8,16,64] r34558 c34558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19333
  · exact u19334
  · exact u19335
  · exact u19336

def r34559 : Route 9 := (fun mask => (mask,id))

def c34559 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34559 : Upper (D 7) (R 7) [34,68,129,160,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,264] 13 (by decide) (choices 1) [1,2,16,64] r34559 c34559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19337
  · exact u19338
  · exact u19339
  · exact u19340

#print axioms u34559
end Delivery.IrregularNine14.P07
