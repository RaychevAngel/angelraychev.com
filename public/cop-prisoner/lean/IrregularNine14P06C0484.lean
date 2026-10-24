import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0173
import IrregularNine14P06C0174

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r29040 : Route 9 := (fun mask => (mask,id))

def c29040 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29040 : Upper (D 6) (R 6) [6,40,144,65,320] 13 := by
  apply FastRouting.sound _ _ [6,40,144,65,320] 13 (by decide) (choices 1) [1,2,4] r29040 c29040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10404
  · exact u10405
  · exact u10406

def b29041 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 148 74 21 353 353 481 353), lower := (rows 7 42 148 74 21 32 64 128 256), losses := [] }

theorem u29041 : Upper (D 6) (R 6) [6,40,144,66,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29041
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29042 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 328, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 148 74 49 357 325 453 325), lower := (rows 7 42 148 74 49 32 64 128 256), losses := [] }

theorem u29042 : Upper (D 6) (R 6) [6,40,144,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29042
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29043 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 148 74 52 353 321 449 321), lower := (rows 7 42 148 74 52 32 64 128 256), losses := [] }

theorem u29043 : Upper (D 6) (R 6) [6,40,144,66,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29043
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29044 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 420, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 7 42 148 74 81 293 357 421 293), lower := (rows 7 42 148 74 81 32 64 128 256), losses := [] }

theorem u29044 : Upper (D 6) (R 6) [6,40,144,66,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29044
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29045 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 148 74 84 289 353 417 289), lower := (rows 7 42 148 74 84 32 64 128 256), losses := [] }

theorem u29045 : Upper (D 6) (R 6) [6,40,144,66,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29045
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29046 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 148 74 112 293 325 389 261), lower := (rows 7 42 148 74 112 32 64 128 256), losses := [] }

theorem u29046 : Upper (D 6) (R 6) [6,40,144,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29046
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29047 : Route 9 := (fun mask => (mask,id))

def c29047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29047 : Upper (D 6) (R 6) [6,40,144,66,257] 13 := by
  apply FastRouting.sound _ _ [6,40,144,66,257] 13 (by decide) (choices 1) [1,4,64] r29047 c29047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10407
  · exact u10408
  · exact u10409

def b29048 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 106, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 148 74 276 97 97 225 353), lower := (rows 7 42 148 74 276 32 64 128 256), losses := [] }

theorem u29048 : Upper (D 6) (R 6) [6,40,144,66,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29048
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29049 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 148 74 304 101 69 197 325), lower := (rows 7 42 148 74 304 32 64 128 256), losses := [] }

theorem u29049 : Upper (D 6) (R 6) [6,40,144,66,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29049
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29050 : Route 9 := (fun mask => (mask,id))

def c29050 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29050 : Upper (D 6) (R 6) [6,40,144,66,320] 13 := by
  apply FastRouting.sound _ _ [6,40,144,66,320] 13 (by decide) (choices 1) [1,4] r29050 c29050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10410
  · exact u10411

def b29051 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 484, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 7 42 148 76 19 353 353 481 353), lower := (rows 7 42 148 76 19 32 64 128 256), losses := [] }

theorem u29051 : Upper (D 6) (R 6) [6,40,144,68,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29051
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29052 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 328, targets := 32 }], pairs := [(2,5),(3,5),(4,2)], upper := (rows 7 42 148 76 49 355 323 451 323), lower := (rows 7 42 148 76 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 25 16 0 65 129 257), good := (rows 463 10 156 76 477 0 64 128 256) }] }

theorem u29052 : Upper (D 6) (R 6) [6,40,144,68,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29052
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29053 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 148 76 50 353 321 449 321), lower := (rows 7 42 148 76 50 32 64 128 256), losses := [] }

theorem u29053 : Upper (D 6) (R 6) [6,40,144,68,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29053
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29054 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 291, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 148 76 81 291 355 419 291), lower := (rows 7 42 148 76 81 32 64 128 256), losses := [] }

theorem u29054 : Upper (D 6) (R 6) [6,40,144,68,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29054
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29055 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 291, targets := 64 },{ cop := 0, region := 360, targets := 2 }], pairs := [(0,6),(1,6),(3,1)], upper := (rows 7 42 148 76 82 289 353 417 289), lower := (rows 7 42 148 76 82 32 64 128 256), losses := [] }

theorem u29055 : Upper (D 6) (R 6) [6,40,144,68,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29055
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29056 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 291, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 148 76 112 291 323 387 259), lower := (rows 7 42 148 76 112 32 64 128 256), losses := [] }

theorem u29056 : Upper (D 6) (R 6) [6,40,144,68,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29056
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29057 : Route 9 := (fun mask => (mask,id))

def c29057 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29057 : Upper (D 6) (R 6) [6,40,144,68,257] 13 := by
  apply FastRouting.sound _ _ [6,40,144,68,257] 13 (by decide) (choices 1) [1,2,64] r29057 c29057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10412
  · exact u10413
  · exact u10414

def r29058 : Route 9 := (fun mask => (mask,id))

def c29058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29058 : Upper (D 6) (R 6) [6,40,144,68,258] 13 := by
  apply FastRouting.sound _ _ [6,40,144,68,258] 13 (by decide) (choices 1) [1,64] r29058 c29058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10415
  · exact u10416

def r29059 : Route 9 := (fun mask => (mask,id))

def c29059 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29059 : Upper (D 6) (R 6) [6,40,144,68,288] 13 := by
  apply FastRouting.sound _ _ [6,40,144,68,288] 13 (by decide) (choices 1) [1,2,64] r29059 c29059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10417
  · exact u10418
  · exact u10419

def b29060 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 148 76 336 35 99 163 291), lower := (rows 7 42 148 76 336 32 64 128 256), losses := [] }

theorem u29060 : Upper (D 6) (R 6) [6,40,144,68,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29060
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29061 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 7 42 148 265 19 100 100 228 356), lower := (rows 7 42 148 265 19 32 64 128 256), losses := [] }

theorem u29061 : Upper (D 6) (R 6) [6,40,144,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29061
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29062 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 42 148 265 21 98 98 226 354), lower := (rows 7 42 148 265 21 32 64 128 256), losses := [] }

theorem u29062 : Upper (D 6) (R 6) [6,40,144,257,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29062
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29063 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 16, targets := 32 }], pairs := [(1,2),(3,2),(4,5)], upper := (rows 7 42 148 265 22 97 97 225 353), lower := (rows 7 42 148 265 22 32 64 128 256), losses := [] }

theorem u29063 : Upper (D 6) (R 6) [6,40,144,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29063
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29064 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 328, targets := 32 }], pairs := [(1,0),(2,0),(3,5)], upper := (rows 7 42 148 265 49 102 70 198 326), lower := (rows 7 42 148 265 49 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 33 65 129 257), good := (rows 486 42 148 490 500 32 64 128 256) }] }

theorem u29064 : Upper (D 6) (R 6) [6,40,144,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29064
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29065 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 148 265 50 101 69 197 325), lower := (rows 7 42 148 265 50 32 64 128 256), losses := [] }

theorem u29065 : Upper (D 6) (R 6) [6,40,144,257,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29065
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29066 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 328, targets := 32 }], pairs := [(1,2),(3,2),(3,5)], upper := (rows 7 42 148 265 52 99 67 195 323), lower := (rows 7 42 148 265 52 32 64 128 256), losses := [] }

theorem u29066 : Upper (D 6) (R 6) [6,40,144,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29066
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29067 : Route 9 := (fun mask => (mask,id))

def c29067 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29067 : Upper (D 6) (R 6) [6,40,144,257,65] 13 := by
  apply FastRouting.sound _ _ [6,40,144,257,65] 13 (by decide) (choices 1) [2,4,64] r29067 c29067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10420
  · exact u10421
  · exact u10422

def r29068 : Route 9 := (fun mask => (mask,id))

def c29068 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29068 : Upper (D 6) (R 6) [6,40,144,257,66] 13 := by
  apply FastRouting.sound _ _ [6,40,144,257,66] 13 (by decide) (choices 1) [1,4,64] r29068 c29068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10423
  · exact u10424
  · exact u10425

def r29069 : Route 9 := (fun mask => (mask,id))

def c29069 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29069 : Upper (D 6) (R 6) [6,40,144,257,68] 13 := by
  apply FastRouting.sound _ _ [6,40,144,257,68] 13 (by decide) (choices 1) [1,2,64] r29069 c29069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10426
  · exact u10427
  · exact u10428

def r29070 : Route 9 := (fun mask => (mask,id))

def c29070 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29070 : Upper (D 6) (R 6) [6,40,144,257,96] 13 := by
  apply FastRouting.sound _ _ [6,40,144,257,96] 13 (by decide) (choices 1) [1,2,4,64] r29070 c29070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10429
  · exact u10430
  · exact u10431
  · exact u10432

def b29071 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 148 266 21 97 97 225 353), lower := (rows 7 42 148 266 21 32 64 128 256), losses := [] }

theorem u29071 : Upper (D 6) (R 6) [6,40,144,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29071
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29072 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 328, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 148 266 49 101 69 197 325), lower := (rows 7 42 148 266 49 32 64 128 256), losses := [] }

theorem u29072 : Upper (D 6) (R 6) [6,40,144,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29072
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29073 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 148 266 52 97 65 193 321), lower := (rows 7 42 148 266 52 32 64 128 256), losses := [] }

theorem u29073 : Upper (D 6) (R 6) [6,40,144,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29073
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29074 : Route 9 := (fun mask => (mask,id))

def c29074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29074 : Upper (D 6) (R 6) [6,40,144,258,65] 13 := by
  apply FastRouting.sound _ _ [6,40,144,258,65] 13 (by decide) (choices 1) [1,4,64] r29074 c29074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10433
  · exact u10434
  · exact u10435

def b29075 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 148 266 84 97 97 225 353), lower := (rows 7 42 148 266 84 32 64 128 256), losses := [] }

theorem u29075 : Upper (D 6) (R 6) [6,40,144,258,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29075
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29076 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 328, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 148 266 112 101 69 197 325), lower := (rows 7 42 148 266 112 32 64 128 256), losses := [] }

theorem u29076 : Upper (D 6) (R 6) [6,40,144,258,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29076
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29077 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 7 42 148 268 19 97 97 225 353), lower := (rows 7 42 148 268 19 32 64 128 256), losses := [] }

theorem u29077 : Upper (D 6) (R 6) [6,40,144,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29077
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29078 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 112, targets := 4 },{ cop := 0, region := 328, targets := 32 }], pairs := [(2,5),(3,5),(4,2)], upper := (rows 7 42 148 268 49 99 67 195 323), lower := (rows 7 42 148 268 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 25 16 0 65 129 257), good := (rows 463 10 156 268 477 0 64 128 256) }] }

theorem u29078 : Upper (D 6) (R 6) [6,40,144,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29078
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29079 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 148 268 50 97 65 193 321), lower := (rows 7 42 148 268 50 32 64 128 256), losses := [] }

theorem u29079 : Upper (D 6) (R 6) [6,40,144,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29079
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29080 : Route 9 := (fun mask => (mask,id))

def c29080 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29080 : Upper (D 6) (R 6) [6,40,144,260,65] 13 := by
  apply FastRouting.sound _ _ [6,40,144,260,65] 13 (by decide) (choices 1) [1,2,64] r29080 c29080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10436
  · exact u10437
  · exact u10438

def r29081 : Route 9 := (fun mask => (mask,id))

def c29081 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29081 : Upper (D 6) (R 6) [6,40,144,260,66] 13 := by
  apply FastRouting.sound _ _ [6,40,144,260,66] 13 (by decide) (choices 1) [1,64] r29081 c29081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10439
  · exact u10440

def r29082 : Route 9 := (fun mask => (mask,id))

def c29082 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29082 : Upper (D 6) (R 6) [6,40,144,260,96] 13 := by
  apply FastRouting.sound _ _ [6,40,144,260,96] 13 (by decide) (choices 1) [1,2,64] r29082 c29082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10441
  · exact u10442
  · exact u10443

def b29083 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 7 42 148 328 19 101 101 229 357), lower := (rows 7 42 148 328 19 32 64 128 256), losses := [] }

theorem u29083 : Upper (D 6) (R 6) [6,40,144,320,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29083
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29084 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 42 148 328 21 99 99 227 355), lower := (rows 7 42 148 328 21 32 64 128 256), losses := [] }

theorem u29084 : Upper (D 6) (R 6) [6,40,144,320,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29084
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29085 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 16, targets := 32 }], pairs := [(1,2),(3,2),(4,5)], upper := (rows 7 42 148 328 22 97 97 225 353), lower := (rows 7 42 148 328 22 32 64 128 256), losses := [] }

theorem u29085 : Upper (D 6) (R 6) [6,40,144,320,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29085
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29086 : Route 9 := (fun mask => (mask,id))

def c29086 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29086 : Upper (D 6) (R 6) [6,40,144,320,33] 13 := by
  apply FastRouting.sound _ _ [6,40,144,320,33] 13 (by decide) (choices 1) [1,2,4,64] r29086 c29086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10444
  · exact u10445
  · exact u10446
  · exact u10447

def b29087 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 148 328 50 101 69 197 325), lower := (rows 7 42 148 328 50 32 64 128 256), losses := [] }

theorem u29087 : Upper (D 6) (R 6) [6,40,144,320,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29087
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29088 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 0, region := 328, targets := 32 }], pairs := [(1,2),(3,2),(3,5)], upper := (rows 7 42 148 328 52 99 67 195 323), lower := (rows 7 42 148 328 52 32 64 128 256), losses := [] }

theorem u29088 : Upper (D 6) (R 6) [6,40,144,320,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29088
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29089 : Route 9 := (fun mask => (mask,id))

def c29089 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29089 : Upper (D 6) (R 6) [6,40,144,320,65] 13 := by
  apply FastRouting.sound _ _ [6,40,144,320,65] 13 (by decide) (choices 1) [1,2,4] r29089 c29089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10448
  · exact u10449
  · exact u10450

def b29090 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 165, targets := 64 },{ cop := 0, region := 360, targets := 2 }], pairs := [(0,6),(2,6),(3,1)], upper := (rows 7 42 148 328 82 37 101 165 293), lower := (rows 7 42 148 328 82 32 64 128 256), losses := [] }

theorem u29090 : Upper (D 6) (R 6) [6,40,144,320,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29090
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29091 : Route 9 := (fun mask => (mask,id))

def c29091 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29091 : Upper (D 6) (R 6) [6,40,144,320,68] 13 := by
  apply FastRouting.sound _ _ [6,40,144,320,68] 13 (by decide) (choices 1) [1,2] r29091 c29091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10451
  · exact u10452

def r29092 : Route 9 := (fun mask => (mask,id))

def c29092 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29092 : Upper (D 6) (R 6) [6,40,144,320,96] 13 := by
  apply FastRouting.sound _ _ [6,40,144,320,96] 13 (by decide) (choices 1) [1,2,4] r29092 c29092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10453
  · exact u10454
  · exact u10455

def b29093 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 42 164 25 19 356 324 452 324), lower := (rows 7 42 164 25 19 32 64 128 256), losses := [] }

theorem u29093 : Upper (D 6) (R 6) [6,40,160,17,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29093
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29094 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 24, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 7 42 164 25 21 354 322 450 322), lower := (rows 7 42 164 25 21 32 64 128 256), losses := [] }

theorem u29094 : Upper (D 6) (R 6) [6,40,160,17,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29094
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29095 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 164 25 22 353 321 449 321), lower := (rows 7 42 164 25 22 32 64 128 256), losses := [] }

theorem u29095 : Upper (D 6) (R 6) [6,40,160,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29095
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29096 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 42 164 25 81 358 326 454 326), lower := (rows 7 42 164 25 81 32 64 128 256), losses := [] }

theorem u29096 : Upper (D 6) (R 6) [6,40,160,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29096
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29097 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 42 164 25 82 357 325 453 325), lower := (rows 7 42 164 25 82 32 64 128 256), losses := [] }

theorem u29097 : Upper (D 6) (R 6) [6,40,160,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29097
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29098 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 3, region := 354, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 42 164 25 84 355 323 451 323), lower := (rows 7 42 164 25 84 32 64 128 256), losses := [] }

theorem u29098 : Upper (D 6) (R 6) [6,40,160,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29098
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29099 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 42 164 25 273 102 70 198 326), lower := (rows 7 42 164 25 273 32 64 128 256), losses := [] }

theorem u29099 : Upper (D 6) (R 6) [6,40,160,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29099
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u29099
end Delivery.IrregularNine14.P06
