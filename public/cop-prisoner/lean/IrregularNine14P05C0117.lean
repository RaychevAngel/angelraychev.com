import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0058
import IrregularNine14P05C0059

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7020 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 140 304 46 78 142 270), lower := (rows 19 35 69 140 304 32 64 128 256), losses := [] }

theorem u7020 : Upper (D 5) (R 5) [18,33,65,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7020
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7021 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 168 22 300 332 396 268), lower := (rows 19 35 69 168 22 32 64 128 256), losses := [] }

theorem u7021 : Upper (D 5) (R 5) [18,33,65,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7021
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7022 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 19, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 69 168 26 300 332 396 268), lower := (rows 19 35 69 168 26 32 64 128 256), losses := [] }

theorem u7022 : Upper (D 5) (R 5) [18,33,65,160,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7022
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7023 : Route 9 := (fun mask => (mask,id))

def c7023 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7023 : Upper (D 5) (R 5) [18,33,65,160,12] 13 := by
  apply FastRouting.sound _ _ [18,33,65,160,12] 13 (by decide) (choices 1) [2,4,8,256] r7023 c7023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3532
  · exact u3533
  · exact u3534
  · exact u3535

def b7024 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 168 274 44 76 140 268), lower := (rows 19 35 69 168 274 32 64 128 256), losses := [] }

theorem u7024 : Upper (D 5) (R 5) [18,33,65,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7024
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7025 : Route 9 := (fun mask => (mask,id))

def c7025 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7025 : Upper (D 5) (R 5) [18,33,65,160,260] 13 := by
  apply FastRouting.sound _ _ [18,33,65,160,260] 13 (by decide) (choices 1) [2,4,8] r7025 c7025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3536
  · exact u3537
  · exact u3538

def r7026 : Route 9 := (fun mask => (mask,id))

def c7026 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7026 : Upper (D 5) (R 5) [18,33,65,160,264] 13 := by
  apply FastRouting.sound _ _ [18,33,65,160,264] 13 (by decide) (choices 1) [2,4,8] r7026 c7026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3539
  · exact u3540
  · exact u3541

def b7027 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 392 22 44 108 172 300), lower := (rows 19 35 69 392 22 32 64 128 256), losses := [] }

theorem u7027 : Upper (D 5) (R 5) [18,33,65,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7027
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7028 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 392 26 44 108 172 300), lower := (rows 19 35 69 392 26 32 64 128 256), losses := [] }

theorem u7028 : Upper (D 5) (R 5) [18,33,65,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7028
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7029 : Route 9 := (fun mask => (mask,id))

def c7029 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7029 : Upper (D 5) (R 5) [18,33,65,384,12] 13 := by
  apply FastRouting.sound _ _ [18,33,65,384,12] 13 (by decide) (choices 1) [2,4,8] r7029 c7029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3542
  · exact u3543
  · exact u3544

def b7030 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 19, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 392 50 44 76 140 268), lower := (rows 19 35 69 392 50 32 64 128 256), losses := [] }

theorem u7030 : Upper (D 5) (R 5) [18,33,65,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7030
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7031 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 392 52 46 78 142 270), lower := (rows 19 35 69 392 52 32 64 128 256), losses := [] }

theorem u7031 : Upper (D 5) (R 5) [18,33,65,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7031
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7032 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 392 56 46 78 142 270), lower := (rows 19 35 69 392 56 32 64 128 256), losses := [] }

theorem u7032 : Upper (D 5) (R 5) [18,33,65,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7032
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7033 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 35 70 140 21 296 360 424 296), lower := (rows 19 35 70 140 21 32 64 128 256), losses := [] }

theorem u7033 : Upper (D 5) (R 5) [18,33,66,132,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7033
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7034 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 35 70 140 25 300 364 428 300), lower := (rows 19 35 70 140 25 32 64 128 256), losses := [] }

theorem u7034 : Upper (D 5) (R 5) [18,33,66,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7034
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7035 : PairBound 9 := { available := 297, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 35 70 140 28 297 361 425 297), lower := (rows 19 35 70 140 28 32 64 128 256), losses := [] }

theorem u7035 : Upper (D 5) (R 5) [18,33,66,132,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7035
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7036 : PairBound 9 := { available := 268, camps := [{ cop := 5, region := 19, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 70 140 49 300 332 396 268), lower := (rows 19 35 70 140 49 32 64 128 256), losses := [] }

theorem u7036 : Upper (D 5) (R 5) [18,33,66,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7036
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7037 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 70 140 52 297 329 393 265), lower := (rows 19 35 70 140 52 32 64 128 256), losses := [] }

theorem u7037 : Upper (D 5) (R 5) [18,33,66,132,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7037
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7038 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 70 140 56 301 333 397 269), lower := (rows 19 35 70 140 56 32 64 128 256), losses := [] }

theorem u7038 : Upper (D 5) (R 5) [18,33,66,132,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7038
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7039 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 35 70 140 273 44 108 172 300), lower := (rows 19 35 70 140 273 32 64 128 256), losses := [] }

theorem u7039 : Upper (D 5) (R 5) [18,33,66,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7039
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7040 : Route 9 := (fun mask => (mask,id))

def c7040 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7040 : Upper (D 5) (R 5) [18,33,66,132,260] 13 := by
  apply FastRouting.sound _ _ [18,33,66,132,260] 13 (by decide) (choices 1) [1,8] r7040 c7040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3545
  · exact u3546

def r7041 : Route 9 := (fun mask => (mask,id))

def c7041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7041 : Upper (D 5) (R 5) [18,33,66,132,264] 13 := by
  apply FastRouting.sound _ _ [18,33,66,132,264] 13 (by decide) (choices 1) [1,4,8] r7041 c7041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3547
  · exact u3548
  · exact u3549

def b7042 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 70 140 304 45 77 141 269), lower := (rows 19 35 70 140 304 32 64 128 256), losses := [] }

theorem u7042 : Upper (D 5) (R 5) [18,33,66,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7042
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7043 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 35 70 168 21 300 332 396 268), lower := (rows 19 35 70 168 21 32 64 128 256), losses := [] }

theorem u7043 : Upper (D 5) (R 5) [18,33,66,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7043
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7044 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 19, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 70 168 25 300 332 396 268), lower := (rows 19 35 70 168 25 32 64 128 256), losses := [] }

theorem u7044 : Upper (D 5) (R 5) [18,33,66,160,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7044
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7045 : Route 9 := (fun mask => (mask,id))

def c7045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7045 : Upper (D 5) (R 5) [18,33,66,160,12] 13 := by
  apply FastRouting.sound _ _ [18,33,66,160,12] 13 (by decide) (choices 1) [1,4,8,256] r7045 c7045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3550
  · exact u3551
  · exact u3552
  · exact u3553

def b7046 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 35 70 168 273 44 76 140 268), lower := (rows 19 35 70 168 273 32 64 128 256), losses := [] }

theorem u7046 : Upper (D 5) (R 5) [18,33,66,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7046
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7047 : Route 9 := (fun mask => (mask,id))

def c7047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7047 : Upper (D 5) (R 5) [18,33,66,160,260] 13 := by
  apply FastRouting.sound _ _ [18,33,66,160,260] 13 (by decide) (choices 1) [1,4,8] r7047 c7047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3554
  · exact u3555
  · exact u3556

def r7048 : Route 9 := (fun mask => (mask,id))

def c7048 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7048 : Upper (D 5) (R 5) [18,33,66,160,264] 13 := by
  apply FastRouting.sound _ _ [18,33,66,160,264] 13 (by decide) (choices 1) [1,4,8] r7048 c7048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3557
  · exact u3558
  · exact u3559

def b7049 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 17, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 35 70 392 21 44 108 172 300), lower := (rows 19 35 70 392 21 32 64 128 256), losses := [] }

theorem u7049 : Upper (D 5) (R 5) [18,33,66,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7049
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7050 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 35 70 392 25 44 108 172 300), lower := (rows 19 35 70 392 25 32 64 128 256), losses := [] }

theorem u7050 : Upper (D 5) (R 5) [18,33,66,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7050
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7051 : Route 9 := (fun mask => (mask,id))

def c7051 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7051 : Upper (D 5) (R 5) [18,33,66,384,12] 13 := by
  apply FastRouting.sound _ _ [18,33,66,384,12] 13 (by decide) (choices 1) [1,4,8] r7051 c7051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3560
  · exact u3561
  · exact u3562

def b7052 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 19, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 70 392 49 44 76 140 268), lower := (rows 19 35 70 392 49 32 64 128 256), losses := [] }

theorem u7052 : Upper (D 5) (R 5) [18,33,66,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7052
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7053 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 70 392 52 45 77 141 269), lower := (rows 19 35 70 392 52 32 64 128 256), losses := [] }

theorem u7053 : Upper (D 5) (R 5) [18,33,66,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7053
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7054 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 70 392 56 45 77 141 269), lower := (rows 19 35 70 392 56 32 64 128 256), losses := [] }

theorem u7054 : Upper (D 5) (R 5) [18,33,66,384,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7054
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7055 : PairBound 9 := { available := 300, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 140 19 300 364 428 300), lower := (rows 19 35 76 140 19 32 64 128 256), losses := [] }

theorem u7055 : Upper (D 5) (R 5) [18,33,72,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7055
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7056 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 35 76 140 21 298 362 426 298), lower := (rows 19 35 76 140 21 32 64 128 256), losses := [] }

theorem u7056 : Upper (D 5) (R 5) [18,33,72,132,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7056
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7057 : PairBound 9 := { available := 297, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 140 22 297 361 425 297), lower := (rows 19 35 76 140 22 32 64 128 256), losses := [] }

theorem u7057 : Upper (D 5) (R 5) [18,33,72,132,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7057
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7058 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 291, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 140 28 291 355 419 291), lower := (rows 19 35 76 140 28 32 64 128 256), losses := [] }

theorem u7058 : Upper (D 5) (R 5) [18,33,72,132,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7058
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7059 : PairBound 9 := { available := 270, camps := [{ cop := 5, region := 19, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 140 49 302 334 398 270), lower := (rows 19 35 76 140 49 32 64 128 256), losses := [] }

theorem u7059 : Upper (D 5) (R 5) [18,33,72,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7059
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7060 : PairBound 9 := { available := 269, camps := [{ cop := 5, region := 19, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 140 50 301 333 397 269), lower := (rows 19 35 76 140 50 32 64 128 256), losses := [] }

theorem u7060 : Upper (D 5) (R 5) [18,33,72,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7060
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7061 : PairBound 9 := { available := 267, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 140 52 299 331 395 267), lower := (rows 19 35 76 140 52 32 64 128 256), losses := [] }

theorem u7061 : Upper (D 5) (R 5) [18,33,72,132,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7061
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7062 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 35 76 140 273 46 110 174 302), lower := (rows 19 35 76 140 273 32 64 128 256), losses := [] }

theorem u7062 : Upper (D 5) (R 5) [18,33,72,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7062
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7063 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 140 274 45 109 173 301), lower := (rows 19 35 76 140 274 32 64 128 256), losses := [] }

theorem u7063 : Upper (D 5) (R 5) [18,33,72,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7063
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7064 : Route 9 := (fun mask => (mask,id))

def c7064 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7064 : Upper (D 5) (R 5) [18,33,72,132,260] 13 := by
  apply FastRouting.sound _ _ [18,33,72,132,260] 13 (by decide) (choices 1) [1,2,8] r7064 c7064
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3563
  · exact u3564
  · exact u3565

def b7065 : PairBound 9 := { available := 15, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 140 304 47 79 143 271), lower := (rows 19 35 76 140 304 32 64 128 256), losses := [] }

theorem u7065 : Upper (D 5) (R 5) [18,33,72,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7065
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7066 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 168 19 300 332 396 268), lower := (rows 19 35 76 168 19 32 64 128 256), losses := [] }

theorem u7066 : Upper (D 5) (R 5) [18,33,72,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7066
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7067 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 35 76 168 21 302 334 398 270), lower := (rows 19 35 76 168 21 32 64 128 256), losses := [] }

theorem u7067 : Upper (D 5) (R 5) [18,33,72,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7067
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7068 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 168 22 301 333 397 269), lower := (rows 19 35 76 168 22 32 64 128 256), losses := [] }

theorem u7068 : Upper (D 5) (R 5) [18,33,72,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7068
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7069 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 19, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 76 168 25 294 326 390 262), lower := (rows 19 35 76 168 25 32 64 128 256), losses := [] }

theorem u7069 : Upper (D 5) (R 5) [18,33,72,160,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7069
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7070 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 19, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 76 168 26 293 325 389 261), lower := (rows 19 35 76 168 26 32 64 128 256), losses := [] }

theorem u7070 : Upper (D 5) (R 5) [18,33,72,160,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7070
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7071 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 35 76 168 28 295 327 391 263), lower := (rows 19 35 76 168 28 32 64 128 256), losses := [] }

theorem u7071 : Upper (D 5) (R 5) [18,33,72,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7071
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7072 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 35 76 168 273 46 78 142 270), lower := (rows 19 35 76 168 273 32 64 128 256), losses := [] }

theorem u7072 : Upper (D 5) (R 5) [18,33,72,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7072
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7073 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 168 274 45 77 141 269), lower := (rows 19 35 76 168 274 32 64 128 256), losses := [] }

theorem u7073 : Upper (D 5) (R 5) [18,33,72,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7073
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7074 : Route 9 := (fun mask => (mask,id))

def c7074 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7074 : Upper (D 5) (R 5) [18,33,72,160,260] 13 := by
  apply FastRouting.sound _ _ [18,33,72,160,260] 13 (by decide) (choices 1) [1,2,4,8] r7074 c7074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3566
  · exact u3567
  · exact u3568
  · exact u3569

def r7075 : Route 9 := (fun mask => (mask,id))

def c7075 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7075 : Upper (D 5) (R 5) [18,33,72,160,264] 13 := by
  apply FastRouting.sound _ _ [18,33,72,160,264] 13 (by decide) (choices 1) [1,2,4] r7075 c7075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3570
  · exact u3571
  · exact u3572

def b7076 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 392 19 44 108 172 300), lower := (rows 19 35 76 392 19 32 64 128 256), losses := [] }

theorem u7076 : Upper (D 5) (R 5) [18,33,72,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7076
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7077 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 35 76 392 21 46 110 174 302), lower := (rows 19 35 76 392 21 32 64 128 256), losses := [] }

theorem u7077 : Upper (D 5) (R 5) [18,33,72,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7077
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7078 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 76 392 22 45 109 173 301), lower := (rows 19 35 76 392 22 32 64 128 256), losses := [] }

theorem u7078 : Upper (D 5) (R 5) [18,33,72,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7078
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7079 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 35 76 392 25 38 102 166 294), lower := (rows 19 35 76 392 25 32 64 128 256), losses := [] }

theorem u7079 : Upper (D 5) (R 5) [18,33,72,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7079
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u7079
end Delivery.IrregularNine14.P05
