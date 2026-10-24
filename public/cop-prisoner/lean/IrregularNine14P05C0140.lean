import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0081
import IrregularNine14P05C0082

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8400 : Route 9 := (fun mask => (mask,id))

def c8400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8400 : Upper (D 5) (R 5) [34,192,48,257,10] 13 := by
  apply FastRouting.sound _ _ [34,192,48,257,10] 13 (by decide) (choices 1) [1,4,8] r8400 c8400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4909
  · exact u4910
  · exact u4911

def r8401 : Route 9 := (fun mask => (mask,id))

def c8401 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8401 : Upper (D 5) (R 5) [34,192,48,257,12] 13 := by
  apply FastRouting.sound _ _ [34,192,48,257,12] 13 (by decide) (choices 1) [1,2,4,8] r8401 c8401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4912
  · exact u4913
  · exact u4914
  · exact u4915

def b8402 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 20, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 194 52 266 21 45 77 141 269), lower := (rows 35 194 52 266 21 32 64 128 256), losses := [] }

theorem u8402 : Upper (D 5) (R 5) [34,192,48,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8402
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8403 : Route 9 := (fun mask => (mask,id))

def c8403 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8403 : Upper (D 5) (R 5) [34,192,48,258,9] 13 := by
  apply FastRouting.sound _ _ [34,192,48,258,9] 13 (by decide) (choices 1) [1,4,8] r8403 c8403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4916
  · exact u4917
  · exact u4918

def r8404 : Route 9 := (fun mask => (mask,id))

def c8404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8404 : Upper (D 5) (R 5) [34,192,48,258,12] 13 := by
  apply FastRouting.sound _ _ [34,192,48,258,12] 13 (by decide) (choices 1) [1,4,8] r8404 c8404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4919
  · exact u4920
  · exact u4921

def b8405 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 194 52 268 19 45 77 141 269), lower := (rows 35 194 52 268 19 32 64 128 256), losses := [] }

theorem u8405 : Upper (D 5) (R 5) [34,192,48,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8405
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8406 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 20, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 35 194 52 268 21 43 75 139 267), lower := (rows 35 194 52 268 21 32 64 128 256), losses := [] }

theorem u8406 : Upper (D 5) (R 5) [34,192,48,260,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8406
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8407 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 20, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 194 52 268 22 41 73 137 265), lower := (rows 35 194 52 268 22 32 64 128 256), losses := [] }

theorem u8407 : Upper (D 5) (R 5) [34,192,48,260,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8407
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8408 : Route 9 := (fun mask => (mask,id))

def c8408 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8408 : Upper (D 5) (R 5) [34,192,48,260,9] 13 := by
  apply FastRouting.sound _ _ [34,192,48,260,9] 13 (by decide) (choices 1) [1,2,4,8] r8408 c8408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4922
  · exact u4923
  · exact u4924
  · exact u4925

def r8409 : Route 9 := (fun mask => (mask,id))

def c8409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8409 : Upper (D 5) (R 5) [34,192,48,260,10] 13 := by
  apply FastRouting.sound _ _ [34,192,48,260,10] 13 (by decide) (choices 1) [1,4,8] r8409 c8409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4926
  · exact u4927
  · exact u4928

def b8410 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 194 52 268 28 43 75 139 267), lower := (rows 35 194 52 268 28 32 64 128 256), losses := [] }

theorem u8410 : Upper (D 5) (R 5) [34,192,48,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8410
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8411 : Route 9 := (fun mask => (mask,id))

def c8411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8411 : Upper (D 5) (R 5) [48,65,129,258,6] 13 := by
  apply FastRouting.sound _ _ [48,65,129,258,6] 13 (by decide) (choices 1) [4,8] r8411 c8411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4929
  · exact u4930

def b8412 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 49 67 133 266 26 44 108 172 300), lower := (rows 49 67 133 266 26 32 64 128 256), losses := [] }

theorem u8412 : Upper (D 5) (R 5) [48,65,129,258,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8412
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8413 : Route 9 := (fun mask => (mask,id))

def c8413 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8413 : Upper (D 5) (R 5) [48,65,129,258,12] 13 := by
  apply FastRouting.sound _ _ [48,65,129,258,12] 13 (by decide) (choices 1) [2,4,8] r8413 c8413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4931
  · exact u4932
  · exact u4933

def b8414 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 49 67 133 266 50 44 76 140 268), lower := (rows 49 67 133 266 50 32 64 128 256), losses := [] }

theorem u8414 : Upper (D 5) (R 5) [48,65,129,258,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8414
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8415 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 49 67 133 266 52 46 78 142 270), lower := (rows 49 67 133 266 52 32 64 128 256), losses := [] }

theorem u8415 : Upper (D 5) (R 5) [48,65,129,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8415
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8416 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 49 67 133 266 56 46 78 142 270), lower := (rows 49 67 133 266 56 32 64 128 256), losses := [] }

theorem u8416 : Upper (D 5) (R 5) [48,65,129,258,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8416
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m8417_4 : Upper (D 5) (R 5) [48,65,129,288,6,4] 13 :=
  permutation_upper _ _ _ [48,65,129,288,6,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4934

def r8417 : Route 9 := (fun mask => (mask,id))

def c8417 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8417 : Upper (D 5) (R 5) [48,65,129,288,6] 13 := by
  apply FastRouting.sound _ _ [48,65,129,288,6] 13 (by decide) (choices 1) [2,4,8] r8417 c8417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4934
  · exact m8417_4
  · exact u4935

def r8418 : Route 9 := (fun mask => (mask,id))

def c8418 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8418 : Upper (D 5) (R 5) [48,65,129,288,10] 13 := by
  apply FastRouting.sound _ _ [48,65,129,288,10] 13 (by decide) (choices 1) [2,4,8] r8418 c8418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4936
  · exact u4937
  · exact u4938

def b8419 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 49 67 134 266 21 44 108 172 300), lower := (rows 49 67 134 266 21 32 64 128 256), losses := [] }

theorem u8419 : Upper (D 5) (R 5) [48,65,130,258,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8419
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m8420_8 : Upper (D 5) (R 5) [48,65,130,258,12,8] 13 :=
  permutation_upper _ _ _ [48,65,130,258,12,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4940

def r8420 : Route 9 := (fun mask => (mask,id))

def c8420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8420 : Upper (D 5) (R 5) [48,65,130,258,12] 13 := by
  apply FastRouting.sound _ _ [48,65,130,258,12] 13 (by decide) (choices 1) [1,4,8] r8420 c8420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4939
  · exact u4940
  · exact m8420_8

def b8421 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 17, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 67 134 266 49 44 76 140 268), lower := (rows 49 67 134 266 49 32 64 128 256), losses := [] }

theorem u8421 : Upper (D 5) (R 5) [48,65,130,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8421
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8422 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 49 67 134 266 52 45 77 141 269), lower := (rows 49 67 134 266 52 32 64 128 256), losses := [] }

theorem u8422 : Upper (D 5) (R 5) [48,65,130,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8422
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8423 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 49 67 134 268 19 44 108 172 300), lower := (rows 49 67 134 268 19 32 64 128 256), losses := [] }

theorem u8423 : Upper (D 5) (R 5) [48,65,130,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8423
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8424 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 49 67 134 268 21 42 106 170 298), lower := (rows 49 67 134 268 21 32 64 128 256), losses := [] }

theorem u8424 : Upper (D 5) (R 5) [48,65,130,260,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8424
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8425 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 49 67 134 268 22 41 105 169 297), lower := (rows 49 67 134 268 22 32 64 128 256), losses := [] }

theorem u8425 : Upper (D 5) (R 5) [48,65,130,260,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8425
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8426 : PairBound 9 := { available := 46, camps := [{ cop := 1, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 49 67 134 268 25 46 110 174 302), lower := (rows 49 67 134 268 25 32 64 128 256), losses := [] }

theorem u8426 : Upper (D 5) (R 5) [48,65,130,260,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8426
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8427 : Route 9 := (fun mask => (mask,id))

def c8427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8427 : Upper (D 5) (R 5) [48,65,130,260,10] 13 := by
  apply FastRouting.sound _ _ [48,65,130,260,10] 13 (by decide) (choices 1) [1,4,8] r8427 c8427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4941
  · exact u4942
  · exact u4943

def b8428 : PairBound 9 := { available := 43, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 49 67 134 268 28 43 107 171 299), lower := (rows 49 67 134 268 28 32 64 128 256), losses := [] }

theorem u8428 : Upper (D 5) (R 5) [48,65,130,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8428
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8429 : PairBound 9 := { available := 14, camps := [{ cop := 5, region := 17, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 67 134 268 49 46 78 142 270), lower := (rows 49 67 134 268 49 32 64 128 256), losses := [] }

theorem u8429 : Upper (D 5) (R 5) [48,65,130,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8429
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8430 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 49 67 134 268 50 45 77 141 269), lower := (rows 49 67 134 268 50 32 64 128 256), losses := [] }

theorem u8430 : Upper (D 5) (R 5) [48,65,130,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8430
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8431 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 49 67 134 268 52 43 75 139 267), lower := (rows 49 67 134 268 52 32 64 128 256), losses := [] }

theorem u8431 : Upper (D 5) (R 5) [48,65,130,260,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8431
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8432 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 49 67 134 268 56 47 79 143 271), lower := (rows 49 67 134 268 56 32 64 128 256), losses := [] }

theorem u8432 : Upper (D 5) (R 5) [48,65,130,260,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8432
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8433 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 49 67 134 296 19 44 76 140 268), lower := (rows 49 67 134 296 19 32 64 128 256), losses := [] }

theorem u8433 : Upper (D 5) (R 5) [48,65,130,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8433
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8434 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 49 67 134 296 21 46 78 142 270), lower := (rows 49 67 134 296 21 32 64 128 256), losses := [] }

theorem u8434 : Upper (D 5) (R 5) [48,65,130,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8434
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8435 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 16, targets := 9 }], pairs := [(4,0),(4,3)], upper := (rows 49 67 134 296 22 45 77 141 269), lower := (rows 49 67 134 296 22 32 64 128 256), losses := [] }

theorem u8435 : Upper (D 5) (R 5) [48,65,130,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8435
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8436 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 17, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 67 134 296 25 46 78 142 270), lower := (rows 49 67 134 296 25 32 64 128 256), losses := [] }

theorem u8436 : Upper (D 5) (R 5) [48,65,130,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8436
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8437 : Route 9 := (fun mask => (mask,id))

def c8437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8437 : Upper (D 5) (R 5) [48,65,130,288,10] 13 := by
  apply FastRouting.sound _ _ [48,65,130,288,10] 13 (by decide) (choices 1) [1,4,8] r8437 c8437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4944
  · exact u4945
  · exact u4946

def r8438 : Route 9 := (fun mask => (mask,id))

def c8438 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8438 : Upper (D 5) (R 5) [48,65,130,288,12] 13 := by
  apply FastRouting.sound _ _ [48,65,130,288,12] 13 (by decide) (choices 1) [1,2,4,8] r8438 c8438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4947
  · exact u4948
  · exact u4949
  · exact u4950

def b8439 : PairBound 9 := { available := 46, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 49 67 140 268 19 46 110 174 302), lower := (rows 49 67 140 268 19 32 64 128 256), losses := [] }

theorem u8439 : Upper (D 5) (R 5) [48,65,136,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8439
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8440 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 49 67 140 268 21 42 106 170 298), lower := (rows 49 67 140 268 21 32 64 128 256), losses := [] }

theorem u8440 : Upper (D 5) (R 5) [48,65,136,260,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8440
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8441 : Route 9 := (fun mask => (mask,id))

def c8441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8441 : Upper (D 5) (R 5) [48,65,136,260,6] 13 := by
  apply FastRouting.sound _ _ [48,65,136,260,6] 13 (by decide) (choices 1) [1,2,8] r8441 c8441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4951
  · exact u4952
  · exact u4953

def b8442 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 49 67 140 268 28 35 99 163 291), lower := (rows 49 67 140 268 28 32 64 128 256), losses := [] }

theorem u8442 : Upper (D 5) (R 5) [48,65,136,260,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8442
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8443 : PairBound 9 := { available := 14, camps := [{ cop := 5, region := 17, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 67 140 268 49 46 78 142 270), lower := (rows 49 67 140 268 49 32 64 128 256), losses := [] }

theorem u8443 : Upper (D 5) (R 5) [48,65,136,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8443
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8444 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 49 67 140 268 50 47 79 143 271), lower := (rows 49 67 140 268 50 32 64 128 256), losses := [] }

theorem u8444 : Upper (D 5) (R 5) [48,65,136,260,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8444
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8445 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 49 67 140 268 52 43 75 139 267), lower := (rows 49 67 140 268 52 32 64 128 256), losses := [] }

theorem u8445 : Upper (D 5) (R 5) [48,65,136,260,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8445
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8446 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 49 67 140 296 19 46 78 142 270), lower := (rows 49 67 140 296 19 32 64 128 256), losses := [] }

theorem u8446 : Upper (D 5) (R 5) [48,65,136,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8446
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8447 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 428, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 49 67 140 296 21 46 78 142 270), lower := (rows 49 67 140 296 21 32 64 128 256), losses := [] }

theorem u8447 : Upper (D 5) (R 5) [48,65,136,288,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8447
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8448 : Route 9 := (fun mask => (mask,id))

def c8448 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8448 : Upper (D 5) (R 5) [48,65,136,288,6] 13 := by
  apply FastRouting.sound _ _ [48,65,136,288,6] 13 (by decide) (choices 1) [1,2,4,8] r8448 c8448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4954
  · exact u4955
  · exact u4956
  · exact u4957

def b8449 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 17, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 67 140 296 25 38 70 134 262), lower := (rows 49 67 140 296 25 32 64 128 256), losses := [] }

theorem u8449 : Upper (D 5) (R 5) [48,65,136,288,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8449
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8450 : Route 9 := (fun mask => (mask,id))

def c8450 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8450 : Upper (D 5) (R 5) [48,65,136,288,10] 13 := by
  apply FastRouting.sound _ _ [48,65,136,288,10] 13 (by decide) (choices 1) [1,2,4] r8450 c8450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4958
  · exact u4959
  · exact u4960

def b8451 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 49 67 140 296 28 39 71 135 263), lower := (rows 49 67 140 296 28 32 64 128 256), losses := [] }

theorem u8451 : Upper (D 5) (R 5) [48,65,136,288,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8451
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8452 : Route 9 := (fun mask => (mask,id))

def c8452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8452 : Upper (D 5) (R 5) [48,68,130,258,5] 13 := by
  apply FastRouting.sound _ _ [48,68,130,258,5] 13 (by decide) (choices 1) [1,8] r8452 c8452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4961
  · exact u4962

def r8453 : Route 9 := (fun mask => (mask,id))

def c8453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8453 : Upper (D 5) (R 5) [48,68,130,258,9] 13 := by
  apply FastRouting.sound _ _ [48,68,130,258,9] 13 (by decide) (choices 1) [1,4,8] r8453 c8453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4963
  · exact u4964
  · exact u4965

def b8454 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 33, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 70 134 266 28 41 105 169 297), lower := (rows 49 70 134 266 28 32 64 128 256), losses := [] }

theorem u8454 : Upper (D 5) (R 5) [48,68,130,258,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8454
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8455 : PairBound 9 := { available := 13, camps := [{ cop := 5, region := 17, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 70 134 266 49 45 77 141 269), lower := (rows 49 70 134 266 49 32 64 128 256), losses := [] }

theorem u8455 : Upper (D 5) (R 5) [48,68,130,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8455
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8456 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 49 70 134 266 52 41 73 137 265), lower := (rows 49 70 134 266 52 32 64 128 256), losses := [] }

theorem u8456 : Upper (D 5) (R 5) [48,68,130,258,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8456
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8457 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 49 70 134 266 56 45 77 141 269), lower := (rows 49 70 134 266 56 32 64 128 256), losses := [] }

theorem u8457 : Upper (D 5) (R 5) [48,68,130,258,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8457
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8458 : Route 9 := (fun mask => (mask,id))

def c8458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8458 : Upper (D 5) (R 5) [48,68,130,288,3] 13 := by
  apply FastRouting.sound _ _ [48,68,130,288,3] 13 (by decide) (choices 1) [1,4,8] r8458 c8458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4966
  · exact u4967
  · exact u4968

def b8459 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 297, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 49 70 134 296 22 41 73 137 265), lower := (rows 49 70 134 296 22 32 64 128 256), losses := [] }

theorem u8459 : Upper (D 5) (R 5) [48,68,130,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8459
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u8459
end Delivery.IrregularNine14.P05
