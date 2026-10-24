import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0056
import IrregularNine14P01C0057
import IrregularNine14P01C0058

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7020 : Route 9 := (fun mask => (mask,id))

def c7020 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7020 : Upper (D 1) (R 1) [52,80,192,257] 13 := by
  apply FastRouting.sound _ _ [52,80,192,257] 13 (by decide) (choices 1) [2,8,32,128] r7020 c7020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3419
  · exact u3420
  · exact u3421
  · exact u3422

def r7021 : Route 9 := (fun mask => (mask,id))

def c7021 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7021 : Upper (D 1) (R 1) [52,80,192,258] 13 := by
  apply FastRouting.sound _ _ [52,80,192,258] 13 (by decide) (choices 1) [1,2,8,32,128] r7021 c7021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3423
  · exact u3424
  · exact u3425
  · exact u3426
  · exact u3427

def r7022 : Route 9 := (fun mask => (mask,id))

def c7022 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7022 : Upper (D 1) (R 1) [52,80,192,288] 13 := by
  apply FastRouting.sound _ _ [52,80,192,288] 13 (by decide) (choices 1) [1,2,8,128] r7022 c7022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3428
  · exact u3429
  · exact u3430
  · exact u3431

def r7023 : Route 9 := (fun mask => (mask,id))

def c7023 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7023 : Upper (D 1) (R 1) [52,80,192,384] 13 := by
  apply FastRouting.sound _ _ [52,80,192,384] 13 (by decide) (choices 1) [1,2,8,32] r7023 c7023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3432
  · exact u3433
  · exact u3434
  · exact u3435

def b7024 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 82 262 11 248 232 232 232 488), lower := (rows 53 82 262 11 16 32 64 128 256), losses := [] }

theorem u7024 : Upper (D 1) (R 1) [52,80,258,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7024
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7025 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 262 41 218 234 202 202 458), lower := (rows 53 82 262 41 16 32 64 128 256), losses := [] }

theorem u7025 : Upper (D 1) (R 1) [52,80,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7025
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7026 : Route 9 := (fun mask => (mask,id))

def c7026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7026 : Upper (D 1) (R 1) [52,80,258,34] 13 := by
  apply FastRouting.sound _ _ [52,80,258,34] 13 (by decide) (choices 1) [1,8,64,128] r7026 c7026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3436
  · exact u3437
  · exact u3438
  · exact u3439

def r7027 : Route 9 := (fun mask => (mask,id))

def c7027 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7027 : Upper (D 1) (R 1) [52,80,258,65] 13 := by
  apply FastRouting.sound _ _ [52,80,258,65] 13 (by decide) (choices 1) [2,8,32,128] r7027 c7027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3440
  · exact u3441
  · exact u3442
  · exact u3443

def b7028 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 82 262 74 185 169 233 169 425), lower := (rows 53 82 262 74 16 32 64 128 256), losses := [] }

theorem u7028 : Upper (D 1) (R 1) [52,80,258,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7028
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7029 : Route 9 := (fun mask => (mask,id))

def c7029 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7029 : Upper (D 1) (R 1) [52,80,258,96] 13 := by
  apply FastRouting.sound _ _ [52,80,258,96] 13 (by decide) (choices 1) [1,2,8,128] r7029 c7029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3444
  · exact u3445
  · exact u3446
  · exact u3447

def r7030 : Route 9 := (fun mask => (mask,id))

def c7030 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7030 : Upper (D 1) (R 1) [52,80,258,129] 13 := by
  apply FastRouting.sound _ _ [52,80,258,129] 13 (by decide) (choices 1) [2,8,32,64,128] r7030 c7030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3448
  · exact u3449
  · exact u3450
  · exact u3451
  · exact u3452

def r7031 : Route 9 := (fun mask => (mask,id))

def c7031 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u7031 : Upper (D 1) (R 1) [52,80,258,130] 13 := by
  apply FastRouting.sound _ _ [52,80,258,130] 13 (by decide) (choices 1) [1,8,32,64,128] r7031 c7031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3453
  · exact u3454
  · exact u3455
  · exact u3456
  · exact u3457

def r7032 : Route 9 := (fun mask => (mask,id))

def c7032 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7032 : Upper (D 1) (R 1) [52,80,258,160] 13 := by
  apply FastRouting.sound _ _ [52,80,258,160] 13 (by decide) (choices 1) [1,2,8,64,128] r7032 c7032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3458
  · exact u3459
  · exact u3460
  · exact u3461
  · exact u3462

def r7033 : Route 9 := (fun mask => (mask,id))

def c7033 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7033 : Upper (D 1) (R 1) [52,80,258,192] 13 := by
  apply FastRouting.sound _ _ [52,80,258,192] 13 (by decide) (choices 1) [1,2,8,32,128] r7033 c7033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3463
  · exact u3464
  · exact u3465
  · exact u3466
  · exact u3467

def b7034 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 82 268 11 242 226 226 226 482), lower := (rows 53 82 268 11 16 32 64 128 256), losses := [] }

theorem u7034 : Upper (D 1) (R 1) [52,80,264,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7034
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7035 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 268 41 210 226 194 194 450), lower := (rows 53 82 268 41 16 32 64 128 256), losses := [] }

theorem u7035 : Upper (D 1) (R 1) [52,80,264,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7035
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7036 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 268 42 211 227 195 195 451), lower := (rows 53 82 268 42 16 32 64 128 256), losses := [] }

theorem u7036 : Upper (D 1) (R 1) [52,80,264,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7036
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7037 : Route 9 := (fun mask => (mask,id))

def c7037 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7037 : Upper (D 1) (R 1) [52,80,264,65] 13 := by
  apply FastRouting.sound _ _ [52,80,264,65] 13 (by decide) (choices 1) [2,32,128] r7037 c7037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3468
  · exact u3469
  · exact u3470

def b7038 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 82 268 74 179 163 227 163 419), lower := (rows 53 82 268 74 16 32 64 128 256), losses := [] }

theorem u7038 : Upper (D 1) (R 1) [52,80,264,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7038
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7039 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 268 104 147 163 195 131 387), lower := (rows 53 82 268 104 16 32 64 128 256), losses := [] }

theorem u7039 : Upper (D 1) (R 1) [52,80,264,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7039
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7040 : Route 9 := (fun mask => (mask,id))

def c7040 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7040 : Upper (D 1) (R 1) [52,80,264,129] 13 := by
  apply FastRouting.sound _ _ [52,80,264,129] 13 (by decide) (choices 1) [2,32,64,128] r7040 c7040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3471
  · exact u3472
  · exact u3473
  · exact u3474

def r7041 : Route 9 := (fun mask => (mask,id))

def c7041 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7041 : Upper (D 1) (R 1) [52,80,264,130] 13 := by
  apply FastRouting.sound _ _ [52,80,264,130] 13 (by decide) (choices 1) [1,2,32,64,128] r7041 c7041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3475
  · exact u3476
  · exact u3477
  · exact u3478
  · exact u3479

def b7042 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 268 168 211 227 195 195 451), lower := (rows 53 82 268 168 16 32 64 128 256), losses := [] }

theorem u7042 : Upper (D 1) (R 1) [52,80,264,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7042
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7043 : Route 9 := (fun mask => (mask,id))

def c7043 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7043 : Upper (D 1) (R 1) [52,80,264,192] 13 := by
  apply FastRouting.sound _ _ [52,80,264,192] 13 (by decide) (choices 1) [1,2,32,128] r7043 c7043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3480
  · exact u3481
  · exact u3482
  · exact u3483

def b7044 : PairBound 9 := { available := 170, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 82 324 11 186 170 234 170 426), lower := (rows 53 82 324 11 16 32 64 128 256), losses := [] }

theorem u7044 : Upper (D 1) (R 1) [52,80,320,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7044
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7045 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 324 41 154 170 202 138 394), lower := (rows 53 82 324 41 16 32 64 128 256), losses := [] }

theorem u7045 : Upper (D 1) (R 1) [52,80,320,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7045
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7046 : Route 9 := (fun mask => (mask,id))

def c7046 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7046 : Upper (D 1) (R 1) [52,80,320,34] 13 := by
  apply FastRouting.sound _ _ [52,80,320,34] 13 (by decide) (choices 1) [1,2,8,128] r7046 c7046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3484
  · exact u3485
  · exact u3486
  · exact u3487

def r7047 : Route 9 := (fun mask => (mask,id))

def c7047 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7047 : Upper (D 1) (R 1) [52,80,320,129] 13 := by
  apply FastRouting.sound _ _ [52,80,320,129] 13 (by decide) (choices 1) [2,8,32,128] r7047 c7047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3488
  · exact u3489
  · exact u3490
  · exact u3491

def r7048 : Route 9 := (fun mask => (mask,id))

def c7048 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7048 : Upper (D 1) (R 1) [52,80,320,130] 13 := by
  apply FastRouting.sound _ _ [52,80,320,130] 13 (by decide) (choices 1) [1,2,8,32,128] r7048 c7048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3492
  · exact u3493
  · exact u3494
  · exact u3495
  · exact u3496

def r7049 : Route 9 := (fun mask => (mask,id))

def c7049 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7049 : Upper (D 1) (R 1) [52,80,320,160] 13 := by
  apply FastRouting.sound _ _ [52,80,320,160] 13 (by decide) (choices 1) [1,2,8,128] r7049 c7049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3497
  · exact u3498
  · exact u3499
  · exact u3500

def b7050 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 82 388 11 250 234 234 234 490), lower := (rows 53 82 388 11 16 32 64 128 256), losses := [] }

theorem u7050 : Upper (D 1) (R 1) [52,80,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7050
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7051 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 388 41 218 234 202 202 458), lower := (rows 53 82 388 41 16 32 64 128 256), losses := [] }

theorem u7051 : Upper (D 1) (R 1) [52,80,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7051
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7052 : Route 9 := (fun mask => (mask,id))

def c7052 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7052 : Upper (D 1) (R 1) [52,80,384,34] 13 := by
  apply FastRouting.sound _ _ [52,80,384,34] 13 (by decide) (choices 1) [1,2,8,64,128] r7052 c7052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3501
  · exact u3502
  · exact u3503
  · exact u3504
  · exact u3505

def r7053 : Route 9 := (fun mask => (mask,id))

def c7053 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7053 : Upper (D 1) (R 1) [52,80,384,65] 13 := by
  apply FastRouting.sound _ _ [52,80,384,65] 13 (by decide) (choices 1) [2,8,32,128] r7053 c7053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3506
  · exact u3507
  · exact u3508
  · exact u3509

def b7054 : PairBound 9 := { available := 171, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 82 388 74 187 171 235 171 427), lower := (rows 53 82 388 74 16 32 64 128 256), losses := [] }

theorem u7054 : Upper (D 1) (R 1) [52,80,384,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7054
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7055 : Route 9 := (fun mask => (mask,id))

def c7055 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7055 : Upper (D 1) (R 1) [52,80,384,96] 13 := by
  apply FastRouting.sound _ _ [52,80,384,96] 13 (by decide) (choices 1) [1,2,8,128] r7055 c7055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3510
  · exact u3511
  · exact u3512
  · exact u3513

def b7056 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 114, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 388 137 122 106 106 234 362), lower := (rows 53 82 388 137 16 32 64 128 256), losses := [] }

theorem u7056 : Upper (D 1) (R 1) [52,80,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7056
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7057 : Route 9 := (fun mask => (mask,id))

def c7057 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7057 : Upper (D 1) (R 1) [52,80,384,130] 13 := by
  apply FastRouting.sound _ _ [52,80,384,130] 13 (by decide) (choices 1) [1,2,8,32,64] r7057 c7057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3514
  · exact u3515
  · exact u3516
  · exact u3517
  · exact u3518

def r7058 : Route 9 := (fun mask => (mask,id))

def c7058 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7058 : Upper (D 1) (R 1) [52,80,384,160] 13 := by
  apply FastRouting.sound _ _ [52,80,384,160] 13 (by decide) (choices 1) [1,2,8,64] r7058 c7058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3519
  · exact u3520
  · exact u3521
  · exact u3522

def r7059 : Route 9 := (fun mask => (mask,id))

def c7059 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7059 : Upper (D 1) (R 1) [52,80,384,192] 13 := by
  apply FastRouting.sound _ _ [52,80,384,192] 13 (by decide) (choices 1) [1,2,8,32] r7059 c7059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3523
  · exact u3524
  · exact u3525
  · exact u3526

def b7060 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 7 26 504 488 488 488 488), lower := (rows 53 194 7 26 16 32 64 128 256), losses := [] }

theorem u7060 : Upper (D 1) (R 1) [52,192,3,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7060
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7061 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 7 56 474 490 458 458 458), lower := (rows 53 194 7 56 16 32 64 128 256), losses := [] }

theorem u7061 : Upper (D 1) (R 1) [52,192,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7061
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7062 : PairBound 9 := { available := 440, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 194 7 74 440 440 504 440 440), lower := (rows 53 194 7 74 16 32 64 128 256), losses := [] }

theorem u7062 : Upper (D 1) (R 1) [52,192,3,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7062
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7063 : PairBound 9 := { available := 426, camps := [{ cop := 3, region := 418, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 7 88 442 426 490 426 426), lower := (rows 53 194 7 88 16 32 64 128 256), losses := [] }

theorem u7063 : Upper (D 1) (R 1) [52,192,3,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7063
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7064 : PairBound 9 := { available := 314, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 194 7 200 314 314 378 442 314), lower := (rows 53 194 7 200 16 32 64 128 256), losses := [] }

theorem u7064 : Upper (D 1) (R 1) [52,192,3,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7064
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7065 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u7065 : Upper (D 1) (R 1) [52,192,3,258] 13 := by
  apply FastRouting.sound _ _ [52,192,3,258] 13 (by decide) (choices 1) [8,32,64] r7065 c7065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3527
  · exact u3528
  · exact u3529

def b7066 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 7 280 250 234 234 234 490), lower := (rows 53 194 7 280 16 32 64 128 256), losses := [] }

theorem u7066 : Upper (D 1) (R 1) [52,192,3,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7066
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7067 : Route 9 := (fun mask => (mask,id))

def c7067 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7067 : Upper (D 1) (R 1) [52,192,3,320] 13 := by
  apply FastRouting.sound _ _ [52,192,3,320] 13 (by decide) (choices 1) [2,8,32,128] r7067 c7067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3530
  · exact u3531
  · exact u3532
  · exact u3533

def b7068 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 13 26 498 482 482 482 482), lower := (rows 53 194 13 26 16 32 64 128 256), losses := [] }

theorem u7068 : Upper (D 1) (R 1) [52,192,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7068
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7069 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 53 194 13 56 466 482 450 450 450), lower := (rows 53 194 13 56 16 32 64 128 256), losses := [] }

theorem u7069 : Upper (D 1) (R 1) [52,192,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7069
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7070 : PairBound 9 := { available := 434, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 194 13 74 434 434 498 434 434), lower := (rows 53 194 13 74 16 32 64 128 256), losses := [] }

theorem u7070 : Upper (D 1) (R 1) [52,192,9,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7070
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7071 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 13 88 434 418 482 418 418), lower := (rows 53 194 13 88 16 32 64 128 256), losses := [] }

theorem u7071 : Upper (D 1) (R 1) [52,192,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7071
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7072 : PairBound 9 := { available := 306, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 194 13 200 306 306 370 434 306), lower := (rows 53 194 13 200 16 32 64 128 256), losses := [] }

theorem u7072 : Upper (D 1) (R 1) [52,192,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7072
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7073 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7073 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7073 : Upper (D 1) (R 1) [52,192,9,258] 13 := by
  apply FastRouting.sound _ _ [52,192,9,258] 13 (by decide) (choices 1) [2,32,64] r7073 c7073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3534
  · exact u3535
  · exact u3536

def b7074 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 53 194 13 280 242 226 226 226 482), lower := (rows 53 194 13 280 16 32 64 128 256), losses := [] }

theorem u7074 : Upper (D 1) (R 1) [52,192,9,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7074
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7075 : Route 9 := (fun mask => (mask,id))

def c7075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7075 : Upper (D 1) (R 1) [52,192,9,320] 13 := by
  apply FastRouting.sound _ _ [52,192,9,320] 13 (by decide) (choices 1) [2,32,128] r7075 c7075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3537
  · exact u3538
  · exact u3539

def b7076 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 194 14 11 496 496 496 496 496), lower := (rows 53 194 14 11 16 32 64 128 256), losses := [] }

theorem u7076 : Upper (D 1) (R 1) [52,192,10,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7076
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7077 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 14 25 498 482 482 482 482), lower := (rows 53 194 14 25 16 32 64 128 256), losses := [] }

theorem u7077 : Upper (D 1) (R 1) [52,192,10,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7077
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7078 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 194 14 26 497 481 481 481 481), lower := (rows 53 194 14 26 16 32 64 128 256), losses := [] }

theorem u7078 : Upper (D 1) (R 1) [52,192,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7078
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7079 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 14 56 467 483 451 451 451), lower := (rows 53 194 14 56 16 32 64 128 256), losses := [] }

theorem u7079 : Upper (D 1) (R 1) [52,192,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7079
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u7079
end Delivery.IrregularNine14.P01
