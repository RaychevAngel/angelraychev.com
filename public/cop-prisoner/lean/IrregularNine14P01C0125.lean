import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0068
import IrregularNine14P01C0069

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7500 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 134 14 26 497 481 481 481 481), lower := (rows 113 134 14 26 16 32 64 128 256), losses := [] }

theorem u7500 : Upper (D 1) (R 1) [112,132,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7500
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7501 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 134 14 56 467 483 451 451 451), lower := (rows 113 134 14 56 16 32 64 128 256), losses := [] }

theorem u7501 : Upper (D 1) (R 1) [112,132,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7501
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7502 : PairBound 9 := { available := 370, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 113 134 14 137 370 370 370 498 370), lower := (rows 113 134 14 137 16 32 64 128 256), losses := [] }

theorem u7502 : Upper (D 1) (R 1) [112,132,10,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7502
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7503 : PairBound 9 := { available := 369, camps := [{ cop := 7, region := 14, targets := 16 }], pairs := [(1,4)], upper := (rows 113 134 14 138 369 369 369 497 369), lower := (rows 113 134 14 138 16 32 64 128 256), losses := [] }

theorem u7503 : Upper (D 1) (R 1) [112,132,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7503
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7504 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 113 134 14 152 371 355 355 483 355), lower := (rows 113 134 14 152 16 32 64 128 256), losses := [] }

theorem u7504 : Upper (D 1) (R 1) [112,132,10,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7504
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7505 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7505 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7505 : Upper (D 1) (R 1) [112,132,10,257] 13 := by
  apply FastRouting.sound _ _ [112,132,10,257] 13 (by decide) (choices 1) [2,32,128] r7505 c7505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4096
  · exact u4097
  · exact u4098

def b7506 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 134 14 266 241 241 241 241 497), lower := (rows 113 134 14 266 16 32 64 128 256), losses := [] }

theorem u7506 : Upper (D 1) (R 1) [112,132,10,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7506
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7507 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7507 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7507 : Upper (D 1) (R 1) [112,132,10,272] 13 := by
  apply FastRouting.sound _ _ [112,132,10,272] 13 (by decide) (choices 1) [1,2,32,128] r7507 c7507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4099
  · exact u4100
  · exact u4101
  · exact u4102

def b7508 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 113 134 14 392 115 115 115 243 371), lower := (rows 113 134 14 392 16 32 64 128 256), losses := [] }

theorem u7508 : Upper (D 1) (R 1) [112,132,10,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7508
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7509 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 497, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 22 11 504 488 488 488 488), lower := (rows 113 134 22 11 16 32 64 128 256), losses := [] }

theorem u7509 : Upper (D 1) (R 1) [112,132,18,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7509
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7510 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 134 22 41 474 490 458 458 458), lower := (rows 113 134 22 41 16 32 64 128 256), losses := [] }

theorem u7510 : Upper (D 1) (R 1) [112,132,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7510
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7511 : PairBound 9 := { available := 457, camps := [{ cop := 3, region := 465, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 22 42 473 489 457 457 457), lower := (rows 113 134 22 42 16 32 64 128 256), losses := [] }

theorem u7511 : Upper (D 1) (R 1) [112,132,18,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7511
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7512 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 134 22 104 411 427 459 395 395), lower := (rows 113 134 22 104 16 32 64 128 256), losses := [] }

theorem u7512 : Upper (D 1) (R 1) [112,132,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7512
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7513 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7513 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | _ => 0)

theorem u7513 : Upper (D 1) (R 1) [112,132,18,129] 13 := by
  apply FastRouting.sound _ _ [112,132,18,129] 13 (by decide) (choices 1) [2,8,32,256] r7513 c7513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4103
  · exact u4104
  · exact u4105
  · exact u4106

def b7514 : PairBound 9 := { available := 361, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 134 22 138 377 361 361 489 361), lower := (rows 113 134 22 138 16 32 64 128 256), losses := [] }

theorem u7514 : Upper (D 1) (R 1) [112,132,18,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7514
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7515 : Route 9 := (fun mask => (mask,id))

def c7515 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u7515 : Upper (D 1) (R 1) [112,132,18,160] 13 := by
  apply FastRouting.sound _ _ [112,132,18,160] 13 (by decide) (choices 1) [1,2,8,64,256] r7515 c7515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4107
  · exact u4108
  · exact u4109
  · exact u4110
  · exact u4111

def r7516 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7516 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7516 : Upper (D 1) (R 1) [112,132,18,257] 13 := by
  apply FastRouting.sound _ _ [112,132,18,257] 13 (by decide) (choices 1) [2,8,32,128] r7516 c7516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4112
  · exact u4113
  · exact u4114
  · exact u4115

def b7517 : PairBound 9 := { available := 233, camps := [{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 22 266 249 233 233 233 489), lower := (rows 113 134 22 266 16 32 64 128 256), losses := [] }

theorem u7517 : Upper (D 1) (R 1) [112,132,18,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7517
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7518 : Route 9 := (fun mask => (mask,id))

def c7518 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7518 : Upper (D 1) (R 1) [112,132,18,288] 13 := by
  apply FastRouting.sound _ _ [112,132,18,288] 13 (by decide) (choices 1) [1,2,8,64,128] r7518 c7518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4116
  · exact u4117
  · exact u4118
  · exact u4119
  · exact u4120

def r7519 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7519 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7519 : Upper (D 1) (R 1) [112,132,18,384] 13 := by
  apply FastRouting.sound _ _ [112,132,18,384] 13 (by decide) (choices 1) [1,2,8,32] r7519 c7519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4121
  · exact u4122
  · exact u4123
  · exact u4124

def b7520 : PairBound 9 := { available := 482, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 113 134 28 11 498 482 482 482 482), lower := (rows 113 134 28 11 16 32 64 128 256), losses := [] }

theorem u7520 : Upper (D 1) (R 1) [112,132,24,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7520
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7521 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 134 28 41 466 482 450 450 450), lower := (rows 113 134 28 41 16 32 64 128 256), losses := [] }

theorem u7521 : Upper (D 1) (R 1) [112,132,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7521
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7522 : Route 9 := (fun mask => (mask,id))

def c7522 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u7522 : Upper (D 1) (R 1) [112,132,24,34] 13 := by
  apply FastRouting.sound _ _ [112,132,24,34] 13 (by decide) (choices 1) [1,2,64,128,256] r7522 c7522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4125
  · exact u4126
  · exact u4127
  · exact u4128
  · exact u4129

def b7523 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 134 28 104 403 419 451 387 387), lower := (rows 113 134 28 104 16 32 64 128 256), losses := [] }

theorem u7523 : Upper (D 1) (R 1) [112,132,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7523
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7524 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 134 28 137 370 354 354 482 354), lower := (rows 113 134 28 137 16 32 64 128 256), losses := [] }

theorem u7524 : Upper (D 1) (R 1) [112,132,24,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7524
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7525 : PairBound 9 := { available := 355, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 134 28 138 371 355 355 483 355), lower := (rows 113 134 28 138 16 32 64 128 256), losses := [] }

theorem u7525 : Upper (D 1) (R 1) [112,132,24,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7525
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7526 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 134 28 168 339 355 323 451 323), lower := (rows 113 134 28 168 16 32 64 128 256), losses := [] }

theorem u7526 : Upper (D 1) (R 1) [112,132,24,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7526
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7527 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 113 134 28 265 242 226 226 226 482), lower := (rows 113 134 28 265 16 32 64 128 256), losses := [] }

theorem u7527 : Upper (D 1) (R 1) [112,132,24,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7527
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7528 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7528 : Upper (D 1) (R 1) [112,132,24,258] 13 := by
  apply FastRouting.sound _ _ [112,132,24,258] 13 (by decide) (choices 1) [1,2,32,128] r7528 c7528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4130
  · exact u4131
  · exact u4132
  · exact u4133

def r7529 : Route 9 := (fun mask => (mask,id))

def c7529 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7529 : Upper (D 1) (R 1) [112,132,24,288] 13 := by
  apply FastRouting.sound _ _ [112,132,24,288] 13 (by decide) (choices 1) [1,2,64,128] r7529 c7529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4134
  · exact u4135
  · exact u4136
  · exact u4137

def b7530 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 134 28 392 115 99 99 227 355), lower := (rows 113 134 28 392 16 32 64 128 256), losses := [] }

theorem u7530 : Upper (D 1) (R 1) [112,132,24,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7530
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7531 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7531 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7531 : Upper (D 1) (R 1) [112,132,257,18] 13 := by
  apply FastRouting.sound _ _ [112,132,257,18] 13 (by decide) (choices 1) [2,8,32,128] r7531 c7531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4138
  · exact u4139
  · exact u4140
  · exact u4141

def b7532 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 134 261 56 218 234 202 202 458), lower := (rows 113 134 261 56 16 32 64 128 256), losses := [] }

theorem u7532 : Upper (D 1) (R 1) [112,132,257,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7532
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7533 : PairBound 9 := { available := 122, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 134 261 138 122 122 122 250 378), lower := (rows 113 134 261 138 16 32 64 128 256), losses := [] }

theorem u7533 : Upper (D 1) (R 1) [112,132,257,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7533
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7534 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7534 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7534 : Upper (D 1) (R 1) [112,132,257,144] 13 := by
  apply FastRouting.sound _ _ [112,132,257,144] 13 (by decide) (choices 1) [2,8,32] r7534 c7534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4142
  · exact u4143
  · exact u4144

def b7535 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 262 11 248 248 248 248 504), lower := (rows 113 134 262 11 16 32 64 128 256), losses := [] }

theorem u7535 : Upper (D 1) (R 1) [112,132,258,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7535
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7536 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 134 262 25 250 234 234 234 490), lower := (rows 113 134 262 25 16 32 64 128 256), losses := [] }

theorem u7536 : Upper (D 1) (R 1) [112,132,258,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7536
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7537 : PairBound 9 := { available := 233, camps := [{ cop := 3, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 262 26 249 233 233 233 489), lower := (rows 113 134 262 26 16 32 64 128 256), losses := [] }

theorem u7537 : Upper (D 1) (R 1) [112,132,258,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7537
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7538 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 134 262 56 219 235 203 203 459), lower := (rows 113 134 262 56 16 32 64 128 256), losses := [] }

theorem u7538 : Upper (D 1) (R 1) [112,132,258,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7538
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7539 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7539 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7539 : Upper (D 1) (R 1) [112,132,258,129] 13 := by
  apply FastRouting.sound _ _ [112,132,258,129] 13 (by decide) (choices 1) [2,8,32] r7539 c7539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4145
  · exact u4146
  · exact u4147

def b7540 : PairBound 9 := { available := 121, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 134 262 138 121 121 121 249 377), lower := (rows 113 134 262 138 16 32 64 128 256), losses := [] }

theorem u7540 : Upper (D 1) (R 1) [112,132,258,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7540
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7541 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7541 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7541 : Upper (D 1) (R 1) [112,132,258,144] 13 := by
  apply FastRouting.sound _ _ [112,132,258,144] 13 (by decide) (choices 1) [1,2,8,32] r7541 c7541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4148
  · exact u4149
  · exact u4150
  · exact u4151

def r7542 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7542 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7542 : Upper (D 1) (R 1) [112,132,264,3] 13 := by
  apply FastRouting.sound _ _ [112,132,264,3] 13 (by decide) (choices 1) [2,32,128] r7542 c7542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4152
  · exact u4153
  · exact u4154

def b7543 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 134 268 25 242 226 226 226 482), lower := (rows 113 134 268 25 16 32 64 128 256), losses := [] }

theorem u7543 : Upper (D 1) (R 1) [112,132,264,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7543
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7544 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7544 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7544 : Upper (D 1) (R 1) [112,132,264,18] 13 := by
  apply FastRouting.sound _ _ [112,132,264,18] 13 (by decide) (choices 1) [1,2,32,128] r7544 c7544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4155
  · exact u4156
  · exact u4157
  · exact u4158

def b7545 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 134 268 56 211 227 195 195 451), lower := (rows 113 134 268 56 16 32 64 128 256), losses := [] }

theorem u7545 : Upper (D 1) (R 1) [112,132,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7545
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7546 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 134 268 137 114 114 114 242 370), lower := (rows 113 134 268 137 16 32 64 128 256), losses := [] }

theorem u7546 : Upper (D 1) (R 1) [112,132,264,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7546
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7547 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 134 268 138 115 115 115 243 371), lower := (rows 113 134 268 138 16 32 64 128 256), losses := [] }

theorem u7547 : Upper (D 1) (R 1) [112,132,264,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7547
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7548 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 134 268 152 115 99 99 227 355), lower := (rows 113 134 268 152 16 32 64 128 256), losses := [] }

theorem u7548 : Upper (D 1) (R 1) [112,132,264,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7548
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7549 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7549 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7549 : Upper (D 1) (R 1) [112,132,272,3] 13 := by
  apply FastRouting.sound _ _ [112,132,272,3] 13 (by decide) (choices 1) [2,8,32,128] r7549 c7549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4159
  · exact u4160
  · exact u4161
  · exact u4162

def b7550 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 134 276 41 218 234 202 202 458), lower := (rows 113 134 276 41 16 32 64 128 256), losses := [] }

theorem u7550 : Upper (D 1) (R 1) [112,132,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7550
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7551 : Route 9 := (fun mask => (mask,id))

def c7551 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7551 : Upper (D 1) (R 1) [112,132,272,34] 13 := by
  apply FastRouting.sound _ _ [112,132,272,34] 13 (by decide) (choices 1) [1,2,8,64,128] r7551 c7551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4163
  · exact u4164
  · exact u4165
  · exact u4166
  · exact u4167

def b7552 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 134 276 104 155 171 203 139 395), lower := (rows 113 134 276 104 16 32 64 128 256), losses := [] }

theorem u7552 : Upper (D 1) (R 1) [112,132,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7552
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7553 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7553 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7553 : Upper (D 1) (R 1) [112,132,272,129] 13 := by
  apply FastRouting.sound _ _ [112,132,272,129] 13 (by decide) (choices 1) [2,8,32] r7553 c7553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4168
  · exact u4169
  · exact u4170

def b7554 : PairBound 9 := { available := 107, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 134 276 138 123 107 107 235 363), lower := (rows 113 134 276 138 16 32 64 128 256), losses := [] }

theorem u7554 : Upper (D 1) (R 1) [112,132,272,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7554
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7555 : Route 9 := (fun mask => (mask,id))

def c7555 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7555 : Upper (D 1) (R 1) [112,132,272,160] 13 := by
  apply FastRouting.sound _ _ [112,132,272,160] 13 (by decide) (choices 1) [1,2,8,64] r7555 c7555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4171
  · exact u4172
  · exact u4173
  · exact u4174

def b7556 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 113 146 7 14 504 488 488 488 488), lower := (rows 113 146 7 14 16 32 64 128 256), losses := [] }

theorem u7556 : Upper (D 1) (R 1) [112,144,3,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7556
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7557 : PairBound 9 := { available := 460, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 146 7 42 476 492 460 460 460), lower := (rows 113 146 7 42 16 32 64 128 256), losses := [] }

theorem u7557 : Upper (D 1) (R 1) [112,144,3,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7557
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7558 : PairBound 9 := { available := 458, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 146 7 44 474 490 458 458 458), lower := (rows 113 146 7 44 16 32 64 128 256), losses := [] }

theorem u7558 : Upper (D 1) (R 1) [112,144,3,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7558
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7559 : PairBound 9 := { available := 362, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 146 7 140 378 362 362 490 362), lower := (rows 113 146 7 140 16 32 64 128 256), losses := [] }

theorem u7559 : Upper (D 1) (R 1) [112,144,3,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7559
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u7559
end Delivery.IrregularNine14.P01
