import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0067
import IrregularNine14P01C0068

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7440 : PairBound 9 := { available := 107, camps := [{ cop := 3, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 388 138 123 107 107 235 363), lower := (rows 113 22 388 138 16 32 64 128 256), losses := [] }

theorem u7440 : Upper (D 1) (R 1) [112,20,384,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7440
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7441 : Route 9 := (fun mask => (mask,id))

def c7441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7441 : Upper (D 1) (R 1) [112,20,384,160] 13 := by
  apply FastRouting.sound _ _ [112,20,384,160] 13 (by decide) (choices 1) [1,2,8,64] r7441 c7441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4039
  · exact u4040
  · exact u4041
  · exact u4042

def b7442 : PairBound 9 := { available := 496, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 113 131 14 14 496 496 496 496 496), lower := (rows 113 131 14 14 16 32 64 128 256), losses := [] }

theorem u7442 : Upper (D 1) (R 1) [112,129,10,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7442
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7443 : PairBound 9 := { available := 484, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 14 26 500 484 484 484 484), lower := (rows 113 131 14 26 16 32 64 128 256), losses := [] }

theorem u7443 : Upper (D 1) (R 1) [112,129,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7443
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7444 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 386, targets := 16 }], pairs := [(1,4)], upper := (rows 113 131 14 28 498 482 482 482 482), lower := (rows 113 131 14 28 16 32 64 128 256), losses := [] }

theorem u7444 : Upper (D 1) (R 1) [112,129,10,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7444
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7445 : PairBound 9 := { available := 454, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 131 14 56 470 486 454 454 454), lower := (rows 113 131 14 56 16 32 64 128 256), losses := [] }

theorem u7445 : Upper (D 1) (R 1) [112,129,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7445
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7446 : PairBound 9 := { available := 372, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 113 131 14 138 372 372 372 500 372), lower := (rows 113 131 14 138 16 32 64 128 256), losses := [] }

theorem u7446 : Upper (D 1) (R 1) [112,129,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7446
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7447 : PairBound 9 := { available := 370, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 113 131 14 140 370 370 370 498 370), lower := (rows 113 131 14 140 16 32 64 128 256), losses := [] }

theorem u7447 : Upper (D 1) (R 1) [112,129,10,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7447
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7448 : PairBound 9 := { available := 358, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 131 14 152 374 358 358 486 358), lower := (rows 113 131 14 152 16 32 64 128 256), losses := [] }

theorem u7448 : Upper (D 1) (R 1) [112,129,10,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7448
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7449 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 131 14 266 244 244 244 244 500), lower := (rows 113 131 14 266 16 32 64 128 256), losses := [] }

theorem u7449 : Upper (D 1) (R 1) [112,129,10,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7449
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7450 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7450 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7450 : Upper (D 1) (R 1) [112,129,10,260] 13 := by
  apply FastRouting.sound _ _ [112,129,10,260] 13 (by decide) (choices 1) [2,32,128] r7450 c7450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4043
  · exact u4044
  · exact u4045

def r7451 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7451 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u7451 : Upper (D 1) (R 1) [112,129,10,272] 13 := by
  apply FastRouting.sound _ _ [112,129,10,272] 13 (by decide) (choices 1) [2,4,32,128] r7451 c7451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4046
  · exact u4047
  · exact u4048
  · exact u4049

def b7452 : PairBound 9 := { available := 118, camps := [{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 131 14 392 118 118 118 246 374), lower := (rows 113 131 14 392 16 32 64 128 256), losses := [] }

theorem u7452 : Upper (D 1) (R 1) [112,129,10,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7452
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7453 : PairBound 9 := { available := 458, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 131 22 44 474 490 458 458 458), lower := (rows 113 131 22 44 16 32 64 128 256), losses := [] }

theorem u7453 : Upper (D 1) (R 1) [112,129,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7453
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7454 : PairBound 9 := { available := 362, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 131 22 140 378 362 362 490 362), lower := (rows 113 131 22 140 16 32 64 128 256), losses := [] }

theorem u7454 : Upper (D 1) (R 1) [112,129,18,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7454
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7455 : PairBound 9 := { available := 334, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 131 22 168 350 366 334 462 334), lower := (rows 113 131 22 168 16 32 64 128 256), losses := [] }

theorem u7455 : Upper (D 1) (R 1) [112,129,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7455
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7456 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 131 22 266 252 236 236 236 492), lower := (rows 113 131 22 266 16 32 64 128 256), losses := [] }

theorem u7456 : Upper (D 1) (R 1) [112,129,18,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7456
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7457 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 131 22 268 250 234 234 234 490), lower := (rows 113 131 22 268 16 32 64 128 256), losses := [] }

theorem u7457 : Upper (D 1) (R 1) [112,129,18,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7457
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7458 : PairBound 9 := { available := 206, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 131 22 296 222 238 206 206 462), lower := (rows 113 131 22 296 16 32 64 128 256), losses := [] }

theorem u7458 : Upper (D 1) (R 1) [112,129,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7458
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7459 : PairBound 9 := { available := 110, camps := [{ cop := 2, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 131 22 392 126 110 110 238 366), lower := (rows 113 131 22 392 16 32 64 128 256), losses := [] }

theorem u7459 : Upper (D 1) (R 1) [112,129,18,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7459
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7460 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 131 28 44 466 482 450 450 450), lower := (rows 113 131 28 44 16 32 64 128 256), losses := [] }

theorem u7460 : Upper (D 1) (R 1) [112,129,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7460
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7461 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 131 28 104 406 422 454 390 390), lower := (rows 113 131 28 104 16 32 64 128 256), losses := [] }

theorem u7461 : Upper (D 1) (R 1) [112,129,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7461
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7462 : PairBound 9 := { available := 358, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 131 28 138 374 358 358 486 358), lower := (rows 113 131 28 138 16 32 64 128 256), losses := [] }

theorem u7462 : Upper (D 1) (R 1) [112,129,24,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7462
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7463 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 386, targets := 16 }], pairs := [(1,4)], upper := (rows 113 131 28 140 370 354 354 482 354), lower := (rows 113 131 28 140 16 32 64 128 256), losses := [] }

theorem u7463 : Upper (D 1) (R 1) [112,129,24,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7463
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7464 : Route 9 := (fun mask => (mask,id))

def c7464 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u7464 : Upper (D 1) (R 1) [112,129,24,160] 13 := by
  apply FastRouting.sound _ _ [112,129,24,160] 13 (by decide) (choices 1) [2,4,64,256] r7464 c7464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4050
  · exact u4051
  · exact u4052
  · exact u4053

def r7465 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7465 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u7465 : Upper (D 1) (R 1) [112,129,24,258] 13 := by
  apply FastRouting.sound _ _ [112,129,24,258] 13 (by decide) (choices 1) [2,4,32,128] r7465 c7465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4054
  · exact u4055
  · exact u4056
  · exact u4057

def b7466 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 130, targets := 16 }], pairs := [(1,4)], upper := (rows 113 131 28 268 242 226 226 226 482), lower := (rows 113 131 28 268 16 32 64 128 256), losses := [] }

theorem u7466 : Upper (D 1) (R 1) [112,129,24,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7466
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7467 : Route 9 := (fun mask => (mask,id))

def c7467 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7467 : Upper (D 1) (R 1) [112,129,24,288] 13 := by
  apply FastRouting.sound _ _ [112,129,24,288] 13 (by decide) (choices 1) [2,4,64,128] r7467 c7467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4058
  · exact u4059
  · exact u4060
  · exact u4061

def r7468 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7468 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7468 : Upper (D 1) (R 1) [112,129,24,384] 13 := by
  apply FastRouting.sound _ _ [112,129,24,384] 13 (by decide) (choices 1) [2,4,32] r7468 c7468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4062
  · exact u4063
  · exact u4064

def b7469 : PairBound 9 := { available := 330, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 131 52 140 346 362 330 458 330), lower := (rows 113 131 52 140 16 32 64 128 256), losses := [] }

theorem u7469 : Upper (D 1) (R 1) [112,129,48,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7469
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7470 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 131 52 200 286 302 334 398 270), lower := (rows 113 131 52 200 16 32 64 128 256), losses := [] }

theorem u7470 : Upper (D 1) (R 1) [112,129,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7470
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7471 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 131 52 266 222 238 206 206 462), lower := (rows 113 131 52 266 16 32 64 128 256), losses := [] }

theorem u7471 : Upper (D 1) (R 1) [112,129,48,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7471
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7472 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 131 52 268 218 234 202 202 458), lower := (rows 113 131 52 268 16 32 64 128 256), losses := [] }

theorem u7472 : Upper (D 1) (R 1) [112,129,48,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7472
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7473 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 131 52 328 158 174 206 142 398), lower := (rows 113 131 52 328 16 32 64 128 256), losses := [] }

theorem u7473 : Upper (D 1) (R 1) [112,129,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7473
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7474 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 131 52 392 94 110 78 206 334), lower := (rows 113 131 52 392 16 32 64 128 256), losses := [] }

theorem u7474 : Upper (D 1) (R 1) [112,129,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7474
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7475 : PairBound 9 := { available := 124, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 131 134 266 124 124 124 252 380), lower := (rows 113 131 134 266 16 32 64 128 256), losses := [] }

theorem u7475 : Upper (D 1) (R 1) [112,129,130,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7475
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7476 : PairBound 9 := { available := 122, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 131 134 268 122 122 122 250 378), lower := (rows 113 131 134 268 16 32 64 128 256), losses := [] }

theorem u7476 : Upper (D 1) (R 1) [112,129,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7476
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7477 : PairBound 9 := { available := 110, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 131 134 280 126 110 110 238 366), lower := (rows 113 131 134 280 16 32 64 128 256), losses := [] }

theorem u7477 : Upper (D 1) (R 1) [112,129,130,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7477
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7478 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7478 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7478 : Upper (D 1) (R 1) [112,129,136,258] 13 := by
  apply FastRouting.sound _ _ [112,129,136,258] 13 (by decide) (choices 1) [2,4,32] r7478 c7478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4065
  · exact u4066
  · exact u4067

def b7479 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 131 140 268 114 114 114 242 370), lower := (rows 113 131 140 268 16 32 64 128 256), losses := [] }

theorem u7479 : Upper (D 1) (R 1) [112,129,136,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7479
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7480 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7480 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7480 : Upper (D 1) (R 1) [112,129,136,272] 13 := by
  apply FastRouting.sound _ _ [112,129,136,272] 13 (by decide) (choices 1) [2,4,32] r7480 c7480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4068
  · exact u4069
  · exact u4070

def r7481 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7481 : Nat → Fin 9 := (fun mask => match mask with | 128 => 7 | 256 => 8 | _ => 0)

theorem u7481 : Upper (D 1) (R 1) [112,129,144,258] 13 := by
  apply FastRouting.sound _ _ [112,129,144,258] 13 (by decide) (choices 1) [2,4,8,32] r7481 c7481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4071
  · exact u4072
  · exact u4073
  · exact u4074

def r7482 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7482 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7482 : Upper (D 1) (R 1) [112,129,144,260] 13 := by
  apply FastRouting.sound _ _ [112,129,144,260] 13 (by decide) (choices 1) [2,8,32] r7482 c7482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4075
  · exact u4076
  · exact u4077

def r7483 : Route 9 := (fun mask => (mask,id))

def c7483 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7483 : Upper (D 1) (R 1) [112,129,144,288] 13 := by
  apply FastRouting.sound _ _ [112,129,144,288] 13 (by decide) (choices 1) [2,4,8,64] r7483 c7483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4078
  · exact u4079
  · exact u4080
  · exact u4081

def b7484 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 7 26 504 488 488 488 488), lower := (rows 113 134 7 26 16 32 64 128 256), losses := [] }

theorem u7484 : Upper (D 1) (R 1) [112,132,3,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7484
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7485 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 134 7 56 474 490 458 458 458), lower := (rows 113 134 7 56 16 32 64 128 256), losses := [] }

theorem u7485 : Upper (D 1) (R 1) [112,132,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7485
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7486 : PairBound 9 := { available := 376, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 134 7 138 376 376 376 504 376), lower := (rows 113 134 7 138 16 32 64 128 256), losses := [] }

theorem u7486 : Upper (D 1) (R 1) [112,132,3,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7486
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7487 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7487 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | _ => 0)

theorem u7487 : Upper (D 1) (R 1) [112,132,3,144] 13 := by
  apply FastRouting.sound _ _ [112,132,3,144] 13 (by decide) (choices 1) [2,8,32,256] r7487 c7487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4082
  · exact u4083
  · exact u4084
  · exact u4085

def b7488 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 7 266 248 248 248 248 504), lower := (rows 113 134 7 266 16 32 64 128 256), losses := [] }

theorem u7488 : Upper (D 1) (R 1) [112,132,3,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7488
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7489 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7489 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7489 : Upper (D 1) (R 1) [112,132,3,272] 13 := by
  apply FastRouting.sound _ _ [112,132,3,272] 13 (by decide) (choices 1) [2,8,32,128] r7489 c7489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4086
  · exact u4087
  · exact u4088
  · exact u4089

def r7490 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7490 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7490 : Upper (D 1) (R 1) [112,132,3,384] 13 := by
  apply FastRouting.sound _ _ [112,132,3,384] 13 (by decide) (choices 1) [2,8,32] r7490 c7490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4090
  · exact u4091
  · exact u4092

def b7491 : PairBound 9 := { available := 482, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 113 134 13 26 498 482 482 482 482), lower := (rows 113 134 13 26 16 32 64 128 256), losses := [] }

theorem u7491 : Upper (D 1) (R 1) [112,132,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7491
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7492 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 134 13 56 466 482 450 450 450), lower := (rows 113 134 13 56 16 32 64 128 256), losses := [] }

theorem u7492 : Upper (D 1) (R 1) [112,132,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7492
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7493 : PairBound 9 := { available := 370, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 134 13 138 370 370 370 498 370), lower := (rows 113 134 13 138 16 32 64 128 256), losses := [] }

theorem u7493 : Upper (D 1) (R 1) [112,132,9,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7493
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7494 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 134 13 152 370 354 354 482 354), lower := (rows 113 134 13 152 16 32 64 128 256), losses := [] }

theorem u7494 : Upper (D 1) (R 1) [112,132,9,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7494
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7495 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7495 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7495 : Upper (D 1) (R 1) [112,132,9,258] 13 := by
  apply FastRouting.sound _ _ [112,132,9,258] 13 (by decide) (choices 1) [2,32,128] r7495 c7495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4093
  · exact u4094
  · exact u4095

def b7496 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 113 134 13 280 242 226 226 226 482), lower := (rows 113 134 13 280 16 32 64 128 256), losses := [] }

theorem u7496 : Upper (D 1) (R 1) [112,132,9,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7496
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7497 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 134 13 392 114 114 114 242 370), lower := (rows 113 134 13 392 16 32 64 128 256), losses := [] }

theorem u7497 : Upper (D 1) (R 1) [112,132,9,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7497
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7498 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 134 14 11 496 496 496 496 496), lower := (rows 113 134 14 11 16 32 64 128 256), losses := [] }

theorem u7498 : Upper (D 1) (R 1) [112,132,10,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7498
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7499 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 134 14 25 498 482 482 482 482), lower := (rows 113 134 14 25 16 32 64 128 256), losses := [] }

theorem u7499 : Upper (D 1) (R 1) [112,132,10,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7499
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u7499
end Delivery.IrregularNine14.P01
