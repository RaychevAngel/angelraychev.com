import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0000

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b420 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 52 328 208 160 97 161 289), lower := (rows 7 11 52 328 208 160 64 128 256), losses := [] }

theorem u420 : Upper (D 3) (R 3) [6,9,48,320,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b420
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b421 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 152 273 33 224 224 480), lower := (rows 7 11 100 152 273 33 64 128 256), losses := [] }

theorem u421 : Upper (D 3) (R 3) [6,9,96,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b421
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b422 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 152 273 96 225 161 417), lower := (rows 7 11 100 152 273 96 64 128 256), losses := [] }

theorem u422 : Upper (D 3) (R 3) [6,9,96,144,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b422
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m423_1 : Upper (D 3) (R 3) [6,9,96,144,257,128,1] 13 :=
  permutation_upper _ _ _ [6,9,96,144,257,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u30

theorem m423_32 : Upper (D 3) (R 3) [6,9,96,144,257,128,32] 13 :=
  permutation_upper _ _ _ [6,9,96,144,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u31

def r423 : Route 9 := (fun mask => (mask,id))

def c423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u423 : Upper (D 3) (R 3) [6,9,96,144,257,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,257,128] 13 (by decide) (choices 1) [1,32] r423 c423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m423_1
  · exact m423_32

def b424 : PairBound 9 := { available := 193, camps := [], pairs := [(3,5)], upper := (rows 7 11 100 152 304 33 193 193 449), lower := (rows 7 11 100 152 304 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 99 163 291), good := (rows 455 459 452 152 472 449 64 128 256) }] }

theorem u424 : Upper (D 3) (R 3) [6,9,96,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b424
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b425 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 152 304 96 193 129 385), lower := (rows 7 11 100 152 304 96 64 128 256), losses := [] }

theorem u425 : Upper (D 3) (R 3) [6,9,96,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b425
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r426 : Route 9 := (fun mask => (mask,id))

def c426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u426 : Upper (D 3) (R 3) [6,9,96,144,288,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,288,128] 13 (by decide) (choices 1) [1] r426 c426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u32

def b427 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 280 145 33 224 224 480), lower := (rows 7 11 100 280 145 33 64 128 256), losses := [] }

theorem u427 : Upper (D 3) (R 3) [6,9,96,272,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b427
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b428 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 280 145 96 225 161 417), lower := (rows 7 11 100 280 145 96 64 128 256), losses := [] }

theorem u428 : Upper (D 3) (R 3) [6,9,96,272,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b428
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m429_1 : Upper (D 3) (R 3) [6,9,96,272,129,128,1] 13 :=
  permutation_upper _ _ _ [6,9,96,272,129,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33

theorem m429_32 : Upper (D 3) (R 3) [6,9,96,272,129,128,32] 13 :=
  permutation_upper _ _ _ [6,9,96,272,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34

def r429 : Route 9 := (fun mask => (mask,id))

def c429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u429 : Upper (D 3) (R 3) [6,9,96,272,129,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,272,129,128] 13 (by decide) (choices 1) [1,32] r429 c429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m429_1
  · exact m429_32

def b430 : PairBound 9 := { available := 193, camps := [], pairs := [(3,5)], upper := (rows 7 11 100 280 176 33 193 193 449), lower := (rows 7 11 100 280 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 99 163 291), good := (rows 455 459 452 280 472 449 64 128 256) }] }

theorem u430 : Upper (D 3) (R 3) [6,9,96,272,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b430
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b431 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 280 176 96 193 129 385), lower := (rows 7 11 100 280 176 96 64 128 256), losses := [] }

theorem u431 : Upper (D 3) (R 3) [6,9,96,272,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b431
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b432 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 280 176 160 65 193 321), lower := (rows 7 11 100 280 176 160 64 128 256), losses := [] }

theorem u432 : Upper (D 3) (R 3) [6,9,96,272,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b432
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r433 : Route 9 := (fun mask => (mask,id))

def c433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u433 : Upper (D 3) (R 3) [6,9,96,384,160,1] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,160,1] 13 (by decide) (choices 1) [1,16] r433 c433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u35
  · exact u36

def b434 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 7 11 100 392 176 48 65 193 321), lower := (rows 7 11 100 392 176 48 64 128 256), losses := [] }

theorem u434 : Upper (D 3) (R 3) [6,9,96,384,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b434
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b435 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 392 176 96 81 145 273), lower := (rows 7 11 100 392 176 96 64 128 256), losses := [] }

theorem u435 : Upper (D 3) (R 3) [6,9,96,384,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b435
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b436 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 261 56 208 33 224 224 480), lower := (rows 7 11 261 56 208 33 64 128 256), losses := [] }

theorem u436 : Upper (D 3) (R 3) [6,9,257,48,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b436
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b437 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 261 56 208 96 225 161 417), lower := (rows 7 11 261 56 208 96 64 128 256), losses := [] }

theorem u437 : Upper (D 3) (R 3) [6,9,257,48,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b437
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b438 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 261 104 176 33 208 208 464), lower := (rows 7 11 261 104 176 33 64 128 256), losses := [] }

theorem u438 : Upper (D 3) (R 3) [6,9,257,96,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b438
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b439 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 11 261 104 176 48 193 193 449), lower := (rows 7 11 261 104 176 48 64 128 256), losses := [] }

theorem u439 : Upper (D 3) (R 3) [6,9,257,96,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b439
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b440 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 261 104 176 96 209 145 401), lower := (rows 7 11 261 104 176 96 64 128 256), losses := [] }

theorem u440 : Upper (D 3) (R 3) [6,9,257,96,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b440
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b441 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 261 104 176 160 81 209 337), lower := (rows 7 11 261 104 176 160 64 128 256), losses := [] }

theorem u441 : Upper (D 3) (R 3) [6,9,257,96,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b441
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b442 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 276 104 145 33 224 224 480), lower := (rows 7 11 276 104 145 33 64 128 256), losses := [] }

theorem u442 : Upper (D 3) (R 3) [6,9,272,96,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b442
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b443 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 276 104 145 96 225 161 417), lower := (rows 7 11 276 104 145 96 64 128 256), losses := [] }

theorem u443 : Upper (D 3) (R 3) [6,9,272,96,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b443
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m444_1 : Upper (D 3) (R 3) [6,9,272,96,129,128,1] 13 :=
  permutation_upper _ _ _ [6,9,272,96,129,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37

theorem m444_32 : Upper (D 3) (R 3) [6,9,272,96,129,128,32] 13 :=
  permutation_upper _ _ _ [6,9,272,96,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u38

def r444 : Route 9 := (fun mask => (mask,id))

def c444 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u444 : Upper (D 3) (R 3) [6,9,272,96,129,128] 13 := by
  apply FastRouting.sound _ _ [6,9,272,96,129,128] 13 (by decide) (choices 1) [1,32] r444 c444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m444_1
  · exact m444_32

def b445 : PairBound 9 := { available := 193, camps := [], pairs := [(2,5)], upper := (rows 7 11 276 104 176 33 193 193 449), lower := (rows 7 11 276 104 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 8 16 0 99 163 291), good := (rows 455 459 276 456 468 449 64 128 256) }] }

theorem u445 : Upper (D 3) (R 3) [6,9,272,96,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b445
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b446 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 276 104 176 96 193 129 385), lower := (rows 7 11 276 104 176 96 64 128 256), losses := [] }

theorem u446 : Upper (D 3) (R 3) [6,9,272,96,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b446
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b447 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 276 104 176 160 65 193 321), lower := (rows 7 11 276 104 176 160 64 128 256), losses := [] }

theorem u447 : Upper (D 3) (R 3) [6,9,272,96,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b447
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b448 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 88 145 33 224 224 480), lower := (rows 7 11 292 88 145 33 64 128 256), losses := [] }

theorem u448 : Upper (D 3) (R 3) [6,9,288,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b448
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r449 : Route 9 := (fun mask => (mask,id))

def c449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u449 : Upper (D 3) (R 3) [6,9,288,80,129,64] 13 := by
  apply FastRouting.sound _ _ [6,9,288,80,129,64] 13 (by decide) (choices 1) [1,32,128] r449 c449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39
  · exact u40
  · exact u41

def r450 : Route 9 := (fun mask => (mask,id))

def c450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u450 : Upper (D 3) (R 3) [6,9,288,80,129,128] 13 := by
  apply FastRouting.sound _ _ [6,9,288,80,129,128] 13 (by decide) (choices 1) [1,32] r450 c450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u42
  · exact u43

def b451 : PairBound 9 := { available := 193, camps := [], pairs := [(3,5)], upper := (rows 7 11 292 88 176 33 193 193 449), lower := (rows 7 11 292 88 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 99 163 291), good := (rows 455 459 452 88 472 449 64 128 256) }] }

theorem u451 : Upper (D 3) (R 3) [6,9,288,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b451
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r452 : Route 9 := (fun mask => (mask,id))

def c452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u452 : Upper (D 3) (R 3) [6,9,288,80,160,64] 13 := by
  apply FastRouting.sound _ _ [6,9,288,80,160,64] 13 (by decide) (choices 1) [1,128] r452 c452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u44
  · exact u45

def b453 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 292 88 176 160 65 193 321), lower := (rows 7 11 292 88 176 160 64 128 256), losses := [] }

theorem u453 : Upper (D 3) (R 3) [6,9,288,80,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b453
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r454 : Route 9 := (fun mask => (mask,id))

def c454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u454 : Upper (D 3) (R 3) [6,9,288,192,96,1] 13 := by
  apply FastRouting.sound _ _ [6,9,288,192,96,1] 13 (by decide) (choices 1) [1,16,128] r454 c454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u46
  · exact u47
  · exact u48

def b455 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 11 292 200 112 48 193 129 385), lower := (rows 7 11 292 200 112 48 64 128 256), losses := [] }

theorem u455 : Upper (D 3) (R 3) [6,9,288,192,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b455
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b456 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 292 200 112 160 81 145 273), lower := (rows 7 11 292 200 112 160 64 128 256), losses := [] }

theorem u456 : Upper (D 3) (R 3) [6,9,288,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b456
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b457 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 37 73 145 96 480 416 416), lower := (rows 7 26 37 73 145 96 64 128 256), losses := [] }

theorem u457 : Upper (D 3) (R 3) [6,24,33,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b457
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b458 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 7 26 37 73 145 288 224 224 480), lower := (rows 7 26 37 73 145 288 64 128 256), losses := [] }

theorem u458 : Upper (D 3) (R 3) [6,24,33,65,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b458
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b459 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 37 73 273 96 224 160 416), lower := (rows 7 26 37 73 273 96 64 128 256), losses := [] }

theorem u459 : Upper (D 3) (R 3) [6,24,33,65,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b459
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r460 : Route 9 := (fun mask => (mask,id))

def c460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u460 : Upper (D 3) (R 3) [6,24,33,65,257,128] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,257,128] 13 (by decide) (choices 1) [32,128] r460 c460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u49
  · exact u50

def b461 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 73 400 33 224 224 480), lower := (rows 7 26 37 73 400 33 64 128 256), losses := [] }

theorem u461 : Upper (D 3) (R 3) [6,24,33,65,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b461
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b462 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 37 73 400 96 225 161 417), lower := (rows 7 26 37 73 400 96 64 128 256), losses := [] }

theorem u462 : Upper (D 3) (R 3) [6,24,33,65,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b462
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b463 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 7 26 37 73 400 160 97 225 353), lower := (rows 7 26 37 73 400 160 64 128 256), losses := [] }

theorem u463 : Upper (D 3) (R 3) [6,24,33,65,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b463
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b464 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 37 200 273 33 224 224 480), lower := (rows 7 26 37 200 273 33 64 128 256), losses := [] }

theorem u464 : Upper (D 3) (R 3) [6,24,33,192,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b464
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b465 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 37 200 273 96 225 161 417), lower := (rows 7 26 37 200 273 96 64 128 256), losses := [] }

theorem u465 : Upper (D 3) (R 3) [6,24,33,192,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b465
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b466 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 100 137 273 33 224 224 480), lower := (rows 7 26 100 137 273 33 64 128 256), losses := [] }

theorem u466 : Upper (D 3) (R 3) [6,24,96,129,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b466
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b467 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 26 100 137 273 96 225 161 417), lower := (rows 7 26 100 137 273 96 64 128 256), losses := [] }

theorem u467 : Upper (D 3) (R 3) [6,24,96,129,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b467
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m468_1 : Upper (D 3) (R 3) [6,24,96,129,257,128,1] 13 :=
  permutation_upper _ _ _ [6,24,96,129,257,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u51

theorem m468_32 : Upper (D 3) (R 3) [6,24,96,129,257,128,32] 13 :=
  permutation_upper _ _ _ [6,24,96,129,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u52

def r468 : Route 9 := (fun mask => (mask,id))

def c468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u468 : Upper (D 3) (R 3) [6,24,96,129,257,128] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,257,128] 13 (by decide) (choices 1) [1,32] r468 c468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m468_1
  · exact m468_32

def b469 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 42, targets := 128 }], pairs := [(1,7)], upper := (rows 7 26 261 41 81 96 224 160 416), lower := (rows 7 26 261 41 81 96 64 128 256), losses := [] }

theorem u469 : Upper (D 3) (R 3) [6,24,257,33,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b469
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m470_32 : Upper (D 3) (R 3) [6,24,257,33,65,128,32] 13 :=
  permutation_upper _ _ _ [6,24,257,33,65,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u53

def r470 : Route 9 := (fun mask => (mask,id))

def c470 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u470 : Upper (D 3) (R 3) [6,24,257,33,65,128] 13 := by
  apply FastRouting.sound _ _ [6,24,257,33,65,128] 13 (by decide) (choices 1) [32,128] r470 c470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m470_32
  · exact u54

def b471 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 261 41 208 33 224 224 480), lower := (rows 7 26 261 41 208 33 64 128 256), losses := [] }

theorem u471 : Upper (D 3) (R 3) [6,24,257,33,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b471
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b472 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 7 26 261 41 208 96 225 161 417), lower := (rows 7 26 261 41 208 96 64 128 256), losses := [] }

theorem u472 : Upper (D 3) (R 3) [6,24,257,33,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b472
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b473 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 292 73 145 33 224 224 480), lower := (rows 7 26 292 73 145 33 64 128 256), losses := [] }

theorem u473 : Upper (D 3) (R 3) [6,24,288,65,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b473
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r474 : Route 9 := (fun mask => (mask,id))

def c474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u474 : Upper (D 3) (R 3) [6,24,288,65,129,64] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,129,64] 13 (by decide) (choices 1) [1,32,128] r474 c474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u55
  · exact u56
  · exact u57

def b475 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 69 56 208 33 456 392 392), lower := (rows 7 35 69 56 208 33 64 128 256), losses := [] }

theorem u475 : Upper (D 3) (R 3) [6,33,65,48,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b475
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b476 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 7 35 69 56 208 40 449 385 385), lower := (rows 7 35 69 56 208 40 64 128 256), losses := [] }

theorem u476 : Upper (D 3) (R 3) [6,33,65,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b476
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b477 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 69 56 208 160 329 393 265), lower := (rows 7 35 69 56 208 160 64 128 256), losses := [] }

theorem u477 : Upper (D 3) (R 3) [6,33,65,48,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b477
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b478 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 7 35 69 56 208 288 201 137 393), lower := (rows 7 35 69 56 208 288 64 128 256), losses := [] }

theorem u478 : Upper (D 3) (R 3) [6,33,65,48,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b478
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b479 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 69 56 336 33 200 136 392), lower := (rows 7 35 69 56 336 33 64 128 256), losses := [] }

theorem u479 : Upper (D 3) (R 3) [6,33,65,48,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b479
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u479
end Delivery.IrregularNine14.P03
