import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0255
import IrregularNine14P06C0256
import IrregularNine14P06C0257

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32700 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 131 38 28 21 352 352 480 352), lower := (rows 11 131 38 28 21 32 64 128 256), losses := [] }

theorem u32700 : Upper (D 6) (R 6) [10,129,34,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32701 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 131 38 28 49 356 324 452 324), lower := (rows 11 131 38 28 49 32 64 128 256), losses := [] }

theorem u32701 : Upper (D 6) (R 6) [10,129,34,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32702 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 24, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 28 52 353 321 449 321), lower := (rows 11 131 38 28 52 32 64 128 256), losses := [] }

theorem u32702 : Upper (D 6) (R 6) [10,129,34,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32703 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0),(4,1)], upper := (rows 11 131 38 28 81 356 356 484 356), lower := (rows 11 131 38 28 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 63 95 159 287), good := (rows 494 486 486 508 508 32 64 128 256) },{ target := 1, region := (rows 1 0 4 8 17 44 76 140 268), good := (rows 505 145 484 508 81 32 64 128 256) }] }

theorem u32703 : Upper (D 6) (R 6) [10,129,34,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32704 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 131 38 28 84 353 353 481 353), lower := (rows 11 131 38 28 84 32 64 128 256), losses := [] }

theorem u32704 : Upper (D 6) (R 6) [10,129,34,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32704 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32705 : Route 9 := (fun mask => (mask,id))

def c32705 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32705 : Upper (D 6) (R 6) [10,129,34,20,96] 13 := by
  apply FastRouting.sound _ _ [10,129,34,20,96] 13 (by decide) (choices 1) [1,4,64,256] r32705 c32705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15344
  · exact u15345
  · exact u15346
  · exact u15347

def b32706 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 100, targets := 1 }], pairs := [(2,0),(3,0),(4,1)], upper := (rows 11 131 38 28 273 100 100 228 356), lower := (rows 11 131 38 28 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 63 95 159 287), good := (rows 494 486 486 508 508 32 64 128 256) },{ target := 1, region := (rows 1 0 4 8 17 44 76 140 268), good := (rows 505 145 484 508 273 32 64 128 256) }] }

theorem u32706 : Upper (D 6) (R 6) [10,129,34,20,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32707 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 131 38 28 276 97 97 225 353), lower := (rows 11 131 38 28 276 32 64 128 256), losses := [] }

theorem u32707 : Upper (D 6) (R 6) [10,129,34,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32708 : Route 9 := (fun mask => (mask,id))

def c32708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32708 : Upper (D 6) (R 6) [10,129,34,20,288] 13 := by
  apply FastRouting.sound _ _ [10,129,34,20,288] 13 (by decide) (choices 1) [1,4,64] r32708 c32708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15348
  · exact u15349
  · exact u15350

def r32709 : Route 9 := (fun mask => (mask,id))

def c32709 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32709 : Upper (D 6) (R 6) [10,129,34,20,320] 13 := by
  apply FastRouting.sound _ _ [10,129,34,20,320] 13 (by decide) (choices 1) [1,4,64] r32709 c32709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15351
  · exact u15352
  · exact u15353

def b32710 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 131 38 56 21 356 324 452 324), lower := (rows 11 131 38 56 21 32 64 128 256), losses := [] }

theorem u32710 : Upper (D 6) (R 6) [10,129,34,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32711 : Route 9 := (fun mask => (mask,id))

def c32711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32711 : Upper (D 6) (R 6) [10,129,34,48,65] 13 := by
  apply FastRouting.sound _ _ [10,129,34,48,65] 13 (by decide) (choices 1) [4,64,256] r32711 c32711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15354
  · exact u15355
  · exact u15356

def r32712 : Route 9 := (fun mask => (mask,id))

def c32712 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32712 : Upper (D 6) (R 6) [10,129,34,48,68] 13 := by
  apply FastRouting.sound _ _ [10,129,34,48,68] 13 (by decide) (choices 1) [1,4,64,256] r32712 c32712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15357
  · exact u15358
  · exact u15359
  · exact u15360

def r32713 : Route 9 := (fun mask => (mask,id))

def c32713 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32713 : Upper (D 6) (R 6) [10,129,34,48,257] 13 := by
  apply FastRouting.sound _ _ [10,129,34,48,257] 13 (by decide) (choices 1) [4,64] r32713 c32713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15361
  · exact u15362

def r32714 : Route 9 := (fun mask => (mask,id))

def c32714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32714 : Upper (D 6) (R 6) [10,129,34,48,260] 13 := by
  apply FastRouting.sound _ _ [10,129,34,48,260] 13 (by decide) (choices 1) [1,4,64] r32714 c32714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15363
  · exact u15364
  · exact u15365

def r32715 : Route 9 := (fun mask => (mask,id))

def c32715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32715 : Upper (D 6) (R 6) [10,129,34,48,320] 13 := by
  apply FastRouting.sound _ _ [10,129,34,48,320] 13 (by decide) (choices 1) [1,4,64] r32715 c32715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15366
  · exact u15367
  · exact u15368

def b32716 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 4, region := 482, targets := 4 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 131 38 76 21 368 368 496 368), lower := (rows 11 131 38 76 21 32 64 128 256), losses := [] }

theorem u32716 : Upper (D 6) (R 6) [10,129,34,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32716 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32717 : Route 9 := (fun mask => (mask,id))

def c32717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u32717 : Upper (D 6) (R 6) [10,129,34,68,33] 13 := by
  apply FastRouting.sound _ _ [10,129,34,68,33] 13 (by decide) (choices 1) [4,16,64,256] r32717 c32717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15369
  · exact u15370
  · exact u15371
  · exact u15372

def b32718 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 38 76 52 369 337 465 337), lower := (rows 11 131 38 76 52 32 64 128 256), losses := [] }

theorem u32718 : Upper (D 6) (R 6) [10,129,34,68,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32719 : Route 9 := (fun mask => (mask,id))

def c32719 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32719 : Upper (D 6) (R 6) [10,129,34,68,65] 13 := by
  apply FastRouting.sound _ _ [10,129,34,68,65] 13 (by decide) (choices 1) [4,16,256] r32719 c32719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15373
  · exact u15374
  · exact u15375

def b32720 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 131 38 76 84 305 369 433 305), lower := (rows 11 131 38 76 84 32 64 128 256), losses := [] }

theorem u32720 : Upper (D 6) (R 6) [10,129,34,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32721 : Route 9 := (fun mask => (mask,id))

def c32721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32721 : Upper (D 6) (R 6) [10,129,34,68,96] 13 := by
  apply FastRouting.sound _ _ [10,129,34,68,96] 13 (by decide) (choices 1) [1,4,16,256] r32721 c32721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15376
  · exact u15377
  · exact u15378
  · exact u15379

def r32722 : Route 9 := (fun mask => (mask,id))

def c32722 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32722 : Upper (D 6) (R 6) [10,129,34,68,257] 13 := by
  apply FastRouting.sound _ _ [10,129,34,68,257] 13 (by decide) (choices 1) [4,16,64] r32722 c32722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15380
  · exact u15381
  · exact u15382

def r32723 : Route 9 := (fun mask => (mask,id))

def c32723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32723 : Upper (D 6) (R 6) [10,129,34,68,260] 13 := by
  apply FastRouting.sound _ _ [10,129,34,68,260] 13 (by decide) (choices 1) [1,16,64] r32723 c32723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15383
  · exact u15384
  · exact u15385

def r32724 : Route 9 := (fun mask => (mask,id))

def c32724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32724 : Upper (D 6) (R 6) [10,129,34,68,288] 13 := by
  apply FastRouting.sound _ _ [10,129,34,68,288] 13 (by decide) (choices 1) [1,4,16,64] r32724 c32724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15386
  · exact u15387
  · exact u15388
  · exact u15389

def r32725 : Route 9 := (fun mask => (mask,id))

def c32725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32725 : Upper (D 6) (R 6) [10,129,34,68,320] 13 := by
  apply FastRouting.sound _ _ [10,129,34,68,320] 13 (by decide) (choices 1) [1,4,16] r32725 c32725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15390
  · exact u15391
  · exact u15392

def b32726 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 38 88 21 356 356 484 356), lower := (rows 11 131 38 88 21 32 64 128 256), losses := [] }

theorem u32726 : Upper (D 6) (R 6) [10,129,34,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32727 : Route 9 := (fun mask => (mask,id))

def c32727 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32727 : Upper (D 6) (R 6) [10,129,34,80,33] 13 := by
  apply FastRouting.sound _ _ [10,129,34,80,33] 13 (by decide) (choices 1) [4,64,256] r32727 c32727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15393
  · exact u15394
  · exact u15395

def b32728 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 38 88 52 357 325 453 325), lower := (rows 11 131 38 88 52 32 64 128 256), losses := [] }

theorem u32728 : Upper (D 6) (R 6) [10,129,34,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32729 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 38 88 81 292 356 420 292), lower := (rows 11 131 38 88 81 32 64 128 256), losses := [] }

theorem u32729 : Upper (D 6) (R 6) [10,129,34,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32730 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 38 88 84 293 357 421 293), lower := (rows 11 131 38 88 84 32 64 128 256), losses := [] }

theorem u32730 : Upper (D 6) (R 6) [10,129,34,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32731 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 38 88 112 293 325 389 261), lower := (rows 11 131 38 88 112 32 64 128 256), losses := [] }

theorem u32731 : Upper (D 6) (R 6) [10,129,34,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32732 : Route 9 := (fun mask => (mask,id))

def c32732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32732 : Upper (D 6) (R 6) [10,129,34,80,257] 13 := by
  apply FastRouting.sound _ _ [10,129,34,80,257] 13 (by decide) (choices 1) [4,64] r32732 c32732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15396
  · exact u15397

def r32733 : Route 9 := (fun mask => (mask,id))

def c32733 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32733 : Upper (D 6) (R 6) [10,129,34,80,260] 13 := by
  apply FastRouting.sound _ _ [10,129,34,80,260] 13 (by decide) (choices 1) [1,4,64] r32733 c32733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15398
  · exact u15399
  · exact u15400

def r32734 : Route 9 := (fun mask => (mask,id))

def c32734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32734 : Upper (D 6) (R 6) [10,129,34,80,288] 13 := by
  apply FastRouting.sound _ _ [10,129,34,80,288] 13 (by decide) (choices 1) [1,4,64] r32734 c32734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15401
  · exact u15402
  · exact u15403

def b32735 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 38 88 336 37 101 165 293), lower := (rows 11 131 38 88 336 32 64 128 256), losses := [] }

theorem u32735 : Upper (D 6) (R 6) [10,129,34,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32736 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(3,0),(3,1)], upper := (rows 11 131 38 104 21 372 340 468 340), lower := (rows 11 131 38 104 21 32 64 128 256), losses := [] }

theorem u32736 : Upper (D 6) (R 6) [10,129,34,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32737 : Route 9 := (fun mask => (mask,id))

def c32737 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32737 : Upper (D 6) (R 6) [10,129,34,96,65] 13 := by
  apply FastRouting.sound _ _ [10,129,34,96,65] 13 (by decide) (choices 1) [4,16,256] r32737 c32737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15404
  · exact u15405
  · exact u15406

def r32738 : Route 9 := (fun mask => (mask,id))

def c32738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32738 : Upper (D 6) (R 6) [10,129,34,96,68] 13 := by
  apply FastRouting.sound _ _ [10,129,34,96,68] 13 (by decide) (choices 1) [1,4,16,256] r32738 c32738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15407
  · exact u15408
  · exact u15409
  · exact u15410

def r32739 : Route 9 := (fun mask => (mask,id))

def c32739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32739 : Upper (D 6) (R 6) [10,129,34,96,257] 13 := by
  apply FastRouting.sound _ _ [10,129,34,96,257] 13 (by decide) (choices 1) [4,16,64] r32739 c32739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15411
  · exact u15412
  · exact u15413

def r32740 : Route 9 := (fun mask => (mask,id))

def c32740 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32740 : Upper (D 6) (R 6) [10,129,34,96,260] 13 := by
  apply FastRouting.sound _ _ [10,129,34,96,260] 13 (by decide) (choices 1) [1,4,16,64] r32740 c32740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15414
  · exact u15415
  · exact u15416
  · exact u15417

def r32741 : Route 9 := (fun mask => (mask,id))

def c32741 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32741 : Upper (D 6) (R 6) [10,129,34,96,320] 13 := by
  apply FastRouting.sound _ _ [10,129,34,96,320] 13 (by decide) (choices 1) [1,4,16] r32741 c32741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15418
  · exact u15419
  · exact u15420

def b32742 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 131 38 268 21 112 112 240 368), lower := (rows 11 131 38 268 21 32 64 128 256), losses := [] }

theorem u32742 : Upper (D 6) (R 6) [10,129,34,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32742 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32743 : Route 9 := (fun mask => (mask,id))

def c32743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32743 : Upper (D 6) (R 6) [10,129,34,260,33] 13 := by
  apply FastRouting.sound _ _ [10,129,34,260,33] 13 (by decide) (choices 1) [4,16,64] r32743 c32743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15421
  · exact u15422
  · exact u15423

def b32744 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 38 268 52 113 81 209 337), lower := (rows 11 131 38 268 52 32 64 128 256), losses := [] }

theorem u32744 : Upper (D 6) (R 6) [10,129,34,260,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32745 : Route 9 := (fun mask => (mask,id))

def c32745 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32745 : Upper (D 6) (R 6) [10,129,34,260,65] 13 := by
  apply FastRouting.sound _ _ [10,129,34,260,65] 13 (by decide) (choices 1) [4,16,64] r32745 c32745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15424
  · exact u15425
  · exact u15426

def r32746 : Route 9 := (fun mask => (mask,id))

def c32746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32746 : Upper (D 6) (R 6) [10,129,34,260,68] 13 := by
  apply FastRouting.sound _ _ [10,129,34,260,68] 13 (by decide) (choices 1) [1,16,64] r32746 c32746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15427
  · exact u15428
  · exact u15429

def r32747 : Route 9 := (fun mask => (mask,id))

def c32747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32747 : Upper (D 6) (R 6) [10,129,34,260,96] 13 := by
  apply FastRouting.sound _ _ [10,129,34,260,96] 13 (by decide) (choices 1) [1,4,16,64] r32747 c32747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15430
  · exact u15431
  · exact u15432
  · exact u15433

def b32748 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 0, region := 100, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 38 280 21 100 100 228 356), lower := (rows 11 131 38 280 21 32 64 128 256), losses := [] }

theorem u32748 : Upper (D 6) (R 6) [10,129,34,272,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32749 : Route 9 := (fun mask => (mask,id))

def c32749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32749 : Upper (D 6) (R 6) [10,129,34,272,33] 13 := by
  apply FastRouting.sound _ _ [10,129,34,272,33] 13 (by decide) (choices 1) [4,64] r32749 c32749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15434
  · exact u15435

def b32750 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 38 280 52 101 69 197 325), lower := (rows 11 131 38 280 52 32 64 128 256), losses := [] }

theorem u32750 : Upper (D 6) (R 6) [10,129,34,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32751 : Route 9 := (fun mask => (mask,id))

def c32751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32751 : Upper (D 6) (R 6) [10,129,34,272,65] 13 := by
  apply FastRouting.sound _ _ [10,129,34,272,65] 13 (by decide) (choices 1) [4,64] r32751 c32751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15436
  · exact u15437

def r32752 : Route 9 := (fun mask => (mask,id))

def c32752 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32752 : Upper (D 6) (R 6) [10,129,34,272,68] 13 := by
  apply FastRouting.sound _ _ [10,129,34,272,68] 13 (by decide) (choices 1) [1,4,64] r32752 c32752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15438
  · exact u15439
  · exact u15440

def r32753 : Route 9 := (fun mask => (mask,id))

def c32753 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32753 : Upper (D 6) (R 6) [10,129,34,272,96] 13 := by
  apply FastRouting.sound _ _ [10,129,34,272,96] 13 (by decide) (choices 1) [1,4,64] r32753 c32753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15441
  · exact u15442
  · exact u15443

def b32754 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(3,0),(3,1)], upper := (rows 11 131 38 296 21 116 84 212 340), lower := (rows 11 131 38 296 21 32 64 128 256), losses := [] }

theorem u32754 : Upper (D 6) (R 6) [10,129,34,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32755 : Route 9 := (fun mask => (mask,id))

def c32755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32755 : Upper (D 6) (R 6) [10,129,34,288,65] 13 := by
  apply FastRouting.sound _ _ [10,129,34,288,65] 13 (by decide) (choices 1) [4,16,64] r32755 c32755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15444
  · exact u15445
  · exact u15446

def r32756 : Route 9 := (fun mask => (mask,id))

def c32756 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32756 : Upper (D 6) (R 6) [10,129,34,288,68] 13 := by
  apply FastRouting.sound _ _ [10,129,34,288,68] 13 (by decide) (choices 1) [1,4,16,64] r32756 c32756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15447
  · exact u15448
  · exact u15449
  · exact u15450

def r32757 : Route 9 := (fun mask => (mask,id))

def c32757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32757 : Upper (D 6) (R 6) [10,129,34,320,5] 13 := by
  apply FastRouting.sound _ _ [10,129,34,320,5] 13 (by decide) (choices 1) [4,16,64] r32757 c32757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15451
  · exact u15452
  · exact u15453

def r32758 : Route 9 := (fun mask => (mask,id))

def c32758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32758 : Upper (D 6) (R 6) [10,129,34,320,33] 13 := by
  apply FastRouting.sound _ _ [10,129,34,320,33] 13 (by decide) (choices 1) [4,16,64] r32758 c32758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15454
  · exact u15455
  · exact u15456

def b32759 : PairBound 9 := { available := 85, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 38 328 52 117 85 213 341), lower := (rows 11 131 38 328 52 32 64 128 256), losses := [] }

theorem u32759 : Upper (D 6) (R 6) [10,129,34,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u32759
end Delivery.IrregularNine14.P06
