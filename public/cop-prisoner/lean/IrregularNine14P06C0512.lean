import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0207
import IrregularNine14P06C0208
import IrregularNine14P06C0209

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30720 : Route 9 := (fun mask => (mask,id))

def c30720 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30720 : Upper (D 6) (R 6) [10,33,129,80,36] 13 := by
  apply FastRouting.sound _ _ [10,33,129,80,36] 13 (by decide) (choices 1) [2,4,64,256] r30720 c30720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12457
  · exact u12458
  · exact u12459
  · exact u12460

def b30721 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 133 88 82 292 356 420 292), lower := (rows 11 35 133 88 82 32 64 128 256), losses := [] }

theorem u30721 : Upper (D 6) (R 6) [10,33,129,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30722 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 35 133 88 84 294 358 422 294), lower := (rows 11 35 133 88 84 32 64 128 256), losses := [] }

theorem u30722 : Upper (D 6) (R 6) [10,33,129,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30723 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 133 88 112 294 326 390 262), lower := (rows 11 35 133 88 112 32 64 128 256), losses := [] }

theorem u30723 : Upper (D 6) (R 6) [10,33,129,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30724 : Route 9 := (fun mask => (mask,id))

def c30724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30724 : Upper (D 6) (R 6) [10,33,129,80,258] 13 := by
  apply FastRouting.sound _ _ [10,33,129,80,258] 13 (by decide) (choices 1) [4,64] r30724 c30724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12461
  · exact u12462

def r30725 : Route 9 := (fun mask => (mask,id))

def c30725 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30725 : Upper (D 6) (R 6) [10,33,129,80,260] 13 := by
  apply FastRouting.sound _ _ [10,33,129,80,260] 13 (by decide) (choices 1) [2,4,64] r30725 c30725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12463
  · exact u12464
  · exact u12465

def r30726 : Route 9 := (fun mask => (mask,id))

def c30726 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30726 : Upper (D 6) (R 6) [10,33,129,80,288] 13 := by
  apply FastRouting.sound _ _ [10,33,129,80,288] 13 (by decide) (choices 1) [2,4,64] r30726 c30726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12466
  · exact u12467
  · exact u12468

def b30727 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 35 133 88 336 38 102 166 294), lower := (rows 11 35 133 88 336 32 64 128 256), losses := [] }

theorem u30727 : Upper (D 6) (R 6) [10,33,129,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30728 : Route 9 := (fun mask => (mask,id))

def c30728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30728 : Upper (D 6) (R 6) [10,33,129,260,6] 13 := by
  apply FastRouting.sound _ _ [10,33,129,260,6] 13 (by decide) (choices 1) [16,64] r30728 c30728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12469
  · exact u12470

def b30729 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 133 268 50 116 84 212 340), lower := (rows 11 35 133 268 50 32 64 128 256), losses := [] }

theorem u30729 : Upper (D 6) (R 6) [10,33,129,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30730 : Route 9 := (fun mask => (mask,id))

def c30730 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30730 : Upper (D 6) (R 6) [10,33,129,260,36] 13 := by
  apply FastRouting.sound _ _ [10,33,129,260,36] 13 (by decide) (choices 1) [2,16,64] r30730 c30730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12471
  · exact u12472
  · exact u12473

def r30731 : Route 9 := (fun mask => (mask,id))

def c30731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30731 : Upper (D 6) (R 6) [10,33,129,260,66] 13 := by
  apply FastRouting.sound _ _ [10,33,129,260,66] 13 (by decide) (choices 1) [4,16,64] r30731 c30731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12474
  · exact u12475
  · exact u12476

def r30732 : Route 9 := (fun mask => (mask,id))

def c30732 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30732 : Upper (D 6) (R 6) [10,33,129,260,68] 13 := by
  apply FastRouting.sound _ _ [10,33,129,260,68] 13 (by decide) (choices 1) [2,16,64] r30732 c30732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12477
  · exact u12478
  · exact u12479

def r30733 : Route 9 := (fun mask => (mask,id))

def c30733 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30733 : Upper (D 6) (R 6) [10,33,129,260,96] 13 := by
  apply FastRouting.sound _ _ [10,33,129,260,96] 13 (by decide) (choices 1) [2,4,16,64] r30733 c30733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12480
  · exact u12481
  · exact u12482
  · exact u12483

def b30734 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 35 133 280 22 100 100 228 356), lower := (rows 11 35 133 280 22 32 64 128 256), losses := [] }

theorem u30734 : Upper (D 6) (R 6) [10,33,129,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30735 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 133 280 50 100 68 196 324), lower := (rows 11 35 133 280 50 32 64 128 256), losses := [] }

theorem u30735 : Upper (D 6) (R 6) [10,33,129,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30736 : Route 9 := (fun mask => (mask,id))

def c30736 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30736 : Upper (D 6) (R 6) [10,33,129,272,36] 13 := by
  apply FastRouting.sound _ _ [10,33,129,272,36] 13 (by decide) (choices 1) [2,4,64] r30736 c30736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12484
  · exact u12485
  · exact u12486

def r30737 : Route 9 := (fun mask => (mask,id))

def c30737 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30737 : Upper (D 6) (R 6) [10,33,129,272,66] 13 := by
  apply FastRouting.sound _ _ [10,33,129,272,66] 13 (by decide) (choices 1) [4,64] r30737 c30737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12487
  · exact u12488

def r30738 : Route 9 := (fun mask => (mask,id))

def c30738 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30738 : Upper (D 6) (R 6) [10,33,129,272,68] 13 := by
  apply FastRouting.sound _ _ [10,33,129,272,68] 13 (by decide) (choices 1) [2,4,64] r30738 c30738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12489
  · exact u12490
  · exact u12491

def r30739 : Route 9 := (fun mask => (mask,id))

def c30739 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30739 : Upper (D 6) (R 6) [10,33,129,272,96] 13 := by
  apply FastRouting.sound _ _ [10,33,129,272,96] 13 (by decide) (choices 1) [2,4,64] r30739 c30739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12492
  · exact u12493
  · exact u12494

def r30740 : Route 9 := (fun mask => (mask,id))

def c30740 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30740 : Upper (D 6) (R 6) [10,33,129,320,6] 13 := by
  apply FastRouting.sound _ _ [10,33,129,320,6] 13 (by decide) (choices 1) [4,16,64] r30740 c30740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12495
  · exact u12496
  · exact u12497

def b30741 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 35 133 328 50 116 84 212 340), lower := (rows 11 35 133 328 50 32 64 128 256), losses := [] }

theorem u30741 : Upper (D 6) (R 6) [10,33,129,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30742 : Route 9 := (fun mask => (mask,id))

def c30742 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30742 : Upper (D 6) (R 6) [10,33,129,320,36] 13 := by
  apply FastRouting.sound _ _ [10,33,129,320,36] 13 (by decide) (choices 1) [2,4,16,64] r30742 c30742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12498
  · exact u12499
  · exact u12500
  · exact u12501

def r30743 : Route 9 := (fun mask => (mask,id))

def c30743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30743 : Upper (D 6) (R 6) [10,33,129,320,66] 13 := by
  apply FastRouting.sound _ _ [10,33,129,320,66] 13 (by decide) (choices 1) [4,16] r30743 c30743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12502
  · exact u12503

def r30744 : Route 9 := (fun mask => (mask,id))

def c30744 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30744 : Upper (D 6) (R 6) [10,33,129,320,68] 13 := by
  apply FastRouting.sound _ _ [10,33,129,320,68] 13 (by decide) (choices 1) [2,4,16] r30744 c30744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12504
  · exact u12505
  · exact u12506

def r30745 : Route 9 := (fun mask => (mask,id))

def c30745 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30745 : Upper (D 6) (R 6) [10,33,129,320,96] 13 := by
  apply FastRouting.sound _ _ [10,33,129,320,96] 13 (by decide) (choices 1) [2,4,16] r30745 c30745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12507
  · exact u12508
  · exact u12509

def b30746 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 35 134 28 21 352 352 480 352), lower := (rows 11 35 134 28 21 32 64 128 256), losses := [] }

theorem u30746 : Upper (D 6) (R 6) [10,33,130,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30747 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 134 28 49 356 324 452 324), lower := (rows 11 35 134 28 49 32 64 128 256), losses := [] }

theorem u30747 : Upper (D 6) (R 6) [10,33,130,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30748 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 134 28 52 353 321 449 321), lower := (rows 11 35 134 28 52 32 64 128 256), losses := [] }

theorem u30748 : Upper (D 6) (R 6) [10,33,130,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30749 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 484, targets := 1 }], pairs := [(2,0),(3,0),(4,1)], upper := (rows 11 35 134 28 81 356 356 484 356), lower := (rows 11 35 134 28 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 63 95 159 287), good := (rows 494 486 486 508 508 32 64 128 256) },{ target := 1, region := (rows 1 0 4 8 17 44 76 140 268), good := (rows 505 49 484 508 81 32 64 128 256) }] }

theorem u30749 : Upper (D 6) (R 6) [10,33,130,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30749 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30750 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 134 28 84 353 353 481 353), lower := (rows 11 35 134 28 84 32 64 128 256), losses := [] }

theorem u30750 : Upper (D 6) (R 6) [10,33,130,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30751 : Route 9 := (fun mask => (mask,id))

def c30751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30751 : Upper (D 6) (R 6) [10,33,130,20,96] 13 := by
  apply FastRouting.sound _ _ [10,33,130,20,96] 13 (by decide) (choices 1) [1,4,64,256] r30751 c30751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12510
  · exact u12511
  · exact u12512
  · exact u12513

def b30752 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 228, targets := 1 }], pairs := [(2,0),(3,0),(4,1)], upper := (rows 11 35 134 28 273 100 100 228 356), lower := (rows 11 35 134 28 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 63 95 159 287), good := (rows 494 486 486 508 508 32 64 128 256) },{ target := 1, region := (rows 1 0 4 8 17 44 76 140 268), good := (rows 505 49 484 508 273 32 64 128 256) }] }

theorem u30752 : Upper (D 6) (R 6) [10,33,130,20,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30753 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 35 134 28 276 97 97 225 353), lower := (rows 11 35 134 28 276 32 64 128 256), losses := [] }

theorem u30753 : Upper (D 6) (R 6) [10,33,130,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30754 : Route 9 := (fun mask => (mask,id))

def c30754 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30754 : Upper (D 6) (R 6) [10,33,130,20,288] 13 := by
  apply FastRouting.sound _ _ [10,33,130,20,288] 13 (by decide) (choices 1) [1,4,64] r30754 c30754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12514
  · exact u12515
  · exact u12516

def r30755 : Route 9 := (fun mask => (mask,id))

def c30755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30755 : Upper (D 6) (R 6) [10,33,130,20,320] 13 := by
  apply FastRouting.sound _ _ [10,33,130,20,320] 13 (by decide) (choices 1) [1,4,64] r30755 c30755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12517
  · exact u12518
  · exact u12519

def b30756 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 35 134 76 21 368 368 496 368), lower := (rows 11 35 134 76 21 32 64 128 256), losses := [] }

theorem u30756 : Upper (D 6) (R 6) [10,33,130,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30757 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 134 76 49 372 340 468 340), lower := (rows 11 35 134 76 49 32 64 128 256), losses := [] }

theorem u30757 : Upper (D 6) (R 6) [10,33,130,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30758 : Route 9 := (fun mask => (mask,id))

def c30758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30758 : Upper (D 6) (R 6) [10,33,130,68,36] 13 := by
  apply FastRouting.sound _ _ [10,33,130,68,36] 13 (by decide) (choices 1) [1,16,64,256] r30758 c30758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12520
  · exact u12521
  · exact u12522
  · exact u12523

def r30759 : Route 9 := (fun mask => (mask,id))

def c30759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30759 : Upper (D 6) (R 6) [10,33,130,68,65] 13 := by
  apply FastRouting.sound _ _ [10,33,130,68,65] 13 (by decide) (choices 1) [4,16,256] r30759 c30759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12524
  · exact u12525
  · exact u12526

def b30760 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 35 134 76 84 305 369 433 305), lower := (rows 11 35 134 76 84 32 64 128 256), losses := [] }

theorem u30760 : Upper (D 6) (R 6) [10,33,130,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30761 : Route 9 := (fun mask => (mask,id))

def c30761 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30761 : Upper (D 6) (R 6) [10,33,130,68,96] 13 := by
  apply FastRouting.sound _ _ [10,33,130,68,96] 13 (by decide) (choices 1) [1,4,16,256] r30761 c30761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12527
  · exact u12528
  · exact u12529
  · exact u12530

def r30762 : Route 9 := (fun mask => (mask,id))

def c30762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30762 : Upper (D 6) (R 6) [10,33,130,68,257] 13 := by
  apply FastRouting.sound _ _ [10,33,130,68,257] 13 (by decide) (choices 1) [4,16,64] r30762 c30762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12531
  · exact u12532
  · exact u12533

def r30763 : Route 9 := (fun mask => (mask,id))

def c30763 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30763 : Upper (D 6) (R 6) [10,33,130,68,260] 13 := by
  apply FastRouting.sound _ _ [10,33,130,68,260] 13 (by decide) (choices 1) [1,16,64] r30763 c30763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12534
  · exact u12535
  · exact u12536

def r30764 : Route 9 := (fun mask => (mask,id))

def c30764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30764 : Upper (D 6) (R 6) [10,33,130,68,288] 13 := by
  apply FastRouting.sound _ _ [10,33,130,68,288] 13 (by decide) (choices 1) [1,4,16,64] r30764 c30764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12537
  · exact u12538
  · exact u12539
  · exact u12540

def r30765 : Route 9 := (fun mask => (mask,id))

def c30765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30765 : Upper (D 6) (R 6) [10,33,130,68,320] 13 := by
  apply FastRouting.sound _ _ [10,33,130,68,320] 13 (by decide) (choices 1) [1,4,16] r30765 c30765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12541
  · exact u12542
  · exact u12543

def b30766 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 0, region := 484, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 35 134 88 21 356 356 484 356), lower := (rows 11 35 134 88 21 32 64 128 256), losses := [] }

theorem u30766 : Upper (D 6) (R 6) [10,33,130,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30767 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 134 88 49 356 324 452 324), lower := (rows 11 35 134 88 49 32 64 128 256), losses := [] }

theorem u30767 : Upper (D 6) (R 6) [10,33,130,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30768 : Route 9 := (fun mask => (mask,id))

def c30768 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30768 : Upper (D 6) (R 6) [10,33,130,80,36] 13 := by
  apply FastRouting.sound _ _ [10,33,130,80,36] 13 (by decide) (choices 1) [1,4,64,256] r30768 c30768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12544
  · exact u12545
  · exact u12546
  · exact u12547

def b30769 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 35 134 88 81 292 356 420 292), lower := (rows 11 35 134 88 81 32 64 128 256), losses := [] }

theorem u30769 : Upper (D 6) (R 6) [10,33,130,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30770 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 35 134 88 84 293 357 421 293), lower := (rows 11 35 134 88 84 32 64 128 256), losses := [] }

theorem u30770 : Upper (D 6) (R 6) [10,33,130,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30771 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 134 88 112 293 325 389 261), lower := (rows 11 35 134 88 112 32 64 128 256), losses := [] }

theorem u30771 : Upper (D 6) (R 6) [10,33,130,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30772 : Route 9 := (fun mask => (mask,id))

def c30772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30772 : Upper (D 6) (R 6) [10,33,130,80,257] 13 := by
  apply FastRouting.sound _ _ [10,33,130,80,257] 13 (by decide) (choices 1) [4,64] r30772 c30772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12548
  · exact u12549

def r30773 : Route 9 := (fun mask => (mask,id))

def c30773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30773 : Upper (D 6) (R 6) [10,33,130,80,260] 13 := by
  apply FastRouting.sound _ _ [10,33,130,80,260] 13 (by decide) (choices 1) [1,4,64] r30773 c30773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12550
  · exact u12551
  · exact u12552

def r30774 : Route 9 := (fun mask => (mask,id))

def c30774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30774 : Upper (D 6) (R 6) [10,33,130,80,288] 13 := by
  apply FastRouting.sound _ _ [10,33,130,80,288] 13 (by decide) (choices 1) [1,4,64] r30774 c30774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12553
  · exact u12554
  · exact u12555

def b30775 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 35 134 88 336 37 101 165 293), lower := (rows 11 35 134 88 336 32 64 128 256), losses := [] }

theorem u30775 : Upper (D 6) (R 6) [10,33,130,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30776 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 360, targets := 3 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(3,0),(3,1)], upper := (rows 11 35 134 268 21 112 112 240 368), lower := (rows 11 35 134 268 21 32 64 128 256), losses := [] }

theorem u30776 : Upper (D 6) (R 6) [10,33,130,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30777 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 11 35 134 268 49 116 84 212 340), lower := (rows 11 35 134 268 49 32 64 128 256), losses := [] }

theorem u30777 : Upper (D 6) (R 6) [10,33,130,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30778 : Route 9 := (fun mask => (mask,id))

def c30778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30778 : Upper (D 6) (R 6) [10,33,130,260,36] 13 := by
  apply FastRouting.sound _ _ [10,33,130,260,36] 13 (by decide) (choices 1) [1,16,64] r30778 c30778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12556
  · exact u12557
  · exact u12558

def r30779 : Route 9 := (fun mask => (mask,id))

def c30779 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30779 : Upper (D 6) (R 6) [10,33,130,260,65] 13 := by
  apply FastRouting.sound _ _ [10,33,130,260,65] 13 (by decide) (choices 1) [4,16,64] r30779 c30779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12559
  · exact u12560
  · exact u12561

#print axioms u30779
end Delivery.IrregularNine14.P06
