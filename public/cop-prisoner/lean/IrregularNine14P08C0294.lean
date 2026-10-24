import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0108
import IrregularNine14P08C0109

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r17640 : Route 9 := (fun mask => (mask,id))

def c17640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17640 : Upper (D 8) (R 8) [288,36,65,48,130] 13 := by
  apply FastRouting.sound _ _ [288,36,65,48,130] 13 (by decide) (choices 1) [1,8,64,128] r17640 c17640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6496
  · exact u6497
  · exact u6498
  · exact u6499

def r17641 : Route 9 := (fun mask => (mask,id))

def c17641 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17641 : Upper (D 8) (R 8) [288,36,65,48,136] 13 := by
  apply FastRouting.sound _ _ [288,36,65,48,136] 13 (by decide) (choices 1) [1,2,64,128] r17641 c17641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6500
  · exact u6501
  · exact u6502
  · exact u6503

def r17642 : Route 9 := (fun mask => (mask,id))

def c17642 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17642 : Upper (D 8) (R 8) [288,36,65,48,192] 13 := by
  apply FastRouting.sound _ _ [288,36,65,48,192] 13 (by decide) (choices 1) [1,2,8,128] r17642 c17642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6504
  · exact u6505
  · exact u6506
  · exact u6507

def b17643 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 289 38 69 73 146 184 248 184 440), lower := (rows 289 38 69 73 146 32 64 128 256), losses := [] }

theorem u17643 : Upper (D 8) (R 8) [288,36,65,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17643 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17644 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 289 38 69 73 152 178 242 178 434), lower := (rows 289 38 69 73 152 32 64 128 256), losses := [] }

theorem u17644 : Upper (D 8) (R 8) [288,36,65,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17644 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17645 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 289 38 69 73 176 186 218 154 410), lower := (rows 289 38 69 73 176 32 64 128 256), losses := [] }

theorem u17645 : Upper (D 8) (R 8) [288,36,65,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17645 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17646 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 74 145 184 248 184 440), lower := (rows 289 38 69 74 145 32 64 128 256), losses := [] }

theorem u17646 : Upper (D 8) (R 8) [288,36,65,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17646 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17647 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 74 152 177 241 177 433), lower := (rows 289 38 69 74 152 32 64 128 256), losses := [] }

theorem u17647 : Upper (D 8) (R 8) [288,36,65,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17647 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17648 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 74 176 185 217 153 409), lower := (rows 289 38 69 74 176 32 64 128 256), losses := [] }

theorem u17648 : Upper (D 8) (R 8) [288,36,65,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17648 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17649 : Route 9 := (fun mask => (mask,id))

def c17649 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17649 : Upper (D 8) (R 8) [288,36,65,80,129] 13 := by
  apply FastRouting.sound _ _ [288,36,65,80,129] 13 (by decide) (choices 1) [2,8,128] r17649 c17649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6508
  · exact u6509
  · exact u6510

def b17650 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 88 146 169 233 169 425), lower := (rows 289 38 69 88 146 32 64 128 256), losses := [] }

theorem u17650 : Upper (D 8) (R 8) [288,36,65,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17650 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17651 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 88 152 163 227 163 419), lower := (rows 289 38 69 88 152 32 64 128 256), losses := [] }

theorem u17651 : Upper (D 8) (R 8) [288,36,65,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17652 : Route 9 := (fun mask => (mask,id))

def c17652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17652 : Upper (D 8) (R 8) [288,36,65,80,160] 13 := by
  apply FastRouting.sound _ _ [288,36,65,80,160] 13 (by decide) (choices 1) [1,2,8,128] r17652 c17652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6511
  · exact u6512
  · exact u6513
  · exact u6514

def r17653 : Route 9 := (fun mask => (mask,id))

def c17653 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17653 : Upper (D 8) (R 8) [288,36,65,96,129] 13 := by
  apply FastRouting.sound _ _ [288,36,65,96,129] 13 (by decide) (choices 1) [2,8,16,128] r17653 c17653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6515
  · exact u6516
  · exact u6517
  · exact u6518

def r17654 : Route 9 := (fun mask => (mask,id))

def c17654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17654 : Upper (D 8) (R 8) [288,36,65,96,130] 13 := by
  apply FastRouting.sound _ _ [288,36,65,96,130] 13 (by decide) (choices 1) [1,8,16,128] r17654 c17654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6519
  · exact u6520
  · exact u6521
  · exact u6522

def r17655 : Route 9 := (fun mask => (mask,id))

def c17655 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17655 : Upper (D 8) (R 8) [288,36,65,96,136] 13 := by
  apply FastRouting.sound _ _ [288,36,65,96,136] 13 (by decide) (choices 1) [1,2,16,128] r17655 c17655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6523
  · exact u6524
  · exact u6525
  · exact u6526

def r17656 : Route 9 := (fun mask => (mask,id))

def c17656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17656 : Upper (D 8) (R 8) [288,36,65,129,130] 13 := by
  apply FastRouting.sound _ _ [288,36,65,129,130] 13 (by decide) (choices 1) [8,16,64] r17656 c17656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6527
  · exact u6528
  · exact u6529

def b17657 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 38 69 137 152 114 114 242 370), lower := (rows 289 38 69 137 152 32 64 128 256), losses := [] }

theorem u17657 : Upper (D 8) (R 8) [288,36,65,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17657 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17658 : Route 9 := (fun mask => (mask,id))

def c17658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17658 : Upper (D 8) (R 8) [288,36,65,129,160] 13 := by
  apply FastRouting.sound _ _ [288,36,65,129,160] 13 (by decide) (choices 1) [2,8,16,64] r17658 c17658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6530
  · exact u6531
  · exact u6532
  · exact u6533

def r17659 : Route 9 := (fun mask => (mask,id))

def c17659 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17659 : Upper (D 8) (R 8) [288,36,65,129,192] 13 := by
  apply FastRouting.sound _ _ [288,36,65,129,192] 13 (by decide) (choices 1) [2,8,16] r17659 c17659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6534
  · exact u6535
  · exact u6536

def b17660 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 38 69 138 152 113 113 241 369), lower := (rows 289 38 69 138 152 32 64 128 256), losses := [] }

theorem u17660 : Upper (D 8) (R 8) [288,36,65,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17660 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17661 : Route 9 := (fun mask => (mask,id))

def c17661 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17661 : Upper (D 8) (R 8) [288,36,65,130,160] 13 := by
  apply FastRouting.sound _ _ [288,36,65,130,160] 13 (by decide) (choices 1) [1,8,16,64] r17661 c17661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6537
  · exact u6538
  · exact u6539
  · exact u6540

def r17662 : Route 9 := (fun mask => (mask,id))

def c17662 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17662 : Upper (D 8) (R 8) [288,36,65,130,192] 13 := by
  apply FastRouting.sound _ _ [288,36,65,130,192] 13 (by decide) (choices 1) [1,8,16] r17662 c17662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6541
  · exact u6542
  · exact u6543

def b17663 : PairBound 9 := { available := 99, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 69 152 152 99 99 227 355), lower := (rows 289 38 69 152 152 32 64 128 256), losses := [] }

theorem u17663 : Upper (D 8) (R 8) [288,36,65,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17663 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17664 : PairBound 9 := { available := 75, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 69 152 176 107 75 203 331), lower := (rows 289 38 69 152 176 32 64 128 256), losses := [] }

theorem u17664 : Upper (D 8) (R 8) [288,36,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17665 : PairBound 9 := { available := 43, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 69 152 208 43 107 171 299), lower := (rows 289 38 69 152 208 32 64 128 256), losses := [] }

theorem u17665 : Upper (D 8) (R 8) [288,36,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17665 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17666 : Route 9 := (fun mask => (mask,id))

def c17666 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17666 : Upper (D 8) (R 8) [288,36,65,160,192] 13 := by
  apply FastRouting.sound _ _ [288,36,65,160,192] 13 (by decide) (choices 1) [1,2,8,16] r17666 c17666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6544
  · exact u6545
  · exact u6546
  · exact u6547

def b17667 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 70 56 88 161 193 129 385), lower := (rows 289 38 70 56 88 32 64 128 256), losses := [] }

theorem u17667 : Upper (D 8) (R 8) [288,36,66,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m17668_128 : Upper (D 8) (R 8) [288,36,66,48,136,128] 13 :=
  permutation_upper _ _ _ [288,36,66,48,136,64] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6549

def r17668 : Route 9 := (fun mask => (mask,id))

def c17668 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17668 : Upper (D 8) (R 8) [288,36,66,48,136] 13 := by
  apply FastRouting.sound _ _ [288,36,66,48,136] 13 (by decide) (choices 1) [1,64,128] r17668 c17668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6548
  · exact u6549
  · exact m17668_128

def b17669 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 70 56 208 169 201 137 393), lower := (rows 289 38 70 56 208 32 64 128 256), losses := [] }

theorem u17669 : Upper (D 8) (R 8) [288,36,66,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17669 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17670 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 70 73 145 184 248 184 440), lower := (rows 289 38 70 73 145 32 64 128 256), losses := [] }

theorem u17670 : Upper (D 8) (R 8) [288,36,66,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17670 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17671 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 70 73 152 177 241 177 433), lower := (rows 289 38 70 73 152 32 64 128 256), losses := [] }

theorem u17671 : Upper (D 8) (R 8) [288,36,66,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17671 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17672 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 70 73 176 185 217 153 409), lower := (rows 289 38 70 73 176 32 64 128 256), losses := [] }

theorem u17672 : Upper (D 8) (R 8) [288,36,66,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17672 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17673 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 70 88 145 169 233 169 425), lower := (rows 289 38 70 88 145 32 64 128 256), losses := [] }

theorem u17673 : Upper (D 8) (R 8) [288,36,66,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17673 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17674 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 70 88 152 161 225 161 417), lower := (rows 289 38 70 88 152 32 64 128 256), losses := [] }

theorem u17674 : Upper (D 8) (R 8) [288,36,66,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17674 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17675 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 70 88 176 169 201 137 393), lower := (rows 289 38 70 88 176 32 64 128 256), losses := [] }

theorem u17675 : Upper (D 8) (R 8) [288,36,66,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17676 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 70 104 145 185 217 153 409), lower := (rows 289 38 70 104 145 32 64 128 256), losses := [] }

theorem u17676 : Upper (D 8) (R 8) [288,36,66,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17676 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17677 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 70 104 152 177 209 145 401), lower := (rows 289 38 70 104 152 32 64 128 256), losses := [] }

theorem u17677 : Upper (D 8) (R 8) [288,36,66,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17677 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17678 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 38 70 137 145 120 120 248 376), lower := (rows 289 38 70 137 145 32 64 128 256), losses := [] }

theorem u17678 : Upper (D 8) (R 8) [288,36,66,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17678 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17679 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 38 70 137 152 113 113 241 369), lower := (rows 289 38 70 137 152 32 64 128 256), losses := [] }

theorem u17679 : Upper (D 8) (R 8) [288,36,66,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17679 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17680 : Route 9 := (fun mask => (mask,id))

def c17680 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17680 : Upper (D 8) (R 8) [288,36,66,129,160] 13 := by
  apply FastRouting.sound _ _ [288,36,66,129,160] 13 (by decide) (choices 1) [1,8,16,64] r17680 c17680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6550
  · exact u6551
  · exact u6552
  · exact u6553

def b17681 : PairBound 9 := { available := 57, camps := [{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 70 137 208 57 121 185 313), lower := (rows 289 38 70 137 208 32 64 128 256), losses := [] }

theorem u17681 : Upper (D 8) (R 8) [288,36,66,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17681 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17682 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 70 152 152 97 97 225 353), lower := (rows 289 38 70 152 152 32 64 128 256), losses := [] }

theorem u17682 : Upper (D 8) (R 8) [288,36,66,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17682 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17683 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 70 152 176 105 73 201 329), lower := (rows 289 38 70 152 176 32 64 128 256), losses := [] }

theorem u17683 : Upper (D 8) (R 8) [288,36,66,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17683 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17684 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 70 152 208 41 105 169 297), lower := (rows 289 38 70 152 208 32 64 128 256), losses := [] }

theorem u17684 : Upper (D 8) (R 8) [288,36,66,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17685 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 70 168 208 57 89 153 281), lower := (rows 289 38 70 168 208 32 64 128 256), losses := [] }

theorem u17685 : Upper (D 8) (R 8) [288,36,66,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17685 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17686 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 56 82 161 193 129 385), lower := (rows 289 38 76 56 82 32 64 128 256), losses := [] }

theorem u17686 : Upper (D 8) (R 8) [288,36,72,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m17687_128 : Upper (D 8) (R 8) [288,36,72,48,130,128] 13 :=
  permutation_upper _ _ _ [288,36,72,48,130,64] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6555

def r17687 : Route 9 := (fun mask => (mask,id))

def c17687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17687 : Upper (D 8) (R 8) [288,36,72,48,130] 13 := by
  apply FastRouting.sound _ _ [288,36,72,48,130] 13 (by decide) (choices 1) [1,64,128] r17687 c17687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6554
  · exact u6555
  · exact m17687_128

def b17688 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 56 208 163 195 131 387), lower := (rows 289 38 76 56 208 32 64 128 256), losses := [] }

theorem u17688 : Upper (D 8) (R 8) [288,36,72,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17688 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17689 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 73 145 178 242 178 434), lower := (rows 289 38 76 73 145 32 64 128 256), losses := [] }

theorem u17689 : Upper (D 8) (R 8) [288,36,72,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17689 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17690 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 73 146 177 241 177 433), lower := (rows 289 38 76 73 146 32 64 128 256), losses := [] }

theorem u17690 : Upper (D 8) (R 8) [288,36,72,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17690 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17691 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 73 176 179 211 147 403), lower := (rows 289 38 76 73 176 32 64 128 256), losses := [] }

theorem u17691 : Upper (D 8) (R 8) [288,36,72,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17691 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17692 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 74 145 177 241 177 433), lower := (rows 289 38 76 74 145 32 64 128 256), losses := [] }

theorem u17692 : Upper (D 8) (R 8) [288,36,72,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17692 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17693 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 74 176 177 209 145 401), lower := (rows 289 38 76 74 176 32 64 128 256), losses := [] }

theorem u17693 : Upper (D 8) (R 8) [288,36,72,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17693 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17694 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 88 145 163 227 163 419), lower := (rows 289 38 76 88 145 32 64 128 256), losses := [] }

theorem u17694 : Upper (D 8) (R 8) [288,36,72,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17694 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17695 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 88 146 161 225 161 417), lower := (rows 289 38 76 88 146 32 64 128 256), losses := [] }

theorem u17695 : Upper (D 8) (R 8) [288,36,72,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17696 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 88 176 163 195 131 387), lower := (rows 289 38 76 88 176 32 64 128 256), losses := [] }

theorem u17696 : Upper (D 8) (R 8) [288,36,72,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17696 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17697 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 76 104 145 179 211 147 403), lower := (rows 289 38 76 104 145 32 64 128 256), losses := [] }

theorem u17697 : Upper (D 8) (R 8) [288,36,72,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17697 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17698 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 76 104 146 177 209 145 401), lower := (rows 289 38 76 104 146 32 64 128 256), losses := [] }

theorem u17698 : Upper (D 8) (R 8) [288,36,72,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17698 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17699 : Route 9 := (fun mask => (mask,id))

def c17699 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u17699 : Upper (D 8) (R 8) [288,36,72,129,65] 13 := by
  apply FastRouting.sound _ _ [288,36,72,129,65] 13 (by decide) (choices 1) [2,16,128] r17699 c17699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6556
  · exact u6557
  · exact u6558

#print axioms u17699
end Delivery.IrregularNine14.P08
