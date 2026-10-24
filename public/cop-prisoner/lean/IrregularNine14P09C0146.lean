import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0110
import IrregularNine14P09C0111
import IrregularNine14P09C0112

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8760 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 4, targets := 353 },{ cop := 2, region := 377, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 131 134 268 304 121 89 217 345), lower := (rows 97 131 134 268 304 32 64 128 256), losses := [] }

theorem u8760 : Upper (D 9) (R 9) [96,129,130,260,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8760 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8761 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 4, targets := 353 },{ cop := 2, region := 377, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 131 134 296 336 61 93 157 285), lower := (rows 97 131 134 296 336 32 64 128 256), losses := [] }

theorem u8761 : Upper (D 9) (R 9) [96,129,130,288,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8761 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m8762_16 : Upper (D 9) (R 9) [96,129,136,257,258,16] 13 :=
  permutation_upper _ _ _ [96,129,136,257,258,4] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6619

def r8762 : Route 9 := (fun mask => (mask,id))

def c8762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8762 : Upper (D 9) (R 9) [96,129,136,257,258] 13 := by
  apply FastRouting.sound _ _ [96,129,136,257,258] 13 (by decide) (choices 1) [4,16,64] r8762 c8762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6619
  · exact m8762_16
  · exact u6620

def r8763 : Route 9 := (fun mask => (mask,id))

def c8763 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8763 : Upper (D 9) (R 9) [96,129,136,257,260] 13 := by
  apply FastRouting.sound _ _ [96,129,136,257,260] 13 (by decide) (choices 1) [2,16,64] r8763 c8763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6621
  · exact u6622
  · exact u6623

def r8764 : Route 9 := (fun mask => (mask,id))

def c8764 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8764 : Upper (D 9) (R 9) [96,129,136,257,288] 13 := by
  apply FastRouting.sound _ _ [96,129,136,257,288] 13 (by decide) (choices 1) [2,4,16,64] r8764 c8764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6624
  · exact u6625
  · exact u6626
  · exact u6627

def r8765 : Route 9 := (fun mask => (mask,id))

def c8765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8765 : Upper (D 9) (R 9) [96,129,136,258,260] 13 := by
  apply FastRouting.sound _ _ [96,129,136,258,260] 13 (by decide) (choices 1) [1,16,64] r8765 c8765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6628
  · exact u6629
  · exact u6630

def r8766 : Route 9 := (fun mask => (mask,id))

def c8766 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8766 : Upper (D 9) (R 9) [96,129,136,258,288] 13 := by
  apply FastRouting.sound _ _ [96,129,136,258,288] 13 (by decide) (choices 1) [1,4,16,64] r8766 c8766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6631
  · exact u6632
  · exact u6633
  · exact u6634

theorem m8767_16 : Upper (D 9) (R 9) [96,129,136,260,257,16] 13 :=
  permutation_upper _ _ _ [96,129,136,260,257,2] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6635

def r8767 : Route 9 := (fun mask => (mask,id))

def c8767 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8767 : Upper (D 9) (R 9) [96,129,136,260,257] 13 := by
  apply FastRouting.sound _ _ [96,129,136,260,257] 13 (by decide) (choices 1) [2,16,64] r8767 c8767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6635
  · exact m8767_16
  · exact u6636

def r8768 : Route 9 := (fun mask => (mask,id))

def c8768 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8768 : Upper (D 9) (R 9) [96,129,136,260,258] 13 := by
  apply FastRouting.sound _ _ [96,129,136,260,258] 13 (by decide) (choices 1) [1,16,64] r8768 c8768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6637
  · exact u6638
  · exact u6639

def r8769 : Route 9 := (fun mask => (mask,id))

def c8769 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8769 : Upper (D 9) (R 9) [96,129,136,260,288] 13 := by
  apply FastRouting.sound _ _ [96,129,136,260,288] 13 (by decide) (choices 1) [1,2,16,64] r8769 c8769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6640
  · exact u6641
  · exact u6642
  · exact u6643

def b8770 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 229, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 131 140 280 274 101 101 229 357), lower := (rows 97 131 140 280 274 32 64 128 256), losses := [] }

theorem u8770 : Upper (D 9) (R 9) [96,129,136,272,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8770 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8771 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 227, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 131 140 280 276 99 99 227 355), lower := (rows 97 131 140 280 276 32 64 128 256), losses := [] }

theorem u8771 : Upper (D 9) (R 9) [96,129,136,272,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8771 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8772 : PairBound 9 := { available := 71, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 131 140 280 304 103 71 199 327), lower := (rows 97 131 140 280 304 32 64 128 256), losses := [] }

theorem u8772 : Upper (D 9) (R 9) [96,129,136,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8772 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8773 : Route 9 := (fun mask => (mask,id))

def c8773 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8773 : Upper (D 9) (R 9) [96,129,136,288,257] 13 := by
  apply FastRouting.sound _ _ [96,129,136,288,257] 13 (by decide) (choices 1) [2,4,16,64] r8773 c8773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6644
  · exact u6645
  · exact u6646
  · exact u6647

def r8774 : Route 9 := (fun mask => (mask,id))

def c8774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8774 : Upper (D 9) (R 9) [96,129,136,288,258] 13 := by
  apply FastRouting.sound _ _ [96,129,136,288,258] 13 (by decide) (choices 1) [1,4,16,64] r8774 c8774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6648
  · exact u6649
  · exact u6650
  · exact u6651

def r8775 : Route 9 := (fun mask => (mask,id))

def c8775 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8775 : Upper (D 9) (R 9) [96,129,136,288,260] 13 := by
  apply FastRouting.sound _ _ [96,129,136,288,260] 13 (by decide) (choices 1) [1,2,16,64] r8775 c8775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6652
  · exact u6653
  · exact u6654
  · exact u6655

def r8776 : Route 9 := (fun mask => (mask,id))

def c8776 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8776 : Upper (D 9) (R 9) [96,129,136,288,320] 13 := by
  apply FastRouting.sound _ _ [96,129,136,288,320] 13 (by decide) (choices 1) [1,2,4,16] r8776 c8776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6656
  · exact u6657
  · exact u6658
  · exact u6659

def r8777 : Route 9 := (fun mask => (mask,id))

def c8777 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8777 : Upper (D 9) (R 9) [96,129,160,257,320] 13 := by
  apply FastRouting.sound _ _ [96,129,160,257,320] 13 (by decide) (choices 1) [2,4,8,16] r8777 c8777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6660
  · exact u6661
  · exact u6662
  · exact u6663

def r8778 : Route 9 := (fun mask => (mask,id))

def c8778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8778 : Upper (D 9) (R 9) [96,129,160,258,260] 13 := by
  apply FastRouting.sound _ _ [96,129,160,258,260] 13 (by decide) (choices 1) [1,8,16,64] r8778 c8778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6664
  · exact u6665
  · exact u6666
  · exact u6667

def b8779 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 16, targets := 225 },{ cop := 4, region := 229, targets := 256 }], pairs := [(0,8),(4,0),(4,5),(4,6),(4,7)], upper := (rows 97 131 164 266 280 117 85 213 341), lower := (rows 97 131 164 266 280 32 64 128 256), losses := [] }

theorem u8779 : Upper (D 9) (R 9) [96,129,160,258,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8779 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8780 : Route 9 := (fun mask => (mask,id))

def c8780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8780 : Upper (D 9) (R 9) [96,129,160,258,320] 13 := by
  apply FastRouting.sound _ _ [96,129,160,258,320] 13 (by decide) (choices 1) [1,4,8,16] r8780 c8780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6668
  · exact u6669
  · exact u6670
  · exact u6671

def b8781 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 225 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,8),(4,0),(4,5),(4,6),(4,7)], upper := (rows 97 131 164 268 280 115 83 211 339), lower := (rows 97 131 164 268 280 32 64 128 256), losses := [] }

theorem u8781 : Upper (D 9) (R 9) [96,129,160,260,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8781 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8782 : Route 9 := (fun mask => (mask,id))

def c8782 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8782 : Upper (D 9) (R 9) [96,129,160,260,320] 13 := by
  apply FastRouting.sound _ _ [96,129,160,260,320] 13 (by decide) (choices 1) [1,2,8,16] r8782 c8782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6672
  · exact u6673
  · exact u6674
  · exact u6675

def b8783 : PairBound 9 := { available := 71, camps := [{ cop := 8, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7),(4,0)], upper := (rows 97 131 164 280 280 103 71 199 327), lower := (rows 97 131 164 280 280 32 64 128 256), losses := [] }

theorem u8783 : Upper (D 9) (R 9) [96,129,160,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8783 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8784 : PairBound 9 := { available := 15, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 131 164 280 336 47 79 143 271), lower := (rows 97 131 164 280 336 32 64 128 256), losses := [] }

theorem u8784 : Upper (D 9) (R 9) [96,129,160,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8784 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8785 : PairBound 9 := { available := 25, camps := [{ cop := 7, region := 6, targets := 353 }], pairs := [(1,0),(1,5),(1,6),(1,8),(2,0)], upper := (rows 97 134 134 296 336 57 89 153 281), lower := (rows 97 134 134 296 336 32 64 128 256), losses := [] }

theorem u8785 : Upper (D 9) (R 9) [96,132,130,288,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8785 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8786 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 2, targets := 353 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(1,6),(1,8)], upper := (rows 97 134 140 266 304 113 81 209 337), lower := (rows 97 134 140 266 304 32 64 128 256), losses := [] }

theorem u8786 : Upper (D 9) (R 9) [96,132,136,258,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8786 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8787 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 2, targets := 353 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(1,6),(1,8)], upper := (rows 97 134 140 296 274 113 81 209 337), lower := (rows 97 134 140 296 274 32 64 128 256), losses := [] }

theorem u8787 : Upper (D 9) (R 9) [96,132,136,288,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8787 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8788 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 2, targets := 353 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(1,6),(1,8)], upper := (rows 97 134 140 296 336 51 83 147 275), lower := (rows 97 134 140 296 336 32 64 128 256), losses := [] }

theorem u8788 : Upper (D 9) (R 9) [96,132,136,288,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8788 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8789 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 2, targets := 353 },{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(1,6),(1,8)], upper := (rows 97 134 164 266 336 57 89 153 281), lower := (rows 97 134 164 266 336 32 64 128 256), losses := [] }

theorem u8789 : Upper (D 9) (R 9) [96,132,160,258,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8789 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8790 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 357, targets := 128 },{ cop := 2, region := 227, targets := 256 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,7),(4,7)], upper := (rows 97 134 262 152 280 97 97 225 353), lower := (rows 97 134 262 152 280 32 64 128 256), losses := [] }

theorem u8790 : Upper (D 9) (R 9) [96,132,258,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8790 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8791 : Route 9 := (fun mask => (mask,id))

def c8791 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8791 : Upper (D 9) (R 9) [96,132,258,144,288] 13 := by
  apply FastRouting.sound _ _ [96,132,258,144,288] 13 (by decide) (choices 1) [1,8,64] r8791 c8791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6676
  · exact u6677
  · exact u6678

def r8792 : Route 9 := (fun mask => (mask,id))

def c8792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8792 : Upper (D 9) (R 9) [96,132,258,160,320] 13 := by
  apply FastRouting.sound _ _ [96,132,258,160,320] 13 (by decide) (choices 1) [1,8,16] r8792 c8792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6679
  · exact u6680
  · exact u6681

def b8793 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 2, region := 227, targets := 256 },{ cop := 3, region := 357, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,7),(4,7)], upper := (rows 97 134 268 152 274 97 97 225 353), lower := (rows 97 134 268 152 274 32 64 128 256), losses := [] }

theorem u8793 : Upper (D 9) (R 9) [96,132,264,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8793 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8794 : Route 9 := (fun mask => (mask,id))

def c8794 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8794 : Upper (D 9) (R 9) [96,132,264,144,288] 13 := by
  apply FastRouting.sound _ _ [96,132,264,144,288] 13 (by decide) (choices 1) [1,2,64] r8794 c8794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6682
  · exact u6683
  · exact u6684

def r8795 : Route 9 := (fun mask => (mask,id))

def c8795 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8795 : Upper (D 9) (R 9) [96,132,264,160,320] 13 := by
  apply FastRouting.sound _ _ [96,132,264,160,320] 13 (by decide) (choices 1) [1,2,16] r8795 c8795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6685
  · exact u6686
  · exact u6687

def r8796 : Route 9 := (fun mask => (mask,id))

def c8796 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8796 : Upper (D 9) (R 9) [96,132,288,144,320] 13 := by
  apply FastRouting.sound _ _ [96,132,288,144,320] 13 (by decide) (choices 1) [1,2,8] r8796 c8796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6688
  · exact u6689
  · exact u6690

def r8797 : Route 9 := (fun mask => (mask,id))

def c8797 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8797 : Upper (D 9) (R 9) [96,132,288,192,264] 13 := by
  apply FastRouting.sound _ _ [96,132,288,192,264] 13 (by decide) (choices 1) [1,2,16] r8797 c8797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6691
  · exact u6692
  · exact u6693

def r8798 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8798 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8798 : Upper (D 9) (R 9) [6,9,17,96] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96] 13 (by decide) (choices 2) [96,160,384] r8798 c8798
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6694
  · exact u6695
  · exact u6696

def b8799 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 7, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 11 37 56 464 480 448 448 448), lower := (rows 7 11 37 56 16 32 64 128 256), losses := [] }

theorem u8799 : Upper (D 9) (R 9) [6,9,33,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8799 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8800 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8800 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8800 : Upper (D 9) (R 9) [6,9,33,80] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80] 13 (by decide) (choices 2) [96,160,192,384] r8800 c8800
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6697
  · exact u6698
  · exact u6699
  · exact u6700

def b8801 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 7, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 11 37 104 464 496 464 464 464), lower := (rows 7 11 37 104 16 32 64 128 256), losses := [] }

theorem u8801 : Upper (D 9) (R 9) [6,9,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8801 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8802 : Route 9 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8802 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8802 : Upper (D 9) (R 9) [6,9,33,192] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192] 13 (by decide) (choices 2) [96,192,288,320] r8802 c8802
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6701
  · exact u6702
  · exact u6703
  · exact u6704

def b8803 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 11, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 11 52 41 464 480 448 448 448), lower := (rows 7 11 52 41 16 32 64 128 256), losses := [] }

theorem u8803 : Upper (D 9) (R 9) [6,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8803 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8804 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 480 },{ cop := 0, region := 500, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,0)], upper := (rows 7 11 52 73 496 480 480 480 480), lower := (rows 7 11 52 73 16 32 64 128 256), losses := [] }

theorem u8804 : Upper (D 9) (R 9) [6,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8804 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8805 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8805 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8805 : Upper (D 9) (R 9) [6,9,48,96] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96] 13 (by decide) (choices 2) [65,129,192,384] r8805 c8805
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6705
  · exact u6706
  · exact u6707
  · exact u6708

def r8806 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8806 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8806 : Upper (D 9) (R 9) [6,9,48,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r8806 c8806
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6709
  · exact u6710
  · exact u6711
  · exact u6712
  · exact u6713
  · exact u6714
  · exact u6715

def b8807 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 480 },{ cop := 0, region := 484, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,0)], upper := (rows 7 11 100 25 496 480 480 480 480), lower := (rows 7 11 100 25 16 32 64 128 256), losses := [] }

theorem u8807 : Upper (D 9) (R 9) [6,9,96,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8807 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8808 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 11, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 7 11 100 41 464 496 464 464 464), lower := (rows 7 11 100 41 16 32 64 128 256), losses := [] }

theorem u8808 : Upper (D 9) (R 9) [6,9,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8808 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8809 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8809 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8809 : Upper (D 9) (R 9) [6,9,96,48] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48] 13 (by decide) (choices 2) [65,129,192,384] r8809 c8809
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6716
  · exact u6717
  · exact u6718
  · exact u6719

def b8810 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 11, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 11 100 104 401 433 465 401 401), lower := (rows 7 11 100 104 16 32 64 128 256), losses := [] }

theorem u8810 : Upper (D 9) (R 9) [6,9,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8810 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8811 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 2, targets := 480 },{ cop := 0, region := 500, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,0)], upper := (rows 7 11 100 137 496 496 496 496 496), lower := (rows 7 11 100 137 16 32 64 128 256), losses := [] }

theorem u8811 : Upper (D 9) (R 9) [6,9,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8811 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8812 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8812 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8812 : Upper (D 9) (R 9) [6,9,96,144] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r8812 c8812
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6720
  · exact u6721
  · exact u6722
  · exact u6723
  · exact u6724
  · exact u6725
  · exact u6726

def r8813 : Route 9 := (fun mask => (mask,id))

def c8813 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8813 : Upper (D 9) (R 9) [6,9,96,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160] 13 (by decide) (choices 2) [65,129,192,257,320,384] r8813 c8813
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6727
  · exact u6728
  · exact u6729
  · exact u6730
  · exact u6731
  · exact u6732

def r8814 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8814 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8814 : Upper (D 9) (R 9) [6,9,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384] 13 (by decide) (choices 2) [33,96,129,160,384] r8814 c8814
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u6733
  · exact u6734
  · exact u6735
  · exact u6736
  · exact u6737

def b8815 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 8, targets := 448 },{ cop := 3, region := 4, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7),(3,8)], upper := (rows 7 26 37 41 464 480 448 448 448), lower := (rows 7 26 37 41 16 32 64 128 256), losses := [] }

theorem u8815 : Upper (D 9) (R 9) [6,24,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8815 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8816 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8816 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8816 : Upper (D 9) (R 9) [6,24,33,65] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65] 13 (by decide) (choices 2) [96,160,192,384] r8816 c8816
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6739
  · exact u6740
  · exact u6741
  · exact u6742

theorem m8817_65 : Upper (D 9) (R 9) [6,24,33,96,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6739

theorem m8817_129 : Upper (D 9) (R 9) [6,24,33,96,129] 13 :=
  permutation_upper _ _ _ [6,24,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6740

def r8817 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8817 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8817 : Upper (D 9) (R 9) [6,24,33,96] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96] 13 (by decide) (choices 2) [65,129,192,384] r8817 c8817
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m8817_65
  · exact m8817_129
  · exact u6743
  · exact u6744

theorem m8818_33 : Upper (D 9) (R 9) [6,24,33,192,33] 13 :=
  permutation_upper _ _ _ [6,24,33,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6738

theorem m8818_65 : Upper (D 9) (R 9) [6,24,33,192,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6741

theorem m8818_96 : Upper (D 9) (R 9) [6,24,33,192,96] 13 :=
  permutation_upper _ _ _ [6,24,33,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6743

theorem m8818_257 : Upper (D 9) (R 9) [6,24,33,192,257] 13 :=
  permutation_upper _ _ _ [6,24,33,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6742

theorem m8818_288 : Upper (D 9) (R 9) [6,24,33,192,288] 13 :=
  permutation_upper _ _ _ [6,24,33,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6744

def r8818 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8818 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8818 : Upper (D 9) (R 9) [6,24,33,192] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r8818 c8818
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8818_33
  · exact m8818_65
  · exact m8818_96
  · exact u6745
  · exact m8818_257
  · exact m8818_288
  · exact u6746

def r8819 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8819 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8819 : Upper (D 9) (R 9) [6,24,96,33] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33] 13 (by decide) (choices 2) [65,129,192,384] r8819 c8819
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6747
  · exact u6748
  · exact u6749
  · exact u6750

#print axioms u8819
end Delivery.IrregularNine14.P09
