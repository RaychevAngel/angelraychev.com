import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0048
import IrregularNine14P09C0049

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6600 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 50, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 97 38 388 137 274 48 73 201 329), lower := (rows 97 38 388 137 274 48 64 128 256), losses := [] }

theorem u6600 : Upper (D 9) (R 9) [96,36,384,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6600 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6601 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 233, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 388 137 274 96 89 153 281), lower := (rows 97 38 388 137 274 96 64 128 256), losses := [] }

theorem u6601 : Upper (D 9) (R 9) [96,36,384,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6601 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6602 : Route 9 := (fun mask => (mask,id))

def c6602 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6602 : Upper (D 9) (R 9) [96,36,384,129,264,1] 13 := by
  apply FastRouting.sound _ _ [96,36,384,129,264,1] 13 (by decide) (choices 1) [2,16] r6602 c6602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2889
  · exact u2890

def b6603 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 388 137 280 34 81 209 337), lower := (rows 97 38 388 137 280 34 64 128 256), losses := [] }

theorem u6603 : Upper (D 9) (R 9) [96,36,384,129,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6603 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6604 : Route 9 := (fun mask => (mask,id))

def c6604 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6604 : Upper (D 9) (R 9) [96,36,384,129,264,16] 13 := by
  apply FastRouting.sound _ _ [96,36,384,129,264,16] 13 (by decide) (choices 1) [1,2] r6604 c6604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2891
  · exact u2892

def b6605 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 388 137 280 96 83 147 275), lower := (rows 97 38 388 137 280 96 64 128 256), losses := [] }

theorem u6605 : Upper (D 9) (R 9) [96,36,384,129,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6605 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6606 : Route 9 := (fun mask => (mask,id))

def c6606 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6606 : Upper (D 9) (R 9) [96,36,384,129,320,1] 13 := by
  apply FastRouting.sound _ _ [96,36,384,129,320,1] 13 (by decide) (choices 1) [2,8,16] r6606 c6606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2893
  · exact u2894
  · exact u2895

def b6607 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 388 137 336 34 89 153 281), lower := (rows 97 38 388 137 336 34 64 128 256), losses := [] }

theorem u6607 : Upper (D 9) (R 9) [96,36,384,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6607 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6608 : Route 9 := (fun mask => (mask,id))

def c6608 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6608 : Upper (D 9) (R 9) [96,36,384,129,320,8] 13 := by
  apply FastRouting.sound _ _ [96,36,384,129,320,8] 13 (by decide) (choices 1) [1,2,16] r6608 c6608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2896
  · exact u2897
  · exact u2898

def b6609 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 201, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6)], upper := (rows 97 38 388 137 336 48 75 139 267), lower := (rows 97 38 388 137 336 48 64 128 256), losses := [] }

theorem u6609 : Upper (D 9) (R 9) [96,36,384,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6609 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6610 : Route 9 := (fun mask => (mask,id))

def c6610 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6610 : Upper (D 9) (R 9) [96,36,384,130,264,1] 13 := by
  apply FastRouting.sound _ _ [96,36,384,130,264,1] 13 (by decide) (choices 1) [1,16] r6610 c6610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2899
  · exact u2900

def b6611 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 58, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 97 38 388 138 280 48 65 193 321), lower := (rows 97 38 388 138 280 48 64 128 256), losses := [] }

theorem u6611 : Upper (D 9) (R 9) [96,36,384,130,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6611 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6612 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 38 388 138 280 96 81 145 273), lower := (rows 97 38 388 138 280 96 64 128 256), losses := [] }

theorem u6612 : Upper (D 9) (R 9) [96,36,384,130,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6612 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6613 : Route 9 := (fun mask => (mask,id))

def c6613 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6613 : Upper (D 9) (R 9) [96,36,384,130,320,1] 13 := by
  apply FastRouting.sound _ _ [96,36,384,130,320,1] 13 (by decide) (choices 1) [1,8,16] r6613 c6613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2901
  · exact u2902
  · exact u2903

def b6614 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 42, targets := 321 }], pairs := [(1,0),(1,6),(1,8),(3,0)], upper := (rows 97 38 388 138 336 40 81 145 273), lower := (rows 97 38 388 138 336 40 64 128 256), losses := [] }

theorem u6614 : Upper (D 9) (R 9) [96,36,384,130,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6614 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6615 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 201, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6)], upper := (rows 97 38 388 138 336 48 73 137 265), lower := (rows 97 38 388 138 336 48 64 128 256), losses := [] }

theorem u6615 : Upper (D 9) (R 9) [96,36,384,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6615 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6616 : Route 9 := (fun mask => (mask,id))

def c6616 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6616 : Upper (D 9) (R 9) [96,36,384,144,320,1] 13 := by
  apply FastRouting.sound _ _ [96,36,384,144,320,1] 13 (by decide) (choices 1) [1,2,8] r6616 c6616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2904
  · exact u2905
  · exact u2906

def b6617 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 34, targets := 449 }], pairs := [(1,0),(1,6),(1,7),(1,8)], upper := (rows 97 38 388 152 336 34 73 137 265), lower := (rows 97 38 388 152 336 34 64 128 256), losses := [] }

theorem u6617 : Upper (D 9) (R 9) [96,36,384,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6617 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6618 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(4,7)], upper := (rows 97 38 388 152 336 40 67 131 259), lower := (rows 97 38 388 152 336 40 64 128 256), losses := [] }

theorem u6618 : Upper (D 9) (R 9) [96,36,384,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6618 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6619 : Route 9 := (fun mask => (mask,id))

def c6619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6619 : Upper (D 9) (R 9) [96,129,136,257,258,4] 13 := by
  apply FastRouting.sound _ _ [96,129,136,257,258,4] 13 (by decide) (choices 1) [16,32] r6619 c6619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2907
  · exact u2908

def b6620 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 131 140 265 274 96 116 180 308), lower := (rows 97 131 140 265 274 96 64 128 256), losses := [] }

theorem u6620 : Upper (D 9) (R 9) [96,129,136,257,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6620 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6621 : Route 9 := (fun mask => (mask,id))

def c6621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6621 : Upper (D 9) (R 9) [96,129,136,257,260,2] 13 := by
  apply FastRouting.sound _ _ [96,129,136,257,260,2] 13 (by decide) (choices 1) [16,32] r6621 c6621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2909
  · exact u2910

theorem m6622_2 : Upper (D 9) (R 9) [96,129,136,257,260,16,2] 13 :=
  permutation_upper _ _ _ [96,129,136,257,260,2,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2909

def r6622 : Route 9 := (fun mask => (mask,id))

def c6622 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6622 : Upper (D 9) (R 9) [96,129,136,257,260,16] 13 := by
  apply FastRouting.sound _ _ [96,129,136,257,260,16] 13 (by decide) (choices 1) [2,32] r6622 c6622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m6622_2
  · exact u2911

def b6623 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 131 140 265 276 96 114 178 306), lower := (rows 97 131 140 265 276 96 64 128 256), losses := [] }

theorem u6623 : Upper (D 9) (R 9) [96,129,136,257,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6623 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6624 : Route 9 := (fun mask => (mask,id))

def c6624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6624 : Upper (D 9) (R 9) [96,129,136,257,288,2] 13 := by
  apply FastRouting.sound _ _ [96,129,136,257,288,2] 13 (by decide) (choices 1) [4,16] r6624 c6624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2912
  · exact u2913

def r6625 : Route 9 := (fun mask => (mask,id))

def c6625 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6625 : Upper (D 9) (R 9) [96,129,136,257,288,4] 13 := by
  apply FastRouting.sound _ _ [96,129,136,257,288,4] 13 (by decide) (choices 1) [2,16] r6625 c6625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2914
  · exact u2915

def b6626 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 131 140 265 304 48 70 198 326), lower := (rows 97 131 140 265 304 48 64 128 256), losses := [] }

theorem u6626 : Upper (D 9) (R 9) [96,129,136,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6626 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6627 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 131 140 265 304 96 86 150 278), lower := (rows 97 131 140 265 304 96 64 128 256), losses := [] }

theorem u6627 : Upper (D 9) (R 9) [96,129,136,257,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6627 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6628 : Route 9 := (fun mask => (mask,id))

def c6628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6628 : Upper (D 9) (R 9) [96,129,136,258,260,1] 13 := by
  apply FastRouting.sound _ _ [96,129,136,258,260,1] 13 (by decide) (choices 1) [16,32] r6628 c6628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2916
  · exact u2917

def b6629 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(4,7)], upper := (rows 97 131 140 266 276 48 97 225 353), lower := (rows 97 131 140 266 276 48 64 128 256), losses := [] }

theorem u6629 : Upper (D 9) (R 9) [96,129,136,258,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6629 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6630 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 131 140 266 276 96 113 177 305), lower := (rows 97 131 140 266 276 96 64 128 256), losses := [] }

theorem u6630 : Upper (D 9) (R 9) [96,129,136,258,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6630 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6631 : Route 9 := (fun mask => (mask,id))

def c6631 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6631 : Upper (D 9) (R 9) [96,129,136,258,288,1] 13 := by
  apply FastRouting.sound _ _ [96,129,136,258,288,1] 13 (by decide) (choices 1) [4,16] r6631 c6631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2918
  · exact u2919

def b6632 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 4, region := 195, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(4,7)], upper := (rows 97 131 140 266 304 36 81 209 337), lower := (rows 97 131 140 266 304 36 64 128 256), losses := [] }

theorem u6632 : Upper (D 9) (R 9) [96,129,136,258,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6632 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6633 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 131 140 266 304 48 69 197 325), lower := (rows 97 131 140 266 304 48 64 128 256), losses := [] }

theorem u6633 : Upper (D 9) (R 9) [96,129,136,258,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6633 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6634 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 131 140 266 304 96 85 149 277), lower := (rows 97 131 140 266 304 96 64 128 256), losses := [] }

theorem u6634 : Upper (D 9) (R 9) [96,129,136,258,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6634 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6635 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(4,7)], upper := (rows 97 131 140 268 273 34 112 240 368), lower := (rows 97 131 140 268 273 34 64 128 256), losses := [] }

theorem u6635 : Upper (D 9) (R 9) [96,129,136,260,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6635 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6636 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 131 140 268 273 96 114 178 306), lower := (rows 97 131 140 268 273 96 64 128 256), losses := [] }

theorem u6636 : Upper (D 9) (R 9) [96,129,136,260,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6636 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6637 : Route 9 := (fun mask => (mask,id))

def c6637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6637 : Upper (D 9) (R 9) [96,129,136,260,258,1] 13 := by
  apply FastRouting.sound _ _ [96,129,136,260,258,1] 13 (by decide) (choices 1) [16,32] r6637 c6637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2920
  · exact u2921

def b6638 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(4,7)], upper := (rows 97 131 140 268 274 48 97 225 353), lower := (rows 97 131 140 268 274 48 64 128 256), losses := [] }

theorem u6638 : Upper (D 9) (R 9) [96,129,136,260,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6638 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6639 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 131 140 268 274 96 113 177 305), lower := (rows 97 131 140 268 274 96 64 128 256), losses := [] }

theorem u6639 : Upper (D 9) (R 9) [96,129,136,260,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6639 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6640 : Route 9 := (fun mask => (mask,id))

def c6640 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6640 : Upper (D 9) (R 9) [96,129,136,260,288,1] 13 := by
  apply FastRouting.sound _ _ [96,129,136,260,288,1] 13 (by decide) (choices 1) [2,16] r6640 c6640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2922
  · exact u2923

def b6641 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 4, region := 195, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(4,7)], upper := (rows 97 131 140 268 304 34 81 209 337), lower := (rows 97 131 140 268 304 34 64 128 256), losses := [] }

theorem u6641 : Upper (D 9) (R 9) [96,129,136,260,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6641 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6642 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 131 140 268 304 48 67 195 323), lower := (rows 97 131 140 268 304 48 64 128 256), losses := [] }

theorem u6642 : Upper (D 9) (R 9) [96,129,136,260,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6642 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6643 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 131 140 268 304 96 83 147 275), lower := (rows 97 131 140 268 304 96 64 128 256), losses := [] }

theorem u6643 : Upper (D 9) (R 9) [96,129,136,260,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6643 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6644 : Route 9 := (fun mask => (mask,id))

def c6644 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6644 : Upper (D 9) (R 9) [96,129,136,288,257,2] 13 := by
  apply FastRouting.sound _ _ [96,129,136,288,257,2] 13 (by decide) (choices 1) [4,16] r6644 c6644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2924
  · exact u2925

def b6645 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 402, targets := 32 },{ cop := 1, region := 336, targets := 128 },{ cop := 4, region := 194, targets := 256 }], pairs := [(1,5),(1,8),(4,5),(4,7)], upper := (rows 97 131 140 296 273 36 82 210 338), lower := (rows 97 131 140 296 273 36 64 128 256), losses := [] }

theorem u6645 : Upper (D 9) (R 9) [96,129,136,288,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6645 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6646 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 97 131 140 296 273 48 70 198 326), lower := (rows 97 131 140 296 273 48 64 128 256), losses := [] }

theorem u6646 : Upper (D 9) (R 9) [96,129,136,288,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6646 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6647 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 131 140 296 273 96 86 150 278), lower := (rows 97 131 140 296 273 96 64 128 256), losses := [] }

theorem u6647 : Upper (D 9) (R 9) [96,129,136,288,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6647 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6648 : Route 9 := (fun mask => (mask,id))

def c6648 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6648 : Upper (D 9) (R 9) [96,129,136,288,258,1] 13 := by
  apply FastRouting.sound _ _ [96,129,136,288,258,1] 13 (by decide) (choices 1) [4,16] r6648 c6648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2926
  · exact u2927

def r6649 : Route 9 := (fun mask => (mask,id))

def c6649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6649 : Upper (D 9) (R 9) [96,129,136,288,258,4] 13 := by
  apply FastRouting.sound _ _ [96,129,136,288,258,4] 13 (by decide) (choices 1) [1,16] r6649 c6649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2928
  · exact u2929

def b6650 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 97 131 140 296 274 48 69 197 325), lower := (rows 97 131 140 296 274 48 64 128 256), losses := [] }

theorem u6650 : Upper (D 9) (R 9) [96,129,136,288,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6650 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6651 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 131 140 296 274 96 85 149 277), lower := (rows 97 131 140 296 274 96 64 128 256), losses := [] }

theorem u6651 : Upper (D 9) (R 9) [96,129,136,288,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6651 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6652 : Route 9 := (fun mask => (mask,id))

def c6652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6652 : Upper (D 9) (R 9) [96,129,136,288,260,1] 13 := by
  apply FastRouting.sound _ _ [96,129,136,288,260,1] 13 (by decide) (choices 1) [2,16] r6652 c6652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2930
  · exact u2931

def r6653 : Route 9 := (fun mask => (mask,id))

def c6653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6653 : Upper (D 9) (R 9) [96,129,136,288,260,2] 13 := by
  apply FastRouting.sound _ _ [96,129,136,288,260,2] 13 (by decide) (choices 1) [1,16] r6653 c6653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2932
  · exact u2933

def b6654 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 97 131 140 296 276 48 67 195 323), lower := (rows 97 131 140 296 276 48 64 128 256), losses := [] }

theorem u6654 : Upper (D 9) (R 9) [96,129,136,288,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6654 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6655 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 131 140 296 276 96 83 147 275), lower := (rows 97 131 140 296 276 96 64 128 256), losses := [] }

theorem u6655 : Upper (D 9) (R 9) [96,129,136,288,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6655 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6656 : Route 9 := (fun mask => (mask,id))

def c6656 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6656 : Upper (D 9) (R 9) [96,129,136,288,320,1] 13 := by
  apply FastRouting.sound _ _ [96,129,136,288,320,1] 13 (by decide) (choices 1) [2,4,16] r6656 c6656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2934
  · exact u2935
  · exact u2936

def r6657 : Route 9 := (fun mask => (mask,id))

def c6657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6657 : Upper (D 9) (R 9) [96,129,136,288,320,2] 13 := by
  apply FastRouting.sound _ _ [96,129,136,288,320,2] 13 (by decide) (choices 1) [1,4,16] r6657 c6657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2937
  · exact u2938
  · exact u2939

def r6658 : Route 9 := (fun mask => (mask,id))

def c6658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6658 : Upper (D 9) (R 9) [96,129,136,288,320,4] 13 := by
  apply FastRouting.sound _ _ [96,129,136,288,320,4] 13 (by decide) (choices 1) [1,2,16] r6658 c6658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2940
  · exact u2941
  · exact u2942

def b6659 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6)], upper := (rows 97 131 140 296 336 48 71 135 263), lower := (rows 97 131 140 296 336 48 64 128 256), losses := [] }

theorem u6659 : Upper (D 9) (R 9) [96,129,136,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6659 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u6659
end Delivery.IrregularNine14.P09
