import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0049
import IrregularNine14P09C0050

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6660 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 36, targets := 321 },{ cop := 2, region := 345, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(2,8)], upper := (rows 97 131 164 265 336 34 92 156 284), lower := (rows 97 131 164 265 336 34 64 128 256), losses := [] }

theorem u6660 : Upper (D 9) (R 9) [96,129,160,257,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6660 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6661 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 410, targets := 32 },{ cop := 1, region := 36, targets := 1 }], pairs := [(1,5),(2,0),(3,5),(4,5)], upper := (rows 97 131 164 265 336 36 90 154 282), lower := (rows 97 131 164 265 336 36 64 128 256), losses := [] }

theorem u6661 : Upper (D 9) (R 9) [96,129,160,257,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6661 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6662_16 : Upper (D 9) (R 9) [96,129,160,257,320,8,16] 13 :=
  permutation_upper _ _ _ [96,129,160,257,320,4,2] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2943

def r6662 : Route 9 := (fun mask => (mask,id))

def c6662 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6662 : Upper (D 9) (R 9) [96,129,160,257,320,8] 13 := by
  apply FastRouting.sound _ _ [96,129,160,257,320,8] 13 (by decide) (choices 1) [2,4,16] r6662 c6662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2944
  · exact u2945
  · exact m6662_16

def b6663 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 131 164 265 336 48 78 142 270), lower := (rows 97 131 164 265 336 48 64 128 256), losses := [] }

theorem u6663 : Upper (D 9) (R 9) [96,129,160,257,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6663 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6664 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 36, targets := 320 },{ cop := 6, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(2,6),(2,8),(4,6)], upper := (rows 97 131 164 266 276 33 88 216 344), lower := (rows 97 131 164 266 276 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 6 8 24 35 0 128 256), good := (rows 33 167 164 318 276 33 0 128 256) }] }

theorem u6664 : Upper (D 9) (R 9) [96,129,160,258,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6664 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6665 : Route 9 := (fun mask => (mask,id))

def c6665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6665 : Upper (D 9) (R 9) [96,129,160,258,260,8] 13 := by
  apply FastRouting.sound _ _ [96,129,160,258,260,8] 13 (by decide) (choices 1) [1,16] r6665 c6665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2946
  · exact u2947

def r6666 : Route 9 := (fun mask => (mask,id))

def c6666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6666 : Upper (D 9) (R 9) [96,129,160,258,260,16] 13 := by
  apply FastRouting.sound _ _ [96,129,160,258,260,16] 13 (by decide) (choices 1) [1,8] r6666 c6666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2948
  · exact u2949

def b6667 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 131 164 266 276 96 89 153 281), lower := (rows 97 131 164 266 276 96 64 128 256), losses := [] }

theorem u6667 : Upper (D 9) (R 9) [96,129,160,258,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6667 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6668 : Route 9 := (fun mask => (mask,id))

def c6668 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6668 : Upper (D 9) (R 9) [96,129,160,258,320,1] 13 := by
  apply FastRouting.sound _ _ [96,129,160,258,320,1] 13 (by decide) (choices 1) [4,8,16] r6668 c6668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2950
  · exact u2951
  · exact u2952

def b6669 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 410, targets := 32 },{ cop := 1, region := 36, targets := 1 }], pairs := [(1,5),(2,0),(3,5),(4,5)], upper := (rows 97 131 164 266 336 36 89 153 281), lower := (rows 97 131 164 266 336 36 64 128 256), losses := [] }

theorem u6669 : Upper (D 9) (R 9) [96,129,160,258,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6669 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6670 : Route 9 := (fun mask => (mask,id))

def c6670 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6670 : Upper (D 9) (R 9) [96,129,160,258,320,8] 13 := by
  apply FastRouting.sound _ _ [96,129,160,258,320,8] 13 (by decide) (choices 1) [1,4,16] r6670 c6670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2953
  · exact u2954
  · exact u2955

def b6671 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 131 164 266 336 48 77 141 269), lower := (rows 97 131 164 266 336 48 64 128 256), losses := [] }

theorem u6671 : Upper (D 9) (R 9) [96,129,160,258,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6671 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6672 : Route 9 := (fun mask => (mask,id))

def c6672 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6672 : Upper (D 9) (R 9) [96,129,160,260,320,1] 13 := by
  apply FastRouting.sound _ _ [96,129,160,260,320,1] 13 (by decide) (choices 1) [2,8,16] r6672 c6672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2956
  · exact u2957
  · exact u2958

def b6673 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 36, targets := 321 },{ cop := 2, region := 345, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(2,8)], upper := (rows 97 131 164 268 336 34 89 153 281), lower := (rows 97 131 164 268 336 34 64 128 256), losses := [] }

theorem u6673 : Upper (D 9) (R 9) [96,129,160,260,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6673 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6674 : Route 9 := (fun mask => (mask,id))

def c6674 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6674 : Upper (D 9) (R 9) [96,129,160,260,320,8] 13 := by
  apply FastRouting.sound _ _ [96,129,160,260,320,8] 13 (by decide) (choices 1) [1,2,16] r6674 c6674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2959
  · exact u2960
  · exact u2961

def b6675 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 131 164 268 336 48 75 139 267), lower := (rows 97 131 164 268 336 48 64 128 256), losses := [] }

theorem u6675 : Upper (D 9) (R 9) [96,129,160,260,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6675 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6676 : Route 9 := (fun mask => (mask,id))

def c6676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6676 : Upper (D 9) (R 9) [96,132,258,144,288,1] 13 := by
  apply FastRouting.sound _ _ [96,132,258,144,288,1] 13 (by decide) (choices 1) [1,8] r6676 c6676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2962
  · exact u2963

def b6677 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(4,7)], upper := (rows 97 134 262 152 304 40 65 193 321), lower := (rows 97 134 262 152 304 40 64 128 256), losses := [] }

theorem u6677 : Upper (D 9) (R 9) [96,132,258,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6677 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6678 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 134 262 152 304 96 73 137 265), lower := (rows 97 134 262 152 304 96 64 128 256), losses := [] }

theorem u6678 : Upper (D 9) (R 9) [96,132,258,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6678 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6679 : Route 9 := (fun mask => (mask,id))

def c6679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6679 : Upper (D 9) (R 9) [96,132,258,160,320,1] 13 := by
  apply FastRouting.sound _ _ [96,132,258,160,320,1] 13 (by decide) (choices 1) [1,8,16] r6679 c6679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2964
  · exact u2965
  · exact u2966

def b6680 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 1, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 97 134 262 168 336 40 81 145 273), lower := (rows 97 134 262 168 336 40 64 128 256), losses := [] }

theorem u6680 : Upper (D 9) (R 9) [96,132,258,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6680 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6681 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 134 262 168 336 48 73 137 265), lower := (rows 97 134 262 168 336 48 64 128 256), losses := [] }

theorem u6681 : Upper (D 9) (R 9) [96,132,258,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6681 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6682 : Route 9 := (fun mask => (mask,id))

def c6682 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6682 : Upper (D 9) (R 9) [96,132,264,144,288,1] 13 := by
  apply FastRouting.sound _ _ [96,132,264,144,288,1] 13 (by decide) (choices 1) [1,2] r6682 c6682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2967
  · exact u2968

def b6683 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 369, targets := 128 },{ cop := 2, region := 227, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(4,7)], upper := (rows 97 134 268 152 304 34 65 193 321), lower := (rows 97 134 268 152 304 34 64 128 256), losses := [] }

theorem u6683 : Upper (D 9) (R 9) [96,132,264,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6683 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6684 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 134 268 152 304 96 67 131 259), lower := (rows 97 134 268 152 304 96 64 128 256), losses := [] }

theorem u6684 : Upper (D 9) (R 9) [96,132,264,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6684 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6685 : Route 9 := (fun mask => (mask,id))

def c6685 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6685 : Upper (D 9) (R 9) [96,132,264,160,320,1] 13 := by
  apply FastRouting.sound _ _ [96,132,264,160,320,1] 13 (by decide) (choices 1) [1,2,16] r6685 c6685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2969
  · exact u2970
  · exact u2971

def b6686 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 40, targets := 321 },{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7),(3,0),(3,6),(3,8)], upper := (rows 97 134 268 168 336 34 81 145 273), lower := (rows 97 134 268 168 336 34 64 128 256), losses := [] }

theorem u6686 : Upper (D 9) (R 9) [96,132,264,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6686 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6687 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 134 268 168 336 48 67 131 259), lower := (rows 97 134 268 168 336 48 64 128 256), losses := [] }

theorem u6687 : Upper (D 9) (R 9) [96,132,264,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6687 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6688 : Route 9 := (fun mask => (mask,id))

def c6688 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6688 : Upper (D 9) (R 9) [96,132,288,144,320,1] 13 := by
  apply FastRouting.sound _ _ [96,132,288,144,320,1] 13 (by decide) (choices 1) [1,2,8] r6688 c6688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2972
  · exact u2973
  · exact u2974

theorem m6689_1 : Upper (D 9) (R 9) [96,132,288,144,320,2,1] 13 :=
  permutation_upper _ _ _ [96,132,288,144,320,1,8] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2974

def r6689 : Route 9 := (fun mask => (mask,id))

def c6689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6689 : Upper (D 9) (R 9) [96,132,288,144,320,2] 13 := by
  apply FastRouting.sound _ _ [96,132,288,144,320,2] 13 (by decide) (choices 1) [1,8] r6689 c6689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m6689_1
  · exact u2975

def b6690 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 2, region := 195, targets := 256 }], pairs := [(0,8),(1,6),(1,8),(2,6)], upper := (rows 97 134 292 152 336 40 67 131 259), lower := (rows 97 134 292 152 336 40 64 128 256), losses := [] }

theorem u6690 : Upper (D 9) (R 9) [96,132,288,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6690 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6691 : Route 9 := (fun mask => (mask,id))

def c6691 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6691 : Upper (D 9) (R 9) [96,132,288,192,264,1] 13 := by
  apply FastRouting.sound _ _ [96,132,288,192,264,1] 13 (by decide) (choices 1) [1,2,16] r6691 c6691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2976
  · exact u2977
  · exact u2978

theorem m6692_1 : Upper (D 9) (R 9) [96,132,288,192,264,2,1] 13 :=
  permutation_upper _ _ _ [96,132,288,192,264,1,16] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2978

def r6692 : Route 9 := (fun mask => (mask,id))

def c6692 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6692 : Upper (D 9) (R 9) [96,132,288,192,264,2] 13 := by
  apply FastRouting.sound _ _ [96,132,288,192,264,2] 13 (by decide) (choices 1) [1,16] r6692 c6692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m6692_1
  · exact u2979

def b6693 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 203, targets := 256 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8)], upper := (rows 97 134 292 200 280 48 67 131 259), lower := (rows 97 134 292 200 280 48 64 128 256), losses := [] }

theorem u6693 : Upper (D 9) (R 9) [96,132,288,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6693 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6694 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 23, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 11 21 104 112 416 448 384 384), lower := (rows 7 11 21 104 112 32 64 128 256), losses := [] }

theorem u6694 : Upper (D 9) (R 9) [6,9,17,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6694 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6695_128 : Upper (D 9) (R 9) [6,9,17,96,160,128] 13 :=
  permutation_upper _ _ _ [6,9,17,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2980

def r6695 : Route 9 := (fun mask => (mask,id))

def c6695 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6695 : Upper (D 9) (R 9) [6,9,17,96,160] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,160] 13 (by decide) (choices 1) [64,128,256] r6695 c6695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2980
  · exact m6695_128
  · exact u2981

def r6696 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6696 : Upper (D 9) (R 9) [6,9,17,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,384] 13 (by decide) (choices 1) [64,128] r6696 c6696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2982
  · exact u2983

def b6697 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 15, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 11 37 88 112 416 448 384 384), lower := (rows 7 11 37 88 112 32 64 128 256), losses := [] }

theorem u6697 : Upper (D 9) (R 9) [6,9,33,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6697 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6698 : Route 9 := (fun mask => (mask,id))

def c6698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6698 : Upper (D 9) (R 9) [6,9,33,80,160] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80,160] 13 (by decide) (choices 1) [64,128,256] r6698 c6698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2984
  · exact u2985
  · exact u2986

def b6699 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 423, targets := 64 },{ cop := 4, region := 8, targets := 160 }], pairs := [(0,6),(1,6),(2,6),(3,5),(3,7)], upper := (rows 7 11 37 88 208 416 480 416 416), lower := (rows 7 11 37 88 208 32 64 128 256), losses := [] }

theorem u6699 : Upper (D 9) (R 9) [6,9,33,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6699 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6700 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6700 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6700 : Upper (D 9) (R 9) [6,9,33,80,384] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80,384] 13 (by decide) (choices 1) [64,128] r6700 c6700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2987
  · exact u2988

def r6701 : Route 9 := (fun mask => (mask,id))

def c6701 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6701 : Upper (D 9) (R 9) [6,9,33,192,96] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,96] 13 (by decide) (choices 1) [16,128,256] r6701 c6701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2989
  · exact u2990
  · exact u2991

def b6702 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 16, targets := 288 },{ cop := 4, region := 8, targets := 32 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,8)], upper := (rows 7 11 37 200 208 304 368 432 304), lower := (rows 7 11 37 200 208 32 64 128 256), losses := [] }

theorem u6702 : Upper (D 9) (R 9) [6,9,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6702 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6703 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6703 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u6703 : Upper (D 9) (R 9) [6,9,33,192,288] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,288] 13 (by decide) (choices 1) [16,64,256] r6703 c6703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2992
  · exact u2993
  · exact u2994

def r6704 : Route 9 := (fun mask => (mask,id))

def c6704 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6704 : Upper (D 9) (R 9) [6,9,33,192,320] 13 := by
  apply FastRouting.sound _ _ [6,9,33,192,320] 13 (by decide) (choices 1) [16,128,256] r6704 c6704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2995
  · exact u2996
  · exact u2997

def b6705 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 23, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 11 52 104 81 416 448 384 384), lower := (rows 7 11 52 104 81 32 64 128 256), losses := [] }

theorem u6705 : Upper (D 9) (R 9) [6,9,48,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6705 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6706 : Route 9 := (fun mask => (mask,id))

def c6706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6706 : Upper (D 9) (R 9) [6,9,48,96,129] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,129] 13 (by decide) (choices 1) [64,128,256] r6706 c6706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2998
  · exact u2999
  · exact u3000

def r6707 : Route 9 := (fun mask => (mask,id))

def c6707 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6707 : Upper (D 9) (R 9) [6,9,48,96,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,192] 13 (by decide) (choices 1) [1,128,256] r6707 c6707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3001
  · exact u3002
  · exact u3003

def r6708 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6708 : Upper (D 9) (R 9) [6,9,48,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,384] 13 (by decide) (choices 1) [1,64,128] r6708 c6708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3004
  · exact u3005
  · exact u3006

def b6709 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 459, targets := 32 },{ cop := 4, region := 4, targets := 192 }], pairs := [(0,5),(1,5),(2,6),(2,7),(3,5)], upper := (rows 7 11 52 200 49 480 448 448 448), lower := (rows 7 11 52 200 49 32 64 128 256), losses := [] }

theorem u6709 : Upper (D 9) (R 9) [6,9,48,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6709 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6710 : Route 9 := (fun mask => (mask,id))

def c6710 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6710 : Upper (D 9) (R 9) [6,9,48,192,65] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,65] 13 (by decide) (choices 1) [128,256] r6710 c6710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3007
  · exact u3008

def b6711 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 4, targets := 449 },{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7),(2,8)], upper := (rows 7 11 52 200 112 417 449 385 385), lower := (rows 7 11 52 200 112 32 64 128 256), losses := [] }

theorem u6711 : Upper (D 9) (R 9) [6,9,48,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6711 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6712 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 16, targets := 289 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,8)], upper := (rows 7 11 52 200 208 289 353 417 289), lower := (rows 7 11 52 200 208 32 64 128 256), losses := [] }

theorem u6712 : Upper (D 9) (R 9) [6,9,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6712 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6713 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6713 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6713 : Upper (D 9) (R 9) [6,9,48,192,257] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,257] 13 (by decide) (choices 1) [64,256] r6713 c6713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3009
  · exact u3010

def b6714 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 4, targets := 449 },{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7),(2,8)], upper := (rows 7 11 52 200 304 481 449 449 449), lower := (rows 7 11 52 200 304 32 64 128 256), losses := [] }

theorem u6714 : Upper (D 9) (R 9) [6,9,48,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6714 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6715 : Route 9 := (fun mask => (mask,id))

def c6715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6715 : Upper (D 9) (R 9) [6,9,48,192,320] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320] 13 (by decide) (choices 1) [1,128,256] r6715 c6715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3011
  · exact u3012
  · exact u3013

def b6716 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 27, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 11 100 56 81 416 448 384 384), lower := (rows 7 11 100 56 81 32 64 128 256), losses := [] }

theorem u6716 : Upper (D 9) (R 9) [6,9,96,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6716 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6717 : Route 9 := (fun mask => (mask,id))

def c6717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6717 : Upper (D 9) (R 9) [6,9,96,48,129] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,129] 13 (by decide) (choices 1) [64,128,256] r6717 c6717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3014
  · exact u3015
  · exact u3016

def r6718 : Route 9 := (fun mask => (mask,id))

def c6718 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6718 : Upper (D 9) (R 9) [6,9,96,48,192] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,192] 13 (by decide) (choices 1) [1,128,256] r6718 c6718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3017
  · exact u3018
  · exact u3019

def r6719 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6719 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6719 : Upper (D 9) (R 9) [6,9,96,48,384] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,384] 13 (by decide) (choices 1) [1,64,128] r6719 c6719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3020
  · exact u3021
  · exact u3022

#print axioms u6719
end Delivery.IrregularNine14.P09
