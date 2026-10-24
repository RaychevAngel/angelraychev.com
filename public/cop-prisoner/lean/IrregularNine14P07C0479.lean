import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0181

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28740 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 262 7 25 176 160 74 202 330), lower := (rows 97 262 7 25 176 160 64 128 256), losses := [] }

theorem u28740 : Upper (D 7) (R 7) [96,260,3,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28741 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1),(1,0),(4,1)], upper := (rows 97 262 7 26 145 40 224 224 480), lower := (rows 97 262 7 26 145 40 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 40 105 169 297), good := (rows 480 262 454 506 464 488 64 128 256) }] }

theorem u28741 : Upper (D 7) (R 7) [96,260,3,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28741 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28742 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 26 145 96 232 168 424), lower := (rows 97 262 7 26 145 96 64 128 256), losses := [] }

theorem u28742 : Upper (D 7) (R 7) [96,260,3,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28743_8 : Upper (D 7) (R 7) [96,260,3,18,129,128,8] 13 :=
  permutation_upper _ _ _ [96,260,3,18,129,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10864

theorem m28743_32 : Upper (D 7) (R 7) [96,260,3,18,129,128,32] 13 :=
  permutation_upper _ _ _ [96,260,3,18,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10865

def r28743 : Route 9 := (fun mask => (mask,id))

def c28743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28743 : Upper (D 7) (R 7) [96,260,3,18,129,128] 13 := by
  apply FastRouting.sound _ _ [96,260,3,18,129,128] 13 (by decide) (choices 1) [8,32] r28743 c28743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28743_8
  · exact m28743_32

def b28744 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 241, targets := 2 },{ cop := 6, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(4,1)], upper := (rows 97 262 7 26 152 33 224 224 480), lower := (rows 97 262 7 26 152 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 14 20 32 97 161 289), good := (rows 480 286 478 26 152 480 64 128 256) }] }

theorem u28744 : Upper (D 7) (R 7) [96,260,3,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28745 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 26 152 96 225 161 417), lower := (rows 97 262 7 26 152 96 64 128 256), losses := [] }

theorem u28745 : Upper (D 7) (R 7) [96,260,3,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28746 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 3, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 97 262 7 26 152 160 97 225 353), lower := (rows 97 262 7 26 152 160 64 128 256), losses := [] }

theorem u28746 : Upper (D 7) (R 7) [96,260,3,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28747 : Route 9 := (fun mask => (mask,id))

def c28747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28747 : Upper (D 7) (R 7) [96,260,3,18,160,1] 13 := by
  apply FastRouting.sound _ _ [96,260,3,18,160,1] 13 (by decide) (choices 1) [8,128] r28747 c28747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10866
  · exact u10867

def b28748 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 3, region := 225, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 97 262 7 26 176 40 193 193 449), lower := (rows 97 262 7 26 176 40 64 128 256), losses := [] }

theorem u28748 : Upper (D 7) (R 7) [96,260,3,18,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28748 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28749 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 26 176 96 201 137 393), lower := (rows 97 262 7 26 176 96 64 128 256), losses := [] }

theorem u28749 : Upper (D 7) (R 7) [96,260,3,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28750 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 262 7 26 176 160 73 201 329), lower := (rows 97 262 7 26 176 160 64 128 256), losses := [] }

theorem u28750 : Upper (D 7) (R 7) [96,260,3,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28751 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 40, targets := 192 },{ cop := 3, region := 208, targets := 33 }], pairs := [(3,6),(3,7),(4,0),(4,5)], upper := (rows 97 262 7 42 88 33 208 144 400), lower := (rows 97 262 7 42 88 33 64 128 256), losses := [] }

theorem u28751 : Upper (D 7) (R 7) [96,260,3,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28752 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 7 42 88 48 193 129 385), lower := (rows 97 262 7 42 88 48 64 128 256), losses := [] }

theorem u28752 : Upper (D 7) (R 7) [96,260,3,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28752 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28753 : Route 9 := (fun mask => (mask,id))

def c28753 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28753 : Upper (D 7) (R 7) [96,260,3,34,72,128] 13 := by
  apply FastRouting.sound _ _ [96,260,3,34,72,128] 13 (by decide) (choices 1) [1,16,128] r28753 c28753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10868
  · exact u10869
  · exact u10870

def b28754 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 7 42 145 40 208 208 464), lower := (rows 97 262 7 42 145 40 64 128 256), losses := [] }

theorem u28754 : Upper (D 7) (R 7) [96,260,3,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28754 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28755 : Route 9 := (fun mask => (mask,id))

def c28755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28755 : Upper (D 7) (R 7) [96,260,3,34,129,16] 13 := by
  apply FastRouting.sound _ _ [96,260,3,34,129,16] 13 (by decide) (choices 1) [8,128] r28755 c28755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10871
  · exact u10872

def b28756 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 42 145 96 216 152 408), lower := (rows 97 262 7 42 145 96 64 128 256), losses := [] }

theorem u28756 : Upper (D 7) (R 7) [96,260,3,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28757 : Route 9 := (fun mask => (mask,id))

def c28757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28757 : Upper (D 7) (R 7) [96,260,3,34,129,128] 13 := by
  apply FastRouting.sound _ _ [96,260,3,34,129,128] 13 (by decide) (choices 1) [8,16] r28757 c28757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10873
  · exact u10874

def b28758 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 40, targets := 192 },{ cop := 3, region := 208, targets := 33 }], pairs := [(3,6),(3,7),(4,0),(4,5)], upper := (rows 97 262 7 42 152 33 208 208 464), lower := (rows 97 262 7 42 152 33 64 128 256), losses := [] }

theorem u28758 : Upper (D 7) (R 7) [96,260,3,34,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28759 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 3, region := 193, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 97 262 7 42 152 48 193 193 449), lower := (rows 97 262 7 42 152 48 64 128 256), losses := [] }

theorem u28759 : Upper (D 7) (R 7) [96,260,3,34,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28759 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28760 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 42 152 96 209 145 401), lower := (rows 97 262 7 42 152 96 64 128 256), losses := [] }

theorem u28760 : Upper (D 7) (R 7) [96,260,3,34,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28761 : Route 9 := (fun mask => (mask,id))

def c28761 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28761 : Upper (D 7) (R 7) [96,260,3,34,136,128] 13 := by
  apply FastRouting.sound _ _ [96,260,3,34,136,128] 13 (by decide) (choices 1) [1,16] r28761 c28761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10875
  · exact u10876

def b28762 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 40, targets := 192 },{ cop := 3, region := 208, targets := 33 }], pairs := [(3,6),(3,7),(4,0),(4,5)], upper := (rows 97 262 7 42 208 33 216 152 408), lower := (rows 97 262 7 42 208 33 64 128 256), losses := [] }

theorem u28762 : Upper (D 7) (R 7) [96,260,3,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28763 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 7 42 208 40 209 145 401), lower := (rows 97 262 7 42 208 40 64 128 256), losses := [] }

theorem u28763 : Upper (D 7) (R 7) [96,260,3,34,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28763 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28764 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 7 42 208 48 201 137 393), lower := (rows 97 262 7 42 208 48 64 128 256), losses := [] }

theorem u28764 : Upper (D 7) (R 7) [96,260,3,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28764 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28765 : Route 9 := (fun mask => (mask,id))

def c28765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28765 : Upper (D 7) (R 7) [96,260,3,34,192,128] 13 := by
  apply FastRouting.sound _ _ [96,260,3,34,192,128] 13 (by decide) (choices 1) [1,8,16] r28765 c28765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10877
  · exact u10878
  · exact u10879

def r28766 : Route 9 := (fun mask => (mask,id))

def c28766 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28766 : Upper (D 7) (R 7) [96,260,3,48,129,2] 13 := by
  apply FastRouting.sound _ _ [96,260,3,48,129,2] 13 (by decide) (choices 1) [8,128] r28766 c28766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10880
  · exact u10881

def b28767 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 97 262 7 56 145 40 194 194 450), lower := (rows 97 262 7 56 145 40 64 128 256), losses := [] }

theorem u28767 : Upper (D 7) (R 7) [96,260,3,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28767 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28768 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 56 145 96 202 138 394), lower := (rows 97 262 7 56 145 96 64 128 256), losses := [] }

theorem u28768 : Upper (D 7) (R 7) [96,260,3,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28769 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 262 7 56 145 160 74 202 330), lower := (rows 97 262 7 56 145 160 64 128 256), losses := [] }

theorem u28769 : Upper (D 7) (R 7) [96,260,3,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28770 : Route 9 := (fun mask => (mask,id))

def c28770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28770 : Upper (D 7) (R 7) [96,260,3,48,130,1] 13 := by
  apply FastRouting.sound _ _ [96,260,3,48,130,1] 13 (by decide) (choices 1) [8,128] r28770 c28770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10882
  · exact u10883

def b28771 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 7 56 146 40 193 193 449), lower := (rows 97 262 7 56 146 40 64 128 256), losses := [] }

theorem u28771 : Upper (D 7) (R 7) [96,260,3,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28771 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28772 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 56 146 96 201 137 393), lower := (rows 97 262 7 56 146 96 64 128 256), losses := [] }

theorem u28772 : Upper (D 7) (R 7) [96,260,3,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28773 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 262 7 56 146 160 73 201 329), lower := (rows 97 262 7 56 146 160 64 128 256), losses := [] }

theorem u28773 : Upper (D 7) (R 7) [96,260,3,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28774 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,5),(2,5)], upper := (rows 97 262 7 56 152 33 194 194 450), lower := (rows 97 262 7 56 152 33 64 128 256), losses := [] }

theorem u28774 : Upper (D 7) (R 7) [96,260,3,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28775 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 217, targets := 2 },{ cop := 0, region := 390, targets := 32 }], pairs := [(0,1),(1,5),(3,1),(4,1)], upper := (rows 97 262 7 56 152 34 193 193 449), lower := (rows 97 262 7 56 152 34 64 128 256), losses := [] }

theorem u28775 : Upper (D 7) (R 7) [96,260,3,48,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28776 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 56 152 96 195 131 387), lower := (rows 97 262 7 56 152 96 64 128 256), losses := [] }

theorem u28776 : Upper (D 7) (R 7) [96,260,3,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28777 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6),(4,0)], upper := (rows 97 262 7 56 152 160 67 195 323), lower := (rows 97 262 7 56 152 160 64 128 256), losses := [] }

theorem u28777 : Upper (D 7) (R 7) [96,260,3,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28778 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 262 7 56 208 33 202 138 394), lower := (rows 97 262 7 56 208 33 64 128 256), losses := [] }

theorem u28778 : Upper (D 7) (R 7) [96,260,3,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28779 : Route 9 := (fun mask => (mask,id))

def c28779 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28779 : Upper (D 7) (R 7) [96,260,3,48,192,2] 13 := by
  apply FastRouting.sound _ _ [96,260,3,48,192,2] 13 (by decide) (choices 1) [1,8,128] r28779 c28779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10884
  · exact u10885
  · exact u10886

def b28780 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 262 7 56 208 40 195 131 387), lower := (rows 97 262 7 56 208 40 64 128 256), losses := [] }

theorem u28780 : Upper (D 7) (R 7) [96,260,3,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28780 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28781 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 262 7 56 208 160 75 139 267), lower := (rows 97 262 7 56 208 160 64 128 256), losses := [] }

theorem u28781 : Upper (D 7) (R 7) [96,260,3,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28782 : Route 9 := (fun mask => (mask,id))

def c28782 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28782 : Upper (D 7) (R 7) [96,260,3,129,130,8] 13 := by
  apply FastRouting.sound _ _ [96,260,3,129,130,8] 13 (by decide) (choices 1) [16,32] r28782 c28782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10887
  · exact u10888

theorem m28783_8 : Upper (D 7) (R 7) [96,260,3,129,130,16,8] 13 :=
  permutation_upper _ _ _ [96,260,3,129,130,8,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10887

def r28783 : Route 9 := (fun mask => (mask,id))

def c28783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28783 : Upper (D 7) (R 7) [96,260,3,129,130,16] 13 := by
  apply FastRouting.sound _ _ [96,260,3,129,130,16] 13 (by decide) (choices 1) [8,32] r28783 c28783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28783_8
  · exact u10889

def b28784 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 137 146 96 120 184 312), lower := (rows 97 262 7 137 146 96 64 128 256), losses := [] }

theorem u28784 : Upper (D 7) (R 7) [96,260,3,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28785 : Route 9 := (fun mask => (mask,id))

def c28785 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28785 : Upper (D 7) (R 7) [96,260,3,129,160,2] 13 := by
  apply FastRouting.sound _ _ [96,260,3,129,160,2] 13 (by decide) (choices 1) [8,16] r28785 c28785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10890
  · exact u10891

def b28786 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 97 262 7 137 176 40 82 210 338), lower := (rows 97 262 7 137 176 40 64 128 256), losses := [] }

theorem u28786 : Upper (D 7) (R 7) [96,260,3,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28786 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28787 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 7 137 176 48 74 202 330), lower := (rows 97 262 7 137 176 48 64 128 256), losses := [] }

theorem u28787 : Upper (D 7) (R 7) [96,260,3,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28787 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28788 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 137 176 96 90 154 282), lower := (rows 97 262 7 137 176 96 64 128 256), losses := [] }

theorem u28788 : Upper (D 7) (R 7) [96,260,3,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28789 : Route 9 := (fun mask => (mask,id))

def c28789 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28789 : Upper (D 7) (R 7) [96,260,3,130,160,1] 13 := by
  apply FastRouting.sound _ _ [96,260,3,130,160,1] 13 (by decide) (choices 1) [8,16] r28789 c28789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10892
  · exact u10893

def b28790 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 262 7 138 176 40 81 209 337), lower := (rows 97 262 7 138 176 40 64 128 256), losses := [] }

theorem u28790 : Upper (D 7) (R 7) [96,260,3,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28790 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28791 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 7 138 176 48 73 201 329), lower := (rows 97 262 7 138 176 48 64 128 256), losses := [] }

theorem u28791 : Upper (D 7) (R 7) [96,260,3,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28791 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28792 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 7 138 176 96 89 153 281), lower := (rows 97 262 7 138 176 96 64 128 256), losses := [] }

theorem u28792 : Upper (D 7) (R 7) [96,260,3,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28793 : Route 9 := (fun mask => (mask,id))

def c28793 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28793 : Upper (D 7) (R 7) [96,260,3,160,192,1] 13 := by
  apply FastRouting.sound _ _ [96,260,3,160,192,1] 13 (by decide) (choices 1) [2,8,16] r28793 c28793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10894
  · exact u10895
  · exact u10896

theorem m28794_1 : Upper (D 7) (R 7) [96,260,3,160,192,2,1] 13 :=
  permutation_upper _ _ _ [96,260,3,160,192,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10894

def r28794 : Route 9 := (fun mask => (mask,id))

def c28794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28794 : Upper (D 7) (R 7) [96,260,3,160,192,2] 13 := by
  apply FastRouting.sound _ _ [96,260,3,160,192,2] 13 (by decide) (choices 1) [1,8,16] r28794 c28794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m28794_1
  · exact u10897
  · exact u10898

def b28795 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 262 7 168 208 40 83 147 275), lower := (rows 97 262 7 168 208 40 64 128 256), losses := [] }

theorem u28795 : Upper (D 7) (R 7) [96,260,3,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28795 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28796 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 7 168 208 48 75 139 267), lower := (rows 97 262 7 168 208 48 64 128 256), losses := [] }

theorem u28796 : Upper (D 7) (R 7) [96,260,3,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28796 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28797 : Route 9 := (fun mask => (mask,id))

def c28797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u28797 : Upper (D 7) (R 7) [96,260,9,18,129,2] 13 := by
  apply FastRouting.sound _ _ [96,260,9,18,129,2] 13 (by decide) (choices 1) [32,128] r28797 c28797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10899
  · exact u10900

def b28798 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 13 26 145 96 226 162 418), lower := (rows 97 262 13 26 145 96 64 128 256), losses := [] }

theorem u28798 : Upper (D 7) (R 7) [96,260,9,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m28799_2 : Upper (D 7) (R 7) [96,260,9,18,129,128,2] 13 :=
  permutation_upper _ _ _ [96,260,9,18,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10900

theorem m28799_32 : Upper (D 7) (R 7) [96,260,9,18,129,128,32] 13 :=
  permutation_upper _ _ _ [96,260,9,18,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u10901

def r28799 : Route 9 := (fun mask => (mask,id))

def c28799 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28799 : Upper (D 7) (R 7) [96,260,9,18,129,128] 13 := by
  apply FastRouting.sound _ _ [96,260,9,18,129,128] 13 (by decide) (choices 1) [2,32] r28799 c28799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m28799_2
  · exact m28799_32

#print axioms u28799
end Delivery.IrregularNine14.P07
