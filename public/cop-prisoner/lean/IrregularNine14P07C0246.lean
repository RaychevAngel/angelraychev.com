import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0043
import IrregularNine14P07C0044

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14760 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 259 100 42 88 48 193 129 385), lower := (rows 7 259 100 42 88 48 64 128 256), losses := [] }

theorem u14760 : Upper (D 7) (R 7) [6,257,96,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14760 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14761 : Route 9 := (fun mask => (mask,id))

def c14761 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14761 : Upper (D 7) (R 7) [6,257,96,34,72,128] 13 := by
  apply FastRouting.sound _ _ [6,257,96,34,72,128] 13 (by decide) (choices 1) [1,16,128] r14761 c14761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2635
  · exact u2636
  · exact u2637

def b14762 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 7 259 100 42 145 40 208 208 464), lower := (rows 7 259 100 42 145 40 64 128 256), losses := [] }

theorem u14762 : Upper (D 7) (R 7) [6,257,96,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14762 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14763 : Route 9 := (fun mask => (mask,id))

def c14763 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14763 : Upper (D 7) (R 7) [6,257,96,34,129,16] 13 := by
  apply FastRouting.sound _ _ [6,257,96,34,129,16] 13 (by decide) (choices 1) [8,128] r14763 c14763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2638
  · exact u2639

def b14764 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 42 145 96 216 152 408), lower := (rows 7 259 100 42 145 96 64 128 256), losses := [] }

theorem u14764 : Upper (D 7) (R 7) [6,257,96,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14765 : Route 9 := (fun mask => (mask,id))

def c14765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14765 : Upper (D 7) (R 7) [6,257,96,34,129,128] 13 := by
  apply FastRouting.sound _ _ [6,257,96,34,129,128] 13 (by decide) (choices 1) [8,16] r14765 c14765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2640
  · exact u2641

def b14766 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 212, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 100 42 152 33 208 208 464), lower := (rows 7 259 100 42 152 33 64 128 256), losses := [] }

theorem u14766 : Upper (D 7) (R 7) [6,257,96,34,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14767 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 387, targets := 32 }], pairs := [(0,5),(1,5),(2,1)], upper := (rows 7 259 100 42 152 48 193 193 449), lower := (rows 7 259 100 42 152 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 56 67 131 259), good := (rows 453 449 100 508 188 48 64 128 256) }] }

theorem u14767 : Upper (D 7) (R 7) [6,257,96,34,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14767 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14768 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 42 152 96 209 145 401), lower := (rows 7 259 100 42 152 96 64 128 256), losses := [] }

theorem u14768 : Upper (D 7) (R 7) [6,257,96,34,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14769 : Route 9 := (fun mask => (mask,id))

def c14769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14769 : Upper (D 7) (R 7) [6,257,96,34,136,128] 13 := by
  apply FastRouting.sound _ _ [6,257,96,34,136,128] 13 (by decide) (choices 1) [1,16] r14769 c14769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2642
  · exact u2643

def b14770 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 212, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 100 42 208 33 216 152 408), lower := (rows 7 259 100 42 208 33 64 128 256), losses := [] }

theorem u14770 : Upper (D 7) (R 7) [6,257,96,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14771 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 7 259 100 42 208 40 209 145 401), lower := (rows 7 259 100 42 208 40 64 128 256), losses := [] }

theorem u14771 : Upper (D 7) (R 7) [6,257,96,34,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14771 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14772 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 259 100 42 208 48 201 137 393), lower := (rows 7 259 100 42 208 48 64 128 256), losses := [] }

theorem u14772 : Upper (D 7) (R 7) [6,257,96,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14772 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14773 : Route 9 := (fun mask => (mask,id))

def c14773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14773 : Upper (D 7) (R 7) [6,257,96,34,192,128] 13 := by
  apply FastRouting.sound _ _ [6,257,96,34,192,128] 13 (by decide) (choices 1) [1,8,16] r14773 c14773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2644
  · exact u2645
  · exact u2646

def b14774 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,6)], upper := (rows 7 259 100 56 145 34 200 200 456), lower := (rows 7 259 100 56 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 16 35 88 152 280), good := (rows 38 290 100 508 508 34 64 128 256) },{ target := 6, region := (rows 1 2 4 24 16 35 0 128 256), good := (rows 39 291 36 56 185 34 0 128 256) }] }

theorem u14774 : Upper (D 7) (R 7) [6,257,96,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14775 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 259 100 56 145 40 194 194 450), lower := (rows 7 259 100 56 145 40 64 128 256), losses := [] }

theorem u14775 : Upper (D 7) (R 7) [6,257,96,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14775 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14776 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 56 145 96 202 138 394), lower := (rows 7 259 100 56 145 96 64 128 256), losses := [] }

theorem u14776 : Upper (D 7) (R 7) [6,257,96,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14777 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 259 100 56 145 160 74 202 330), lower := (rows 7 259 100 56 145 160 64 128 256), losses := [] }

theorem u14777 : Upper (D 7) (R 7) [6,257,96,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14778 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(4,0)], upper := (rows 7 259 100 56 146 33 200 200 456), lower := (rows 7 259 100 56 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 40 17 32 108 172 300), good := (rows 470 274 492 508 146 508 64 128 256) }] }

theorem u14778 : Upper (D 7) (R 7) [6,257,96,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14779 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 259 100 56 146 40 193 193 449), lower := (rows 7 259 100 56 146 40 64 128 256), losses := [] }

theorem u14779 : Upper (D 7) (R 7) [6,257,96,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14779 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14780 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 56 146 96 201 137 393), lower := (rows 7 259 100 56 146 96 64 128 256), losses := [] }

theorem u14780 : Upper (D 7) (R 7) [6,257,96,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14781 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 259 100 56 146 160 73 201 329), lower := (rows 7 259 100 56 146 160 64 128 256), losses := [] }

theorem u14781 : Upper (D 7) (R 7) [6,257,96,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14782 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 387, targets := 32 }], pairs := [(0,5),(1,5),(2,0),(3,0)], upper := (rows 7 259 100 56 152 33 194 194 450), lower := (rows 7 259 100 56 152 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 49 32 67 131 259), good := (rows 478 466 124 60 152 508 64 128 256) }] }

theorem u14782 : Upper (D 7) (R 7) [6,257,96,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14783 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 387, targets := 32 }], pairs := [(0,5),(1,5),(2,1),(3,1)], upper := (rows 7 259 100 56 152 34 193 193 449), lower := (rows 7 259 100 56 152 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 36 44 49 32 67 131 259), good := (rows 477 465 124 60 152 508 64 128 256) }] }

theorem u14783 : Upper (D 7) (R 7) [6,257,96,48,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14784 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 56 152 96 195 131 387), lower := (rows 7 259 100 56 152 96 64 128 256), losses := [] }

theorem u14784 : Upper (D 7) (R 7) [6,257,96,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14785 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6),(4,0)], upper := (rows 7 259 100 56 152 160 67 195 323), lower := (rows 7 259 100 56 152 160 64 128 256), losses := [] }

theorem u14785 : Upper (D 7) (R 7) [6,257,96,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14786 : Route 9 := (fun mask => (mask,id))

def c14786 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14786 : Upper (D 7) (R 7) [6,257,96,48,192,1] 13 := by
  apply FastRouting.sound _ _ [6,257,96,48,192,1] 13 (by decide) (choices 1) [2,8,128] r14786 c14786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2647
  · exact u2648
  · exact u2649

def r14787 : Route 9 := (fun mask => (mask,id))

def c14787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14787 : Upper (D 7) (R 7) [6,257,96,48,192,2] 13 := by
  apply FastRouting.sound _ _ [6,257,96,48,192,2] 13 (by decide) (choices 1) [1,8,128] r14787 c14787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2650
  · exact u2651
  · exact u2652

def b14788 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 44, targets := 131 }], pairs := [(2,0),(2,1),(2,7)], upper := (rows 7 259 100 56 208 40 195 131 387), lower := (rows 7 259 100 56 208 40 64 128 256), losses := [] }

theorem u14788 : Upper (D 7) (R 7) [6,257,96,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14788 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14789 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 259 100 56 208 160 75 139 267), lower := (rows 7 259 100 56 208 160 64 128 256), losses := [] }

theorem u14789 : Upper (D 7) (R 7) [6,257,96,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14790 : Route 9 := (fun mask => (mask,id))

def c14790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14790 : Upper (D 7) (R 7) [6,257,96,129,130,8] 13 := by
  apply FastRouting.sound _ _ [6,257,96,129,130,8] 13 (by decide) (choices 1) [16,32] r14790 c14790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2653
  · exact u2654

theorem m14791_8 : Upper (D 7) (R 7) [6,257,96,129,130,16,8] 13 :=
  permutation_upper _ _ _ [6,257,96,129,130,8,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2653

def r14791 : Route 9 := (fun mask => (mask,id))

def c14791 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14791 : Upper (D 7) (R 7) [6,257,96,129,130,16] 13 := by
  apply FastRouting.sound _ _ [6,257,96,129,130,16] 13 (by decide) (choices 1) [8,32] r14791 c14791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14791_8
  · exact u2655

def b14792 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 137 146 96 120 184 312), lower := (rows 7 259 100 137 146 96 64 128 256), losses := [] }

theorem u14792 : Upper (D 7) (R 7) [6,257,96,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14793 : PairBound 9 := { available := 88, camps := [], pairs := [(2,0),(2,1),(3,1),(4,0)], upper := (rows 7 259 100 137 176 34 88 216 344), lower := (rows 7 259 100 137 176 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 35 72 136 264), good := (rows 38 290 100 508 176 34 64 128 256) },{ target := 1, region := (rows 1 0 52 11 52 32 97 161 289), good := (rows 477 457 500 457 500 508 64 128 256) }] }

theorem u14793 : Upper (D 7) (R 7) [6,257,96,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14794 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 259 100 137 176 40 82 210 338), lower := (rows 7 259 100 137 176 40 64 128 256), losses := [] }

theorem u14794 : Upper (D 7) (R 7) [6,257,96,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14794 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14795 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 259 100 137 176 48 74 202 330), lower := (rows 7 259 100 137 176 48 64 128 256), losses := [] }

theorem u14795 : Upper (D 7) (R 7) [6,257,96,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14795 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14796 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 137 176 96 90 154 282), lower := (rows 7 259 100 137 176 96 64 128 256), losses := [] }

theorem u14796 : Upper (D 7) (R 7) [6,257,96,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14797 : PairBound 9 := { available := 88, camps := [], pairs := [(2,0),(2,1),(3,0),(4,0)], upper := (rows 7 259 100 138 176 33 88 216 344), lower := (rows 7 259 100 138 176 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 52 11 52 32 97 161 289), good := (rows 478 458 500 138 500 508 64 128 256) },{ target := 1, region := (rows 1 0 12 8 24 35 72 136 264), good := (rows 37 289 100 508 176 33 64 128 256) }] }

theorem u14797 : Upper (D 7) (R 7) [6,257,96,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14798 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 259 100 138 176 40 81 209 337), lower := (rows 7 259 100 138 176 40 64 128 256), losses := [] }

theorem u14798 : Upper (D 7) (R 7) [6,257,96,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14798 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14799 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 259 100 138 176 48 73 201 329), lower := (rows 7 259 100 138 176 48 64 128 256), losses := [] }

theorem u14799 : Upper (D 7) (R 7) [6,257,96,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14799 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14800 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 259 100 138 176 96 89 153 281), lower := (rows 7 259 100 138 176 96 64 128 256), losses := [] }

theorem u14800 : Upper (D 7) (R 7) [6,257,96,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14801 : Route 9 := (fun mask => (mask,id))

def c14801 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14801 : Upper (D 7) (R 7) [6,257,96,160,192,1] 13 := by
  apply FastRouting.sound _ _ [6,257,96,160,192,1] 13 (by decide) (choices 1) [2,8,16] r14801 c14801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2656
  · exact u2657
  · exact u2658

theorem m14802_1 : Upper (D 7) (R 7) [6,257,96,160,192,2,1] 13 :=
  permutation_upper _ _ _ [6,257,96,160,192,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2656

def r14802 : Route 9 := (fun mask => (mask,id))

def c14802 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14802 : Upper (D 7) (R 7) [6,257,96,160,192,2] 13 := by
  apply FastRouting.sound _ _ [6,257,96,160,192,2] 13 (by decide) (choices 1) [1,8,16] r14802 c14802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m14802_1
  · exact u2659
  · exact u2660

def b14803 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 259 100 168 208 40 83 147 275), lower := (rows 7 259 100 168 208 40 64 128 256), losses := [] }

theorem u14803 : Upper (D 7) (R 7) [6,257,96,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14803 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14804 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 259 100 168 208 48 75 139 267), lower := (rows 7 259 100 168 208 48 64 128 256), losses := [] }

theorem u14804 : Upper (D 7) (R 7) [6,257,96,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14804 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14805 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 40, targets := 192 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,6),(3,7),(4,0)], upper := (rows 7 266 21 41 112 34 192 192 448), lower := (rows 7 266 21 41 112 34 64 128 256), losses := [] }

theorem u14805 : Upper (D 7) (R 7) [6,264,17,33,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14805 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14806 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 7 266 21 41 112 96 194 130 386), lower := (rows 7 266 21 41 112 96 64 128 256), losses := [] }

theorem u14806 : Upper (D 7) (R 7) [6,264,17,33,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14807 : Route 9 := (fun mask => (mask,id))

def c14807 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14807 : Upper (D 7) (R 7) [6,264,17,33,96,128] 13 := by
  apply FastRouting.sound _ _ [6,264,17,33,96,128] 13 (by decide) (choices 1) [2,128] r14807 c14807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2661
  · exact u2662

def b14808 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 40, targets := 192 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,6),(3,7),(4,0)], upper := (rows 7 266 21 41 208 34 224 224 480), lower := (rows 7 266 21 41 208 34 64 128 256), losses := [] }

theorem u14808 : Upper (D 7) (R 7) [6,264,17,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14809 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 466, targets := 1 },{ cop := 3, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,1),(4,0)], upper := (rows 7 266 21 41 208 96 226 162 418), lower := (rows 7 266 21 41 208 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 16 112 64 128 256), good := (rows 13 264 61 41 240 96 96 128 256) }] }

theorem u14809 : Upper (D 7) (R 7) [6,264,17,33,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14810 : PairBound 9 := { available := 192, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 266 21 42 112 33 192 192 448), lower := (rows 7 266 21 42 112 33 64 128 256), losses := [] }

theorem u14810 : Upper (D 7) (R 7) [6,264,17,34,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14811 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 7 266 21 42 112 96 193 129 385), lower := (rows 7 266 21 42 112 96 64 128 256), losses := [] }

theorem u14811 : Upper (D 7) (R 7) [6,264,17,34,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14812 : Route 9 := (fun mask => (mask,id))

def c14812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14812 : Upper (D 7) (R 7) [6,264,17,34,96,128] 13 := by
  apply FastRouting.sound _ _ [6,264,17,34,96,128] 13 (by decide) (choices 1) [1,128] r14812 c14812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2663
  · exact u2664

def b14813 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 266 21 42 208 33 224 224 480), lower := (rows 7 266 21 42 208 33 64 128 256), losses := [] }

theorem u14813 : Upper (D 7) (R 7) [6,264,17,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14814 : Route 9 := (fun mask => (mask,id))

def c14814 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14814 : Upper (D 7) (R 7) [6,264,17,34,192,64] 13 := by
  apply FastRouting.sound _ _ [6,264,17,34,192,64] 13 (by decide) (choices 1) [1,32,128] r14814 c14814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2665
  · exact u2666
  · exact u2667

def b14815 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 3, region := 386, targets := 32 }], pairs := [(1,0),(1,5),(3,0),(4,0)], upper := (rows 7 266 21 104 176 33 194 194 450), lower := (rows 7 266 21 104 176 33 64 128 256), losses := [] }

theorem u14815 : Upper (D 7) (R 7) [6,264,17,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14816 : Route 9 := (fun mask => (mask,id))

def c14816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14816 : Upper (D 7) (R 7) [6,264,17,96,160,2] 13 := by
  apply FastRouting.sound _ _ [6,264,17,96,160,2] 13 (by decide) (choices 1) [1,128] r14816 c14816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2668
  · exact u2669

def b14817 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 266 21 104 176 96 195 131 387), lower := (rows 7 266 21 104 176 96 64 128 256), losses := [] }

theorem u14817 : Upper (D 7) (R 7) [6,264,17,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14818 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 266 21 104 176 160 67 195 323), lower := (rows 7 266 21 104 176 160 64 128 256), losses := [] }

theorem u14818 : Upper (D 7) (R 7) [6,264,17,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14819 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 3, region := 482, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 7 266 37 25 82 96 224 160 416), lower := (rows 7 266 37 25 82 96 64 128 256), losses := [] }

theorem u14819 : Upper (D 7) (R 7) [6,264,33,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u14819
end Delivery.IrregularNine14.P07
