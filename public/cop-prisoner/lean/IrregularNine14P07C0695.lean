import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0545
import IrregularNine14P07C0546
import IrregularNine14P07C0547
import IrregularNine14P07C0548
import IrregularNine14P07C0549
import IrregularNine14P07C0550

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b41700 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 50 38 74 465 481 449 449 449), lower := (rows 13 50 38 74 16 32 64 128 256), losses := [] }

theorem u41700 : Upper (D 7) (R 7) [12,48,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41701 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 50 38 200 467 483 451 451 451), lower := (rows 13 50 38 200 16 32 64 128 256), losses := [] }

theorem u41701 : Upper (D 7) (R 7) [12,48,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41702 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 50 38 265 211 227 195 195 451), lower := (rows 13 50 38 265 16 32 64 128 256), losses := [] }

theorem u41702 : Upper (D 7) (R 7) [12,48,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41703 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 50 38 266 209 225 193 193 449), lower := (rows 13 50 38 266 16 32 64 128 256), losses := [] }

theorem u41703 : Upper (D 7) (R 7) [12,48,34,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41704 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 4, targets := 193 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(2,0),(2,6),(2,7)], upper := (rows 13 50 38 328 211 227 195 195 451), lower := (rows 13 50 38 328 16 32 64 128 256), losses := [] }

theorem u41704 : Upper (D 7) (R 7) [12,48,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41705 : PairBound 9 := { available := 418, camps := [{ cop := 6, region := 13, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 50 69 73 434 418 482 418 418), lower := (rows 13 50 69 73 16 32 64 128 256), losses := [] }

theorem u41705 : Upper (D 7) (R 7) [12,48,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41706 : PairBound 9 := { available := 419, camps := [{ cop := 3, region := 5, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 50 69 74 435 419 483 419 419), lower := (rows 13 50 69 74 16 32 64 128 256), losses := [] }

theorem u41706 : Upper (D 7) (R 7) [12,48,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41707 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 5, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 50 69 104 403 419 451 387 387), lower := (rows 13 50 69 104 16 32 64 128 256), losses := [] }

theorem u41707 : Upper (D 7) (R 7) [12,48,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41708_130 : Upper (D 7) (R 7) [12,48,65,129,130] 13 :=
  permutation_upper _ _ _ [12,48,65,129,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32756

theorem m41708_160 : Upper (D 7) (R 7) [12,48,65,129,160] 13 :=
  permutation_upper _ _ _ [12,48,65,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32757

theorem m41708_384 : Upper (D 7) (R 7) [12,48,65,129,384] 13 :=
  permutation_upper _ _ _ [12,48,65,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32761

def r41708 : Route 9 := (fun mask => (mask,id))

def c41708 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41708 : Upper (D 7) (R 7) [12,48,65,129] 13 := by
  apply FastRouting.sound _ _ [12,48,65,129] 13 (by decide) (choices 2) [34,66,96,130,160,192,258,288,320,384] r41708 c41708
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32755
  · exact u32756
  · exact u32757
  · exact m41708_130
  · exact m41708_160
  · exact u32758
  · exact u32759
  · exact u32760
  · exact u32761
  · exact m41708_384

def r41709 : Route 9 := (fun mask => (mask,id))

def c41709 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41709 : Upper (D 7) (R 7) [12,48,65,130] 13 := by
  apply FastRouting.sound _ _ [12,48,65,130] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r41709 c41709
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32762
  · exact u32763
  · exact u32764
  · exact u32765
  · exact u32766
  · exact u32767
  · exact u32768
  · exact u32769
  · exact u32770
  · exact u32771
  · exact u32772
  · exact u32773
  · exact u32774
  · exact u32775
  · exact u32776

def r41710 : Route 9 := (fun mask => (mask,id))

def c41710 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41710 : Upper (D 7) (R 7) [12,48,65,160] 13 := by
  apply FastRouting.sound _ _ [12,48,65,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41710 c41710
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32777
  · exact u32778
  · exact u32779
  · exact u32780
  · exact u32781
  · exact u32782
  · exact u32783
  · exact u32784
  · exact u32785
  · exact u32786

def b41711 : PairBound 9 := { available := 419, camps := [{ cop := 3, region := 5, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 50 69 200 435 419 483 419 419), lower := (rows 13 50 69 200 16 32 64 128 256), losses := [] }

theorem u41711 : Upper (D 7) (R 7) [12,48,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41712 : Route 9 := (fun mask => (mask,id))

def c41712 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41712 : Upper (D 7) (R 7) [12,48,65,257] 13 := by
  apply FastRouting.sound _ _ [12,48,65,257] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41712 c41712
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32787
  · exact u32788
  · exact u32789
  · exact u32790
  · exact u32791
  · exact u32792

def r41713 : Route 9 := (fun mask => (mask,id))

def c41713 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41713 : Upper (D 7) (R 7) [12,48,65,258] 13 := by
  apply FastRouting.sound _ _ [12,48,65,258] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41713 c41713
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32793
  · exact u32794
  · exact u32795
  · exact u32796
  · exact u32797
  · exact u32798
  · exact u32799
  · exact u32800
  · exact u32801
  · exact u32802

def r41714 : Route 9 := (fun mask => (mask,id))

def c41714 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41714 : Upper (D 7) (R 7) [12,48,65,288] 13 := by
  apply FastRouting.sound _ _ [12,48,65,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41714 c41714
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32803
  · exact u32804
  · exact u32805
  · exact u32806
  · exact u32807
  · exact u32808

def b41715 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 5, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(2,1)], upper := (rows 13 50 69 328 179 163 227 163 419), lower := (rows 13 50 69 328 16 32 64 128 256), losses := [] }

theorem u41715 : Upper (D 7) (R 7) [12,48,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41716 : Route 9 := (fun mask => (mask,id))

def c41716 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41716 : Upper (D 7) (R 7) [12,48,65,384] 13 := by
  apply FastRouting.sound _ _ [12,48,65,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41716 c41716
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32809
  · exact u32810
  · exact u32811
  · exact u32812
  · exact u32813
  · exact u32814
  · exact u32815
  · exact u32816
  · exact u32817
  · exact u32818

def b41717 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 9, targets := 160 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 50 70 74 433 417 481 417 417), lower := (rows 13 50 70 74 16 32 64 128 256), losses := [] }

theorem u41717 : Upper (D 7) (R 7) [12,48,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41718 : Route 9 := (fun mask => (mask,id))

def c41718 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41718 : Upper (D 7) (R 7) [12,48,66,96] 13 := by
  apply FastRouting.sound _ _ [12,48,66,96] 13 (by decide) (choices 2) [3,129,130,257,258,384] r41718 c41718
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32819
  · exact u32820
  · exact u32821
  · exact u32822
  · exact u32823
  · exact u32824

theorem m41719_129 : Upper (D 7) (R 7) [12,48,66,130,129] 13 :=
  permutation_upper _ _ _ [12,48,66,130,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32826

theorem m41719_160 : Upper (D 7) (R 7) [12,48,66,130,160] 13 :=
  permutation_upper _ _ _ [12,48,66,130,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32827

theorem m41719_384 : Upper (D 7) (R 7) [12,48,66,130,384] 13 :=
  permutation_upper _ _ _ [12,48,66,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32831

def r41719 : Route 9 := (fun mask => (mask,id))

def c41719 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41719 : Upper (D 7) (R 7) [12,48,66,130] 13 := by
  apply FastRouting.sound _ _ [12,48,66,130] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r41719 c41719
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32825
  · exact u32826
  · exact u32827
  · exact m41719_129
  · exact m41719_160
  · exact u32828
  · exact u32829
  · exact u32830
  · exact u32831
  · exact m41719_384

def r41720 : Route 9 := (fun mask => (mask,id))

def c41720 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41720 : Upper (D 7) (R 7) [12,48,66,160] 13 := by
  apply FastRouting.sound _ _ [12,48,66,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41720 c41720
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32832
  · exact u32833
  · exact u32834
  · exact u32835
  · exact u32836
  · exact u32837
  · exact u32838
  · exact u32839
  · exact u32840
  · exact u32841

def r41721 : Route 9 := (fun mask => (mask,id))

def c41721 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41721 : Upper (D 7) (R 7) [12,48,66,192] 13 := by
  apply FastRouting.sound _ _ [12,48,66,192] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r41721 c41721
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32842
  · exact u32843
  · exact u32844
  · exact u32845
  · exact u32846
  · exact u32847
  · exact u32848
  · exact u32849
  · exact u32850
  · exact u32851

def r41722 : Route 9 := (fun mask => (mask,id))

def c41722 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41722 : Upper (D 7) (R 7) [12,48,66,257] 13 := by
  apply FastRouting.sound _ _ [12,48,66,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41722 c41722
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32852
  · exact u32853
  · exact u32854
  · exact u32855
  · exact u32856
  · exact u32857
  · exact u32858
  · exact u32859
  · exact u32860
  · exact u32861

def r41723 : Route 9 := (fun mask => (mask,id))

def c41723 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41723 : Upper (D 7) (R 7) [12,48,66,258] 13 := by
  apply FastRouting.sound _ _ [12,48,66,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41723 c41723
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32862
  · exact u32863
  · exact u32864
  · exact u32865
  · exact u32866
  · exact u32867

def r41724 : Route 9 := (fun mask => (mask,id))

def c41724 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41724 : Upper (D 7) (R 7) [12,48,66,288] 13 := by
  apply FastRouting.sound _ _ [12,48,66,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41724 c41724
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32868
  · exact u32869
  · exact u32870
  · exact u32871
  · exact u32872
  · exact u32873

def r41725 : Route 9 := (fun mask => (mask,id))

def c41725 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41725 : Upper (D 7) (R 7) [12,48,66,320] 13 := by
  apply FastRouting.sound _ _ [12,48,66,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r41725 c41725
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32874
  · exact u32875
  · exact u32876
  · exact u32877
  · exact u32878
  · exact u32879

def r41726 : Route 9 := (fun mask => (mask,id))

def c41726 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41726 : Upper (D 7) (R 7) [12,48,66,384] 13 := by
  apply FastRouting.sound _ _ [12,48,66,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41726 c41726
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32880
  · exact u32881
  · exact u32882
  · exact u32883
  · exact u32884
  · exact u32885
  · exact u32886
  · exact u32887
  · exact u32888
  · exact u32889

def r41727 : Route 9 := (fun mask => (mask,id))

def c41727 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u41727 : Upper (D 7) (R 7) [12,48,96,192] 13 := by
  apply FastRouting.sound _ _ [12,48,96,192] 13 (by decide) (choices 2) [3,129,130,257,258,384] r41727 c41727
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32890
  · exact u32891
  · exact u32892
  · exact u32893
  · exact u32894
  · exact u32895

def r41728 : Route 9 := (fun mask => (mask,id))

def c41728 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41728 : Upper (D 7) (R 7) [12,48,96,257] 13 := by
  apply FastRouting.sound _ _ [12,48,96,257] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41728 c41728
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32896
  · exact u32897
  · exact u32898
  · exact u32899
  · exact u32900
  · exact u32901

def r41729 : Route 9 := (fun mask => (mask,id))

def c41729 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41729 : Upper (D 7) (R 7) [12,48,96,258] 13 := by
  apply FastRouting.sound _ _ [12,48,96,258] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41729 c41729
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32902
  · exact u32903
  · exact u32904
  · exact u32905
  · exact u32906
  · exact u32907

def r41730 : Route 9 := (fun mask => (mask,id))

def c41730 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41730 : Upper (D 7) (R 7) [12,48,96,320] 13 := by
  apply FastRouting.sound _ _ [12,48,96,320] 13 (by decide) (choices 2) [3,129,130] r41730 c41730
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u32908
  · exact u32909
  · exact u32910

def r41731 : Route 9 := (fun mask => (mask,id))

def c41731 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41731 : Upper (D 7) (R 7) [12,48,96,384] 13 := by
  apply FastRouting.sound _ _ [12,48,96,384] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41731 c41731
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32911
  · exact u32912
  · exact u32913
  · exact u32914
  · exact u32915
  · exact u32916

def b41732 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 9, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 50 196 200 307 291 355 419 291), lower := (rows 13 50 196 200 16 32 64 128 256), losses := [] }

theorem u41732 : Upper (D 7) (R 7) [12,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41733 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41733 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41733 : Upper (D 7) (R 7) [12,48,192,257] 13 := by
  apply FastRouting.sound _ _ [12,48,192,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41733 c41733
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32917
  · exact u32918
  · exact u32919
  · exact u32920
  · exact u32921
  · exact u32922
  · exact u32923

def r41734 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41734 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41734 : Upper (D 7) (R 7) [12,48,192,258] 13 := by
  apply FastRouting.sound _ _ [12,48,192,258] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41734 c41734
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32924
  · exact u32925
  · exact u32926
  · exact u32927
  · exact u32928
  · exact u32929
  · exact u32930

def r41735 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41735 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41735 : Upper (D 7) (R 7) [12,48,192,288] 13 := by
  apply FastRouting.sound _ _ [12,48,192,288] 13 (by decide) (choices 2) [3,65,66,192] r41735 c41735
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32931
  · exact u32932
  · exact u32933
  · exact u32934

def r41736 : Route 9 := (fun mask => (mask,id))

def c41736 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41736 : Upper (D 7) (R 7) [12,48,192,320] 13 := by
  apply FastRouting.sound _ _ [12,48,192,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r41736 c41736
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32935
  · exact u32936
  · exact u32937
  · exact u32938
  · exact u32939
  · exact u32940

def b41737 : PairBound 9 := { available := 496, camps := [{ cop := 1, region := 13, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 98 7 11 496 496 496 496 496), lower := (rows 13 98 7 11 16 32 64 128 256), losses := [] }

theorem u41737 : Upper (D 7) (R 7) [12,96,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41738 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41738 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41738 : Upper (D 7) (R 7) [12,96,3,17] 13 := by
  apply FastRouting.sound _ _ [12,96,3,17] 13 (by decide) (choices 2) [34,96,130,160,258,288,384] r41738 c41738
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32941
  · exact u32942
  · exact u32943
  · exact u32944
  · exact u32945
  · exact u32946
  · exact u32947

def b41739 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 98 7 26 497 481 481 481 481), lower := (rows 13 98 7 26 16 32 64 128 256), losses := [] }

theorem u41739 : Upper (D 7) (R 7) [12,96,3,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41740 : PairBound 9 := { available := 466, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 7 41 466 498 466 466 466), lower := (rows 13 98 7 41 16 32 64 128 256), losses := [] }

theorem u41740 : Upper (D 7) (R 7) [12,96,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41741 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 13, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 7 42 465 497 465 465 465), lower := (rows 13 98 7 42 16 32 64 128 256), losses := [] }

theorem u41741 : Upper (D 7) (R 7) [12,96,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41742 : Route 9 := (fun mask => (mask,id))

def c41742 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41742 : Upper (D 7) (R 7) [12,96,3,48] 13 := by
  apply FastRouting.sound _ _ [12,96,3,48] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41742 c41742
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32948
  · exact u32949
  · exact u32950
  · exact u32951
  · exact u32952
  · exact u32953
  · exact u32954
  · exact u32955
  · exact u32956
  · exact u32957

def b41743 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 13, targets := 128 },{ cop := 1, region := 8, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(3,7)], upper := (rows 13 98 7 104 403 435 467 403 403), lower := (rows 13 98 7 104 16 32 64 128 256), losses := [] }

theorem u41743 : Upper (D 7) (R 7) [12,96,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41744 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41744 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41744 : Upper (D 7) (R 7) [12,96,3,129] 13 := by
  apply FastRouting.sound _ _ [12,96,3,129] 13 (by decide) (choices 2) [34,96,130,160,258,288,384] r41744 c41744
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32958
  · exact u32959
  · exact u32960
  · exact u32961
  · exact u32962
  · exact u32963
  · exact u32964

def b41745 : PairBound 9 := { available := 497, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 98 7 138 497 497 497 497 497), lower := (rows 13 98 7 138 16 32 64 128 256), losses := [] }

theorem u41745 : Upper (D 7) (R 7) [12,96,3,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41746 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41746 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41746 : Upper (D 7) (R 7) [12,96,3,144] 13 := by
  apply FastRouting.sound _ _ [12,96,3,144] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r41746 c41746
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32965
  · exact u32966
  · exact u32967
  · exact u32968
  · exact u32969
  · exact u32970
  · exact u32971
  · exact u32972
  · exact u32973
  · exact u32974
  · exact u32975

def r41747 : Route 9 := (fun mask => (mask,id))

def c41747 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41747 : Upper (D 7) (R 7) [12,96,3,160] 13 := by
  apply FastRouting.sound _ _ [12,96,3,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41747 c41747
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32976
  · exact u32977
  · exact u32978
  · exact u32979
  · exact u32980
  · exact u32981
  · exact u32982
  · exact u32983
  · exact u32984
  · exact u32985

def r41748 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41748 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41748 : Upper (D 7) (R 7) [12,96,3,257] 13 := by
  apply FastRouting.sound _ _ [12,96,3,257] 13 (by decide) (choices 2) [34,96,130,160] r41748 c41748
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u32986
  · exact u32987
  · exact u32988
  · exact u32989

def b41749 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 98 7 266 241 241 241 241 497), lower := (rows 13 98 7 266 16 32 64 128 256), losses := [] }

theorem u41749 : Upper (D 7) (R 7) [12,96,3,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41750 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41750 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41750 : Upper (D 7) (R 7) [12,96,3,272] 13 := by
  apply FastRouting.sound _ _ [12,96,3,272] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41750 c41750
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32990
  · exact u32991
  · exact u32992
  · exact u32993
  · exact u32994
  · exact u32995
  · exact u32996

def r41751 : Route 9 := (fun mask => (mask,id))

def c41751 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41751 : Upper (D 7) (R 7) [12,96,3,288] 13 := by
  apply FastRouting.sound _ _ [12,96,3,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41751 c41751
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u32997
  · exact u32998
  · exact u32999
  · exact u33000
  · exact u33001
  · exact u33002

def r41752 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41752 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41752 : Upper (D 7) (R 7) [12,96,3,384] 13 := by
  apply FastRouting.sound _ _ [12,96,3,384] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41752 c41752
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33003
  · exact u33004
  · exact u33005
  · exact u33006
  · exact u33007
  · exact u33008
  · exact u33009

def r41753 : Route 9 := (fun mask => (mask,id))

def c41753 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41753 : Upper (D 7) (R 7) [12,96,17,33] 13 := by
  apply FastRouting.sound _ _ [12,96,17,33] 13 (by decide) (choices 2) [66,130,192,258,320,384] r41753 c41753
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33010
  · exact u33011
  · exact u33012
  · exact u33013
  · exact u33014
  · exact u33015

def b41754 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 13 98 21 42 467 483 451 451 451), lower := (rows 13 98 21 42 16 32 64 128 256), losses := [] }

theorem u41754 : Upper (D 7) (R 7) [12,96,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41755 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 13 98 21 104 403 419 451 387 387), lower := (rows 13 98 21 104 16 32 64 128 256), losses := [] }

theorem u41755 : Upper (D 7) (R 7) [12,96,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41756 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41756 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41756 : Upper (D 7) (R 7) [12,96,17,129] 13 := by
  apply FastRouting.sound _ _ [12,96,17,129] 13 (by decide) (choices 2) [34,96,130,160,258,288,384] r41756 c41756
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33016
  · exact u33017
  · exact u33018
  · exact u33019
  · exact u33020
  · exact u33021
  · exact u33022

def r41757 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41757 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u41757 : Upper (D 7) (R 7) [12,96,17,130] 13 := by
  apply FastRouting.sound _ _ [12,96,17,130] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r41757 c41757
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33023
  · exact u33024
  · exact u33025
  · exact u33026
  · exact u33027
  · exact u33028
  · exact u33029
  · exact u33030
  · exact u33031
  · exact u33032
  · exact u33033

def r41758 : Route 9 := (fun mask => (mask,id))

def c41758 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u41758 : Upper (D 7) (R 7) [12,96,17,160] 13 := by
  apply FastRouting.sound _ _ [12,96,17,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r41758 c41758
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33034
  · exact u33035
  · exact u33036
  · exact u33037
  · exact u33038
  · exact u33039
  · exact u33040
  · exact u33041
  · exact u33042
  · exact u33043

def r41759 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41759 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41759 : Upper (D 7) (R 7) [12,96,17,257] 13 := by
  apply FastRouting.sound _ _ [12,96,17,257] 13 (by decide) (choices 2) [34,96,130,160] r41759 c41759
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33044
  · exact u33045
  · exact u33046
  · exact u33047

#print axioms u41759
end Delivery.IrregularNine14.P07
