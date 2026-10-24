import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0107
import IrregularNine14P07C0108

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21780 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 322 14 56 148 96 193 129 385), lower := (rows 35 322 14 56 148 96 64 128 256), losses := [] }

theorem u21780 : Upper (D 7) (R 7) [34,320,10,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21781 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 322 14 56 148 160 65 193 321), lower := (rows 35 322 14 56 148 160 64 128 256), losses := [] }

theorem u21781 : Upper (D 7) (R 7) [34,320,10,48,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21782 : Route 9 := (fun mask => (mask,id))

def c21782 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21782 : Upper (D 7) (R 7) [34,320,10,48,192,1] 13 := by
  apply FastRouting.sound _ _ [34,320,10,48,192,1] 13 (by decide) (choices 1) [1,4,128] r21782 c21782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6471
  · exact u6472
  · exact u6473

def b21783 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 322 14 56 208 36 193 129 385), lower := (rows 35 322 14 56 208 36 64 128 256), losses := [] }

theorem u21783 : Upper (D 7) (R 7) [34,320,10,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21783 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21784 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 322 14 56 208 160 69 133 261), lower := (rows 35 322 14 56 208 160 64 128 256), losses := [] }

theorem u21784 : Upper (D 7) (R 7) [34,320,10,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21785 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 322 14 73 52 33 208 144 400), lower := (rows 35 322 14 73 52 33 64 128 256), losses := [] }

theorem u21785 : Upper (D 7) (R 7) [34,320,10,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21786 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 322 14 73 52 48 193 129 385), lower := (rows 35 322 14 73 52 48 64 128 256), losses := [] }

theorem u21786 : Upper (D 7) (R 7) [34,320,10,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21786 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21787 : Route 9 := (fun mask => (mask,id))

def c21787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21787 : Upper (D 7) (R 7) [34,320,10,65,36,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,65,36,128] 13 (by decide) (choices 1) [1,16,128] r21787 c21787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6474
  · exact u6475
  · exact u6476

def b21788 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 322 14 73 145 36 240 176 432), lower := (rows 35 322 14 73 145 36 64 128 256), losses := [] }

theorem u21788 : Upper (D 7) (R 7) [34,320,10,65,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21788 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21789 : Route 9 := (fun mask => (mask,id))

def c21789 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21789 : Upper (D 7) (R 7) [34,320,10,65,129,16] 13 := by
  apply FastRouting.sound _ _ [34,320,10,65,129,16] 13 (by decide) (choices 1) [4,32,128] r21789 c21789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6477
  · exact u6478
  · exact u6479

def r21790 : Route 9 := (fun mask => (mask,id))

def c21790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21790 : Upper (D 7) (R 7) [34,320,10,65,129,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,65,129,128] 13 (by decide) (choices 1) [4,16,32] r21790 c21790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6480
  · exact u6481
  · exact u6482

def b21791 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 322 14 73 148 33 240 176 432), lower := (rows 35 322 14 73 148 33 64 128 256), losses := [] }

theorem u21791 : Upper (D 7) (R 7) [34,320,10,65,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21792 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 35 322 14 73 148 48 225 161 417), lower := (rows 35 322 14 73 148 48 64 128 256), losses := [] }

theorem u21792 : Upper (D 7) (R 7) [34,320,10,65,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21792 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21793 : Route 9 := (fun mask => (mask,id))

def c21793 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21793 : Upper (D 7) (R 7) [34,320,10,65,132,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,65,132,128] 13 (by decide) (choices 1) [1,16,32] r21793 c21793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6483
  · exact u6484
  · exact u6485

def b21794 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 322 14 73 176 33 212 148 404), lower := (rows 35 322 14 73 176 33 64 128 256), losses := [] }

theorem u21794 : Upper (D 7) (R 7) [34,320,10,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21795 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 322 14 73 176 36 209 145 401), lower := (rows 35 322 14 73 176 36 64 128 256), losses := [] }

theorem u21795 : Upper (D 7) (R 7) [34,320,10,65,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21795 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21796 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 14 73 176 48 197 133 389), lower := (rows 35 322 14 73 176 48 64 128 256), losses := [] }

theorem u21796 : Upper (D 7) (R 7) [34,320,10,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21796 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21797 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 322 14 73 176 160 85 149 277), lower := (rows 35 322 14 73 176 160 64 128 256), losses := [] }

theorem u21797 : Upper (D 7) (R 7) [34,320,10,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21798 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 322 14 88 52 33 193 129 385), lower := (rows 35 322 14 88 52 33 64 128 256), losses := [] }

theorem u21798 : Upper (D 7) (R 7) [34,320,10,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21799 : Route 9 := (fun mask => (mask,id))

def c21799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21799 : Upper (D 7) (R 7) [34,320,10,80,36,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,80,36,128] 13 (by decide) (choices 1) [1,128] r21799 c21799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6486
  · exact u6487

def r21800 : Route 9 := (fun mask => (mask,id))

def c21800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21800 : Upper (D 7) (R 7) [34,320,10,80,129,1] 13 := by
  apply FastRouting.sound _ _ [34,320,10,80,129,1] 13 (by decide) (choices 1) [4,32,128] r21800 c21800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6488
  · exact u6489
  · exact u6490

def b21801 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 322 14 88 145 36 225 161 417), lower := (rows 35 322 14 88 145 36 64 128 256), losses := [] }

theorem u21801 : Upper (D 7) (R 7) [34,320,10,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21801 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21802 : Route 9 := (fun mask => (mask,id))

def c21802 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21802 : Upper (D 7) (R 7) [34,320,10,80,129,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,80,129,128] 13 (by decide) (choices 1) [1,4,32] r21802 c21802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6491
  · exact u6492
  · exact u6493

def r21803 : Route 9 := (fun mask => (mask,id))

def c21803 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21803 : Upper (D 7) (R 7) [34,320,10,80,132,1] 13 := by
  apply FastRouting.sound _ _ [34,320,10,80,132,1] 13 (by decide) (choices 1) [1,32,128] r21803 c21803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6494
  · exact u6495
  · exact u6496

def b21804 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,6)], upper := (rows 35 322 14 88 148 160 97 161 289), lower := (rows 35 322 14 88 148 160 64 128 256), losses := [] }

theorem u21804 : Upper (D 7) (R 7) [34,320,10,80,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21805 : Route 9 := (fun mask => (mask,id))

def c21805 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21805 : Upper (D 7) (R 7) [34,320,10,80,160,1] 13 := by
  apply FastRouting.sound _ _ [34,320,10,80,160,1] 13 (by decide) (choices 1) [1,4,128] r21805 c21805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6497
  · exact u6498
  · exact u6499

def b21806 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 322 14 88 176 36 193 129 385), lower := (rows 35 322 14 88 176 36 64 128 256), losses := [] }

theorem u21806 : Upper (D 7) (R 7) [34,320,10,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21806 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21807 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 322 14 88 176 160 69 133 261), lower := (rows 35 322 14 88 176 160 64 128 256), losses := [] }

theorem u21807 : Upper (D 7) (R 7) [34,320,10,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21808 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 322 14 104 145 33 212 148 404), lower := (rows 35 322 14 104 145 33 64 128 256), losses := [] }

theorem u21808 : Upper (D 7) (R 7) [34,320,10,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21809 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 322 14 104 145 36 209 145 401), lower := (rows 35 322 14 104 145 36 64 128 256), losses := [] }

theorem u21809 : Upper (D 7) (R 7) [34,320,10,96,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21809 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21810 : Route 9 := (fun mask => (mask,id))

def c21810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21810 : Upper (D 7) (R 7) [34,320,10,96,129,16] 13 := by
  apply FastRouting.sound _ _ [34,320,10,96,129,16] 13 (by decide) (choices 1) [1,4,128] r21810 c21810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6500
  · exact u6501
  · exact u6502

def r21811 : Route 9 := (fun mask => (mask,id))

def c21811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21811 : Upper (D 7) (R 7) [34,320,10,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,96,129,128] 13 (by decide) (choices 1) [1,4,16] r21811 c21811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6503
  · exact u6504
  · exact u6505

def b21812 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 322 14 104 148 33 209 145 401), lower := (rows 35 322 14 104 148 33 64 128 256), losses := [] }

theorem u21812 : Upper (D 7) (R 7) [34,320,10,96,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21813 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 35 322 14 104 148 48 193 129 385), lower := (rows 35 322 14 104 148 48 64 128 256), losses := [] }

theorem u21813 : Upper (D 7) (R 7) [34,320,10,96,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21813 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21814 : Route 9 := (fun mask => (mask,id))

def c21814 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21814 : Upper (D 7) (R 7) [34,320,10,96,132,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,96,132,128] 13 (by decide) (choices 1) [1,16] r21814 c21814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6506
  · exact u6507

def b21815 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 322 14 137 52 33 208 208 464), lower := (rows 35 322 14 137 52 33 64 128 256), losses := [] }

theorem u21815 : Upper (D 7) (R 7) [34,320,10,129,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21816 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 35 322 14 137 52 48 193 193 449), lower := (rows 35 322 14 137 52 48 64 128 256), losses := [] }

theorem u21816 : Upper (D 7) (R 7) [34,320,10,129,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21816 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21817 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 14 137 52 96 209 145 401), lower := (rows 35 322 14 137 52 96 64 128 256), losses := [] }

theorem u21817 : Upper (D 7) (R 7) [34,320,10,129,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21818 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,1)], upper := (rows 35 322 14 137 52 160 81 209 337), lower := (rows 35 322 14 137 52 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 34 322 62 168 52 160 64 160 256) },{ target := 1, region := (rows 1 0 4 8 20 168 64 128 256), good := (rows 33 320 60 169 52 160 64 160 256) }] }

theorem u21818 : Upper (D 7) (R 7) [34,320,10,129,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21819 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 322 14 137 81 36 240 176 432), lower := (rows 35 322 14 137 81 36 64 128 256), losses := [] }

theorem u21819 : Upper (D 7) (R 7) [34,320,10,129,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21819 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21820 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 322 14 137 81 48 228 164 420), lower := (rows 35 322 14 137 81 48 64 128 256), losses := [] }

theorem u21820 : Upper (D 7) (R 7) [34,320,10,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21820 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21821 : Route 9 := (fun mask => (mask,id))

def c21821 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21821 : Upper (D 7) (R 7) [34,320,10,129,65,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,129,65,128] 13 (by decide) (choices 1) [4,16,32] r21821 c21821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6508
  · exact u6509
  · exact u6510

def b21822 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(4,1)], upper := (rows 35 322 14 137 84 33 240 176 432), lower := (rows 35 322 14 137 84 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 41 68 132 260), good := (rows 33 320 508 169 468 33 64 128 256) },{ target := 6, region := (rows 7 2 4 24 16 63 0 144 272), good := (rows 35 291 47 169 445 33 0 128 256) }] }

theorem u21822 : Upper (D 7) (R 7) [34,320,10,129,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21823 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 0, region := 136, targets := 2 }], pairs := [(2,6),(3,1),(3,6)], upper := (rows 35 322 14 137 84 48 225 161 417), lower := (rows 35 322 14 137 84 48 64 128 256), losses := [] }

theorem u21823 : Upper (D 7) (R 7) [34,320,10,129,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21823 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21824 : Route 9 := (fun mask => (mask,id))

def c21824 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21824 : Upper (D 7) (R 7) [34,320,10,129,68,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,129,68,128] 13 (by decide) (choices 1) [1,16,32] r21824 c21824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6511
  · exact u6512
  · exact u6513

def b21825 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,7)], upper := (rows 35 322 14 137 112 33 212 148 404), lower := (rows 35 322 14 137 112 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 41 68 132 260), good := (rows 33 320 508 169 112 33 64 128 256) }] }

theorem u21825 : Upper (D 7) (R 7) [34,320,10,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21826 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 322 14 137 112 36 209 145 401), lower := (rows 35 322 14 137 112 36 64 128 256), losses := [] }

theorem u21826 : Upper (D 7) (R 7) [34,320,10,129,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21826 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21827 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 14 137 112 48 197 133 389), lower := (rows 35 322 14 137 112 48 64 128 256), losses := [] }

theorem u21827 : Upper (D 7) (R 7) [34,320,10,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21827 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21828 : Route 9 := (fun mask => (mask,id))

def c21828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21828 : Upper (D 7) (R 7) [34,320,10,129,96,128] 13 := by
  apply FastRouting.sound _ _ [34,320,10,129,96,128] 13 (by decide) (choices 1) [1,4,16] r21828 c21828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6514
  · exact u6515
  · exact u6516

def b21829 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 322 14 137 148 33 112 240 368), lower := (rows 35 322 14 137 148 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 41 68 132 260), good := (rows 33 320 508 169 468 33 64 128 256) }] }

theorem u21829 : Upper (D 7) (R 7) [34,320,10,129,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21830 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,7),(1,7),(3,1)], upper := (rows 35 322 14 137 148 48 97 225 353), lower := (rows 35 322 14 137 148 48 64 128 256), losses := [] }

theorem u21830 : Upper (D 7) (R 7) [34,320,10,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21830 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21831 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 14 137 148 96 113 177 305), lower := (rows 35 322 14 137 148 96 64 128 256), losses := [] }

theorem u21831 : Upper (D 7) (R 7) [34,320,10,129,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21831 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21832 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 3, region := 48, targets := 66 }], pairs := [(0,6),(0,7),(4,1),(4,6)], upper := (rows 35 322 14 137 176 33 84 212 340), lower := (rows 35 322 14 137 176 33 64 128 256), losses := [] }

theorem u21832 : Upper (D 7) (R 7) [34,320,10,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21833 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 322 14 137 176 36 81 209 337), lower := (rows 35 322 14 137 176 36 64 128 256), losses := [] }

theorem u21833 : Upper (D 7) (R 7) [34,320,10,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21833 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21834 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 14 137 176 48 69 197 325), lower := (rows 35 322 14 137 176 48 64 128 256), losses := [] }

theorem u21834 : Upper (D 7) (R 7) [34,320,10,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21834 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21835 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 14 137 176 96 85 149 277), lower := (rows 35 322 14 137 176 96 64 128 256), losses := [] }

theorem u21835 : Upper (D 7) (R 7) [34,320,10,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21836 : Route 9 := (fun mask => (mask,id))

def c21836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21836 : Upper (D 7) (R 7) [34,320,10,129,192,1] 13 := by
  apply FastRouting.sound _ _ [34,320,10,129,192,1] 13 (by decide) (choices 1) [4,16,32] r21836 c21836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6517
  · exact u6518
  · exact u6519

def b21837 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 322 14 137 208 36 113 177 305), lower := (rows 35 322 14 137 208 36 64 128 256), losses := [] }

theorem u21837 : Upper (D 7) (R 7) [34,320,10,129,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21837 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21838 : Route 9 := (fun mask => (mask,id))

def c21838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21838 : Upper (D 7) (R 7) [34,320,10,129,192,16] 13 := by
  apply FastRouting.sound _ _ [34,320,10,129,192,16] 13 (by decide) (choices 1) [1,4,32] r21838 c21838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6520
  · exact u6521
  · exact u6522

def b21839 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,7)], upper := (rows 35 322 14 140 81 33 240 176 432), lower := (rows 35 322 14 140 81 33 64 128 256), losses := [] }

theorem u21839 : Upper (D 7) (R 7) [34,320,10,132,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u21839
end Delivery.IrregularNine14.P07
