import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0492
import IrregularNine14P07C0493
import IrregularNine14P07C0494

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r40680 : Route 9 := (fun mask => (mask,id))

def c40680 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40680 : Upper (D 7) (R 7) [96,288,9,130,192] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,192] 13 (by decide) (choices 1) [1,2,4,16] r40680 c40680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29575
  · exact u29576
  · exact u29577
  · exact u29578

def b40681 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 290 13 140 81 178 210 146 402), lower := (rows 97 290 13 140 81 32 64 128 256), losses := [] }

theorem u40681 : Upper (D 7) (R 7) [96,288,9,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40682 : Route 9 := (fun mask => (mask,id))

def c40682 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40682 : Upper (D 7) (R 7) [96,288,9,132,66] 13 := by
  apply FastRouting.sound _ _ [96,288,9,132,66] 13 (by decide) (choices 1) [1,2,16,128] r40682 c40682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29579
  · exact u29580
  · exact u29581
  · exact u29582

def b40683 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 12, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 97 290 13 140 145 114 82 210 338), lower := (rows 97 290 13 140 145 32 64 128 256), losses := [] }

theorem u40683 : Upper (D 7) (R 7) [96,288,9,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40684 : Route 9 := (fun mask => (mask,id))

def c40684 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40684 : Upper (D 7) (R 7) [96,288,9,132,130] 13 := by
  apply FastRouting.sound _ _ [96,288,9,132,130] 13 (by decide) (choices 1) [1,2,16,64] r40684 c40684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29583
  · exact u29584
  · exact u29585
  · exact u29586

def r40685 : Route 9 := (fun mask => (mask,id))

def c40685 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40685 : Upper (D 7) (R 7) [96,288,9,132,192] 13 := by
  apply FastRouting.sound _ _ [96,288,9,132,192] 13 (by decide) (choices 1) [1,2,16] r40685 c40685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29587
  · exact u29588
  · exact u29589

def r40686 : Route 9 := (fun mask => (mask,id))

def c40686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40686 : Upper (D 7) (R 7) [96,288,9,144,6] 13 := by
  apply FastRouting.sound _ _ [96,288,9,144,6] 13 (by decide) (choices 1) [1,2,64,128] r40686 c40686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29590
  · exact u29591
  · exact u29592
  · exact u29593

def b40687 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 290 13 152 81 166 198 134 390), lower := (rows 97 290 13 152 81 32 64 128 256), losses := [] }

theorem u40687 : Upper (D 7) (R 7) [96,288,9,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40688 : Route 9 := (fun mask => (mask,id))

def c40688 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40688 : Upper (D 7) (R 7) [96,288,9,144,66] 13 := by
  apply FastRouting.sound _ _ [96,288,9,144,66] 13 (by decide) (choices 1) [1,2,4,128] r40688 c40688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29594
  · exact u29595
  · exact u29596
  · exact u29597

def r40689 : Route 9 := (fun mask => (mask,id))

def c40689 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40689 : Upper (D 7) (R 7) [96,288,9,144,68] 13 := by
  apply FastRouting.sound _ _ [96,288,9,144,68] 13 (by decide) (choices 1) [1,2,128] r40689 c40689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29598
  · exact u29599
  · exact u29600

def b40690 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 12, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 97 290 13 152 145 102 70 198 326), lower := (rows 97 290 13 152 145 32 64 128 256), losses := [] }

theorem u40690 : Upper (D 7) (R 7) [96,288,9,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40691 : PairBound 9 := { available := 71, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 290 13 152 146 103 71 199 327), lower := (rows 97 290 13 152 146 32 64 128 256), losses := [] }

theorem u40691 : Upper (D 7) (R 7) [96,288,9,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40692 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 290 13 152 148 99 67 195 323), lower := (rows 97 290 13 152 148 32 64 128 256), losses := [] }

theorem u40692 : Upper (D 7) (R 7) [96,288,9,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40693 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 290 13 152 208 39 71 135 263), lower := (rows 97 290 13 152 208 32 64 128 256), losses := [] }

theorem u40693 : Upper (D 7) (R 7) [96,288,9,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40694 : Route 9 := (fun mask => (mask,id))

def c40694 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40694 : Upper (D 7) (R 7) [96,288,9,192,6] 13 := by
  apply FastRouting.sound _ _ [96,288,9,192,6] 13 (by decide) (choices 1) [1,2,16,128] r40694 c40694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29601
  · exact u29602
  · exact u29603
  · exact u29604

def r40695 : Route 9 := (fun mask => (mask,id))

def c40695 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40695 : Upper (D 7) (R 7) [96,288,9,192,129] 13 := by
  apply FastRouting.sound _ _ [96,288,9,192,129] 13 (by decide) (choices 1) [2,4,16] r40695 c40695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29605
  · exact u29606
  · exact u29607

def r40696 : Route 9 := (fun mask => (mask,id))

def c40696 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40696 : Upper (D 7) (R 7) [96,288,9,192,130] 13 := by
  apply FastRouting.sound _ _ [96,288,9,192,130] 13 (by decide) (choices 1) [1,2,4,16] r40696 c40696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29608
  · exact u29609
  · exact u29610
  · exact u29611

def b40697 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(1,7),(4,6)], upper := (rows 97 290 13 200 148 51 83 147 275), lower := (rows 97 290 13 200 148 32 64 128 256), losses := [] }

theorem u40697 : Upper (D 7) (R 7) [96,288,9,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40698 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 12, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 14 145 241 209 209 465), lower := (rows 97 290 14 14 145 32 64 128 256), losses := [] }

theorem u40698 : Upper (D 7) (R 7) [96,288,10,6,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40699 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 12, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 14 208 177 209 145 401), lower := (rows 97 290 14 14 208 32 64 128 256), losses := [] }

theorem u40699 : Upper (D 7) (R 7) [96,288,10,6,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40700 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 26 84 161 193 129 385), lower := (rows 97 290 14 26 84 32 64 128 256), losses := [] }

theorem u40700 : Upper (D 7) (R 7) [96,288,10,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40701 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 26 145 229 197 197 453), lower := (rows 97 290 14 26 145 32 64 128 256), losses := [] }

theorem u40701 : Upper (D 7) (R 7) [96,288,10,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40702 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 26 148 225 193 193 449), lower := (rows 97 290 14 26 148 32 64 128 256), losses := [] }

theorem u40702 : Upper (D 7) (R 7) [96,288,10,18,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40703 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 26 208 165 197 133 389), lower := (rows 97 290 14 26 208 32 64 128 256), losses := [] }

theorem u40703 : Upper (D 7) (R 7) [96,288,10,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40704 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 290 14 28 81 163 195 131 387), lower := (rows 97 290 14 28 81 32 64 128 256), losses := [] }

theorem u40704 : Upper (D 7) (R 7) [96,288,10,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40705 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 12, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 28 82 161 193 129 385), lower := (rows 97 290 14 28 82 32 64 128 256), losses := [] }

theorem u40705 : Upper (D 7) (R 7) [96,288,10,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40706 : Route 9 := (fun mask => (mask,id))

def c40706 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40706 : Upper (D 7) (R 7) [96,288,10,20,129] 13 := by
  apply FastRouting.sound _ _ [96,288,10,20,129] 13 (by decide) (choices 1) [1,2,64,128] r40706 c40706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29612
  · exact u29613
  · exact u29614
  · exact u29615

def b40707 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 12, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 28 146 225 193 193 449), lower := (rows 97 290 14 28 146 32 64 128 256), losses := [] }

theorem u40707 : Upper (D 7) (R 7) [96,288,10,20,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40708 : Route 9 := (fun mask => (mask,id))

def c40708 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40708 : Upper (D 7) (R 7) [96,288,10,20,192] 13 := by
  apply FastRouting.sound _ _ [96,288,10,20,192] 13 (by decide) (choices 1) [1,2,128] r40708 c40708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29616
  · exact u29617
  · exact u29618

def b40709 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 290 14 73 145 182 214 150 406), lower := (rows 97 290 14 73 145 32 64 128 256), losses := [] }

theorem u40709 : Upper (D 7) (R 7) [96,288,10,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40710 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 290 14 73 146 181 213 149 405), lower := (rows 97 290 14 73 146 32 64 128 256), losses := [] }

theorem u40710 : Upper (D 7) (R 7) [96,288,10,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40711 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 290 14 73 148 179 211 147 403), lower := (rows 97 290 14 73 148 32 64 128 256), losses := [] }

theorem u40711 : Upper (D 7) (R 7) [96,288,10,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40712 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 74 145 181 213 149 405), lower := (rows 97 290 14 74 145 32 64 128 256), losses := [] }

theorem u40712 : Upper (D 7) (R 7) [96,288,10,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40713 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 74 148 177 209 145 401), lower := (rows 97 290 14 74 148 32 64 128 256), losses := [] }

theorem u40713 : Upper (D 7) (R 7) [96,288,10,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40714 : Route 9 := (fun mask => (mask,id))

def c40714 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40714 : Upper (D 7) (R 7) [96,288,10,68,129] 13 := by
  apply FastRouting.sound _ _ [96,288,10,68,129] 13 (by decide) (choices 1) [1,2,16,128] r40714 c40714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29619
  · exact u29620
  · exact u29621
  · exact u29622

def r40715 : Route 9 := (fun mask => (mask,id))

def c40715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40715 : Upper (D 7) (R 7) [96,288,10,68,130] 13 := by
  apply FastRouting.sound _ _ [96,288,10,68,130] 13 (by decide) (choices 1) [1,16,128] r40715 c40715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29623
  · exact u29624
  · exact u29625

def r40716 : Route 9 := (fun mask => (mask,id))

def c40716 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40716 : Upper (D 7) (R 7) [96,288,10,80,129] 13 := by
  apply FastRouting.sound _ _ [96,288,10,80,129] 13 (by decide) (choices 1) [1,2,4,128] r40716 c40716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29626
  · exact u29627
  · exact u29628
  · exact u29629

def r40717 : Route 9 := (fun mask => (mask,id))

def c40717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40717 : Upper (D 7) (R 7) [96,288,10,80,130] 13 := by
  apply FastRouting.sound _ _ [96,288,10,80,130] 13 (by decide) (choices 1) [1,4,128] r40717 c40717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29630
  · exact u29631
  · exact u29632

def r40718 : Route 9 := (fun mask => (mask,id))

def c40718 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40718 : Upper (D 7) (R 7) [96,288,10,80,132] 13 := by
  apply FastRouting.sound _ _ [96,288,10,80,132] 13 (by decide) (choices 1) [1,2,128] r40718 c40718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29633
  · exact u29634
  · exact u29635

def b40719 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 290 14 137 81 182 214 150 406), lower := (rows 97 290 14 137 81 32 64 128 256), losses := [] }

theorem u40719 : Upper (D 7) (R 7) [96,288,10,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40720 : Route 9 := (fun mask => (mask,id))

def c40720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40720 : Upper (D 7) (R 7) [96,288,10,129,66] 13 := by
  apply FastRouting.sound _ _ [96,288,10,129,66] 13 (by decide) (choices 1) [1,4,16,128] r40720 c40720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29636
  · exact u29637
  · exact u29638
  · exact u29639

def r40721 : Route 9 := (fun mask => (mask,id))

def c40721 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40721 : Upper (D 7) (R 7) [96,288,10,129,68] 13 := by
  apply FastRouting.sound _ _ [96,288,10,129,68] 13 (by decide) (choices 1) [1,2,16,128] r40721 c40721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29640
  · exact u29641
  · exact u29642
  · exact u29643

def b40722 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 97 290 14 137 145 118 86 214 342), lower := (rows 97 290 14 137 145 32 64 128 256), losses := [] }

theorem u40722 : Upper (D 7) (R 7) [96,288,10,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40723 : Route 9 := (fun mask => (mask,id))

def c40723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40723 : Upper (D 7) (R 7) [96,288,10,129,130] 13 := by
  apply FastRouting.sound _ _ [96,288,10,129,130] 13 (by decide) (choices 1) [1,4,16,64] r40723 c40723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29644
  · exact u29645
  · exact u29646
  · exact u29647

def r40724 : Route 9 := (fun mask => (mask,id))

def c40724 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40724 : Upper (D 7) (R 7) [96,288,10,129,132] 13 := by
  apply FastRouting.sound _ _ [96,288,10,129,132] 13 (by decide) (choices 1) [1,2,16,64] r40724 c40724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29648
  · exact u29649
  · exact u29650
  · exact u29651

def r40725 : Route 9 := (fun mask => (mask,id))

def c40725 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40725 : Upper (D 7) (R 7) [96,288,10,129,192] 13 := by
  apply FastRouting.sound _ _ [96,288,10,129,192] 13 (by decide) (choices 1) [1,2,4,16] r40725 c40725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29652
  · exact u29653
  · exact u29654
  · exact u29655

def b40726 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 138 84 177 209 145 401), lower := (rows 97 290 14 138 84 32 64 128 256), losses := [] }

theorem u40726 : Upper (D 7) (R 7) [96,288,10,130,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40727 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 138 145 117 85 213 341), lower := (rows 97 290 14 138 145 32 64 128 256), losses := [] }

theorem u40727 : Upper (D 7) (R 7) [96,288,10,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40728 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 20, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(4,0)], upper := (rows 97 290 14 138 148 113 81 209 337), lower := (rows 97 290 14 138 148 32 64 128 256), losses := [] }

theorem u40728 : Upper (D 7) (R 7) [96,288,10,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40729 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 97 290 14 138 208 53 85 149 277), lower := (rows 97 290 14 138 208 32 64 128 256), losses := [] }

theorem u40729 : Upper (D 7) (R 7) [96,288,10,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40730 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 290 14 140 81 179 211 147 403), lower := (rows 97 290 14 140 81 32 64 128 256), losses := [] }

theorem u40730 : Upper (D 7) (R 7) [96,288,10,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40731 : Route 9 := (fun mask => (mask,id))

def c40731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40731 : Upper (D 7) (R 7) [96,288,10,132,66] 13 := by
  apply FastRouting.sound _ _ [96,288,10,132,66] 13 (by decide) (choices 1) [1,16,128] r40731 c40731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29656
  · exact u29657
  · exact u29658

def r40732 : Route 9 := (fun mask => (mask,id))

def c40732 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40732 : Upper (D 7) (R 7) [96,288,10,132,129] 13 := by
  apply FastRouting.sound _ _ [96,288,10,132,129] 13 (by decide) (choices 1) [1,2,16,64] r40732 c40732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29659
  · exact u29660
  · exact u29661
  · exact u29662

def b40733 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 97 290 14 140 146 113 81 209 337), lower := (rows 97 290 14 140 146 32 64 128 256), losses := [] }

theorem u40733 : Upper (D 7) (R 7) [96,288,10,132,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40734 : Route 9 := (fun mask => (mask,id))

def c40734 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40734 : Upper (D 7) (R 7) [96,288,10,132,192] 13 := by
  apply FastRouting.sound _ _ [96,288,10,132,192] 13 (by decide) (choices 1) [1,2,16] r40734 c40734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29663
  · exact u29664
  · exact u29665

def b40735 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 290 14 152 81 167 199 135 391), lower := (rows 97 290 14 152 81 32 64 128 256), losses := [] }

theorem u40735 : Upper (D 7) (R 7) [96,288,10,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40736 : Route 9 := (fun mask => (mask,id))

def c40736 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40736 : Upper (D 7) (R 7) [96,288,10,144,66] 13 := by
  apply FastRouting.sound _ _ [96,288,10,144,66] 13 (by decide) (choices 1) [1,4,128] r40736 c40736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29666
  · exact u29667
  · exact u29668

def r40737 : Route 9 := (fun mask => (mask,id))

def c40737 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40737 : Upper (D 7) (R 7) [96,288,10,144,68] 13 := by
  apply FastRouting.sound _ _ [96,288,10,144,68] 13 (by decide) (choices 1) [1,2,128] r40737 c40737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29669
  · exact u29670
  · exact u29671

def b40738 : PairBound 9 := { available := 71, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 290 14 152 145 103 71 199 327), lower := (rows 97 290 14 152 145 32 64 128 256), losses := [] }

theorem u40738 : Upper (D 7) (R 7) [96,288,10,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40739 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 12, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 97 290 14 152 146 101 69 197 325), lower := (rows 97 290 14 152 146 32 64 128 256), losses := [] }

theorem u40739 : Upper (D 7) (R 7) [96,288,10,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u40739
end Delivery.IrregularNine14.P07
