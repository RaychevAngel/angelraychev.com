import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0075
import IrregularNine14P07C0076

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r17760 : Route 9 := (fun mask => (mask,id))

def c17760 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17760 : Upper (D 7) (R 7) [12,288,48,192,66,128] 13 := by
  apply FastRouting.sound _ _ [12,288,48,192,66,128] 13 (by decide) (choices 1) [1,2] r17760 c17760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4540
  · exact u4541

def b17761 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 290 69 137 82 34 240 176 432), lower := (rows 13 290 69 137 82 34 64 128 256), losses := [] }

theorem u17761 : Upper (D 7) (R 7) [12,288,65,129,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17762 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 13 290 69 137 82 48 226 162 418), lower := (rows 13 290 69 137 82 48 64 128 256), losses := [] }

theorem u17762 : Upper (D 7) (R 7) [12,288,65,129,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17762 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17763 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 338, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 290 69 137 82 160 114 178 306), lower := (rows 13 290 69 137 82 160 64 128 256), losses := [] }

theorem u17763 : Upper (D 7) (R 7) [12,288,65,129,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17764 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 290 69 137 112 34 210 146 402), lower := (rows 13 290 69 137 112 34 64 128 256), losses := [] }

theorem u17764 : Upper (D 7) (R 7) [12,288,65,129,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17765 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 290 69 137 112 48 194 130 386), lower := (rows 13 290 69 137 112 48 64 128 256), losses := [] }

theorem u17765 : Upper (D 7) (R 7) [12,288,65,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17765 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17766 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 338, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 290 69 137 112 160 82 146 274), lower := (rows 13 290 69 137 112 160 64 128 256), losses := [] }

theorem u17766 : Upper (D 7) (R 7) [12,288,65,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17767 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 13 290 69 138 19 48 224 224 480), lower := (rows 13 290 69 138 19 48 64 128 256), losses := [] }

theorem u17767 : Upper (D 7) (R 7) [12,288,65,130,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17767 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17768 : Route 9 := (fun mask => (mask,id))

def c17768 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17768 : Upper (D 7) (R 7) [12,288,65,130,3,64] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,3,64] 13 (by decide) (choices 1) [16,32,128] r17768 c17768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4542
  · exact u4543
  · exact u4544

def r17769 : Route 9 := (fun mask => (mask,id))

def c17769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17769 : Upper (D 7) (R 7) [12,288,65,130,3,128] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,3,128] 13 (by decide) (choices 1) [16,32] r17769 c17769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4545
  · exact u4546

def b17770 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 13 290 69 138 49 34 208 208 464), lower := (rows 13 290 69 138 49 34 64 128 256), losses := [] }

theorem u17770 : Upper (D 7) (R 7) [12,288,65,130,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17771 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 }], pairs := [(4,1),(4,6),(4,7)], upper := (rows 13 290 69 138 49 48 194 194 450), lower := (rows 13 290 69 138 49 48 64 128 256), losses := [] }

theorem u17771 : Upper (D 7) (R 7) [12,288,65,130,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17771 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17772 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 48, targets := 130 },{ cop := 4, region := 394, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,7)], upper := (rows 13 290 69 138 49 96 210 146 402), lower := (rows 13 290 69 138 49 96 64 128 256), losses := [] }

theorem u17772 : Upper (D 7) (R 7) [12,288,65,130,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17773 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 458, targets := 1 },{ cop := 4, region := 326, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 290 69 138 49 160 82 210 338), lower := (rows 13 290 69 138 49 160 64 128 256), losses := [] }

theorem u17773 : Upper (D 7) (R 7) [12,288,65,130,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17774 : Route 9 := (fun mask => (mask,id))

def c17774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17774 : Upper (D 7) (R 7) [12,288,65,130,66,1] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,66,1] 13 (by decide) (choices 1) [16,32,128] r17774 c17774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4547
  · exact u4548
  · exact u4549

def r17775 : Route 9 := (fun mask => (mask,id))

def c17775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17775 : Upper (D 7) (R 7) [12,288,65,130,66,16] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,66,16] 13 (by decide) (choices 1) [1,32,128] r17775 c17775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4550
  · exact u4551
  · exact u4552

def r17776 : Route 9 := (fun mask => (mask,id))

def c17776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17776 : Upper (D 7) (R 7) [12,288,65,130,66,128] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,66,128] 13 (by decide) (choices 1) [1,16,32] r17776 c17776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4553
  · exact u4554
  · exact u4555

def b17777 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 48, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 13 290 69 138 112 33 210 146 402), lower := (rows 13 290 69 138 112 33 64 128 256), losses := [] }

theorem u17777 : Upper (D 7) (R 7) [12,288,65,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17778 : Route 9 := (fun mask => (mask,id))

def c17778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17778 : Upper (D 7) (R 7) [12,288,65,130,96,2] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,96,2] 13 (by decide) (choices 1) [1,16,128] r17778 c17778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4556
  · exact u4557
  · exact u4558

def b17779 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 290 69 138 112 48 195 131 387), lower := (rows 13 290 69 138 112 48 64 128 256), losses := [] }

theorem u17779 : Upper (D 7) (R 7) [12,288,65,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17779 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17780 : Route 9 := (fun mask => (mask,id))

def c17780 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17780 : Upper (D 7) (R 7) [12,288,65,130,96,128] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,96,128] 13 (by decide) (choices 1) [1,2,16] r17780 c17780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4559
  · exact u4560
  · exact u4561

def b17781 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 4, region := 322, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 290 69 138 176 33 82 210 338), lower := (rows 13 290 69 138 176 33 64 128 256), losses := [] }

theorem u17781 : Upper (D 7) (R 7) [12,288,65,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17782 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 290 69 138 176 34 81 209 337), lower := (rows 13 290 69 138 176 34 64 128 256), losses := [] }

theorem u17782 : Upper (D 7) (R 7) [12,288,65,130,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17783 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 290 69 138 176 48 67 195 323), lower := (rows 13 290 69 138 176 48 64 128 256), losses := [] }

theorem u17783 : Upper (D 7) (R 7) [12,288,65,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17783 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17784 : Route 9 := (fun mask => (mask,id))

def c17784 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17784 : Upper (D 7) (R 7) [12,288,65,130,160,64] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,160,64] 13 (by decide) (choices 1) [1,2,16] r17784 c17784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4562
  · exact u4563
  · exact u4564

def r17785 : Route 9 := (fun mask => (mask,id))

def c17785 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17785 : Upper (D 7) (R 7) [12,288,65,130,192,1] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,192,1] 13 (by decide) (choices 1) [2,16,32] r17785 c17785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4565
  · exact u4566
  · exact u4567

def r17786 : Route 9 := (fun mask => (mask,id))

def c17786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17786 : Upper (D 7) (R 7) [12,288,65,130,192,2] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,192,2] 13 (by decide) (choices 1) [1,16,32] r17786 c17786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4568
  · exact u4569
  · exact u4570

def r17787 : Route 9 := (fun mask => (mask,id))

def c17787 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17787 : Upper (D 7) (R 7) [12,288,65,130,192,16] 13 := by
  apply FastRouting.sound _ _ [12,288,65,130,192,16] 13 (by decide) (choices 1) [1,2,32] r17787 c17787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4571
  · exact u4572
  · exact u4573

def b17788 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 13 290 69 152 19 34 224 224 480), lower := (rows 13 290 69 152 19 34 64 128 256), losses := [] }

theorem u17788 : Upper (D 7) (R 7) [12,288,65,144,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17789 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 5, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 13 290 69 152 19 96 226 162 418), lower := (rows 13 290 69 152 19 96 64 128 256), losses := [{ target := 6, region := (rows 1 34 4 24 16 32 0 162 290), good := (rows 13 418 5 152 411 418 0 128 256) }] }

theorem u17789 : Upper (D 7) (R 7) [12,288,65,144,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17790 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 5, region := 322, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(3,0)], upper := (rows 13 290 69 152 19 160 98 226 354), lower := (rows 13 290 69 152 19 160 64 128 256), losses := [{ target := 7, region := (rows 9 34 20 8 16 32 98 0 290), good := (rows 13 354 69 29 343 354 64 0 256) }] }

theorem u17790 : Upper (D 7) (R 7) [12,288,65,144,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17791 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 458, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 13 290 69 152 49 34 194 194 450), lower := (rows 13 290 69 152 49 34 64 128 256), losses := [] }

theorem u17791 : Upper (D 7) (R 7) [12,288,65,144,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17792 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 48, targets := 130 },{ cop := 4, region := 394, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,7)], upper := (rows 13 290 69 152 49 96 194 130 386), lower := (rows 13 290 69 152 49 96 64 128 256), losses := [] }

theorem u17792 : Upper (D 7) (R 7) [12,288,65,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17793 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 458, targets := 1 },{ cop := 4, region := 326, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 290 69 152 49 160 66 194 322), lower := (rows 13 290 69 152 49 160 64 128 256), losses := [] }

theorem u17793 : Upper (D 7) (R 7) [12,288,65,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17794 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 69 152 82 33 226 162 418), lower := (rows 13 290 69 152 82 33 64 128 256), losses := [] }

theorem u17794 : Upper (D 7) (R 7) [12,288,65,144,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17795 : Route 9 := (fun mask => (mask,id))

def c17795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17795 : Upper (D 7) (R 7) [12,288,65,144,66,2] 13 := by
  apply FastRouting.sound _ _ [12,288,65,144,66,2] 13 (by decide) (choices 1) [1,32,128] r17795 c17795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4574
  · exact u4575
  · exact u4576

def r17796 : Route 9 := (fun mask => (mask,id))

def c17796 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17796 : Upper (D 7) (R 7) [12,288,65,144,66,128] 13 := by
  apply FastRouting.sound _ _ [12,288,65,144,66,128] 13 (by decide) (choices 1) [1,2,32] r17796 c17796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4577
  · exact u4578
  · exact u4579

def b17797 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 48, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 13 290 69 152 112 33 194 130 386), lower := (rows 13 290 69 152 112 33 64 128 256), losses := [] }

theorem u17797 : Upper (D 7) (R 7) [12,288,65,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17798 : Route 9 := (fun mask => (mask,id))

def c17798 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17798 : Upper (D 7) (R 7) [12,288,65,144,96,2] 13 := by
  apply FastRouting.sound _ _ [12,288,65,144,96,2] 13 (by decide) (choices 1) [1,2,128] r17798 c17798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4580
  · exact u4581
  · exact u4582

def r17799 : Route 9 := (fun mask => (mask,id))

def c17799 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17799 : Upper (D 7) (R 7) [12,288,65,144,96,128] 13 := by
  apply FastRouting.sound _ _ [12,288,65,144,96,128] 13 (by decide) (choices 1) [1,2] r17799 c17799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4583
  · exact u4584

def b17800 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 13 290 69 168 19 34 208 208 464), lower := (rows 13 290 69 168 19 34 64 128 256), losses := [] }

theorem u17800 : Upper (D 7) (R 7) [12,288,65,160,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17801 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 4, region := 196, targets := 32 }], pairs := [(1,0),(2,5),(3,0)], upper := (rows 13 290 69 168 19 48 194 194 450), lower := (rows 13 290 69 168 19 48 64 128 256), losses := [] }

theorem u17801 : Upper (D 7) (R 7) [12,288,65,160,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17801 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17802 : Route 9 := (fun mask => (mask,id))

def c17802 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17802 : Upper (D 7) (R 7) [12,288,65,160,3,64] 13 := by
  apply FastRouting.sound _ _ [12,288,65,160,3,64] 13 (by decide) (choices 1) [2,16,128] r17802 c17802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4585
  · exact u4586
  · exact u4587

def b17803 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 69 168 19 160 82 210 338), lower := (rows 13 290 69 168 19 160 64 128 256), losses := [] }

theorem u17803 : Upper (D 7) (R 7) [12,288,65,160,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17804 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 290 69 168 82 33 210 146 402), lower := (rows 13 290 69 168 82 33 64 128 256), losses := [] }

theorem u17804 : Upper (D 7) (R 7) [12,288,65,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17805 : Route 9 := (fun mask => (mask,id))

def c17805 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17805 : Upper (D 7) (R 7) [12,288,65,160,66,2] 13 := by
  apply FastRouting.sound _ _ [12,288,65,160,66,2] 13 (by decide) (choices 1) [1,16,128] r17805 c17805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4588
  · exact u4589
  · exact u4590

def r17806 : Route 9 := (fun mask => (mask,id))

def c17806 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17806 : Upper (D 7) (R 7) [12,288,65,160,66,16] 13 := by
  apply FastRouting.sound _ _ [12,288,65,160,66,16] 13 (by decide) (choices 1) [1,2,128] r17806 c17806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4591
  · exact u4592
  · exact u4593

def b17807 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 69 168 82 160 83 147 275), lower := (rows 13 290 69 168 82 160 64 128 256), losses := [] }

theorem u17807 : Upper (D 7) (R 7) [12,288,65,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17808 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 290 69 168 146 33 82 210 338), lower := (rows 13 290 69 168 146 33 64 128 256), losses := [] }

theorem u17808 : Upper (D 7) (R 7) [12,288,65,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17809 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 13 290 69 168 146 34 81 209 337), lower := (rows 13 290 69 168 146 34 64 128 256), losses := [] }

theorem u17809 : Upper (D 7) (R 7) [12,288,65,160,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17810 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 69 168 146 48 67 195 323), lower := (rows 13 290 69 168 146 48 64 128 256), losses := [] }

theorem u17810 : Upper (D 7) (R 7) [12,288,65,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17810 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17811 : Route 9 := (fun mask => (mask,id))

def c17811 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17811 : Upper (D 7) (R 7) [12,288,65,160,130,64] 13 := by
  apply FastRouting.sound _ _ [12,288,65,160,130,64] 13 (by decide) (choices 1) [1,2,16] r17811 c17811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4594
  · exact u4595
  · exact u4596

def b17812 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 290 69 168 208 33 82 146 274), lower := (rows 13 290 69 168 208 33 64 128 256), losses := [] }

theorem u17812 : Upper (D 7) (R 7) [12,288,65,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17813 : Route 9 := (fun mask => (mask,id))

def c17813 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17813 : Upper (D 7) (R 7) [12,288,65,160,192,2] 13 := by
  apply FastRouting.sound _ _ [12,288,65,160,192,2] 13 (by decide) (choices 1) [1,2,16] r17813 c17813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4597
  · exact u4598
  · exact u4599

def b17814 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 290 69 168 208 48 67 131 259), lower := (rows 13 290 69 168 208 48 64 128 256), losses := [] }

theorem u17814 : Upper (D 7) (R 7) [12,288,65,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17814 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17815 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 57, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 13 290 70 88 49 33 194 130 386), lower := (rows 13 290 70 88 49 33 64 128 256), losses := [] }

theorem u17815 : Upper (D 7) (R 7) [12,288,66,80,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17816 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 57, targets := 128 },{ cop := 8, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(3,7),(4,7)], upper := (rows 13 290 70 88 49 34 193 129 385), lower := (rows 13 290 70 88 49 34 64 128 256), losses := [] }

theorem u17816 : Upper (D 7) (R 7) [12,288,66,80,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17817 : Route 9 := (fun mask => (mask,id))

def c17817 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17817 : Upper (D 7) (R 7) [12,288,66,80,33,128] 13 := by
  apply FastRouting.sound _ _ [12,288,66,80,33,128] 13 (by decide) (choices 1) [1,2,128] r17817 c17817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4600
  · exact u4601
  · exact u4602

def b17818 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 5, region := 454, targets := 1 }], pairs := [(1,0),(1,6),(2,0),(4,6)], upper := (rows 13 290 70 88 145 33 226 162 418), lower := (rows 13 290 70 88 145 33 64 128 256), losses := [] }

theorem u17818 : Upper (D 7) (R 7) [12,288,66,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17819 : PairBound 9 := { available := 161, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 13 290 70 88 145 34 225 161 417), lower := (rows 13 290 70 88 145 34 64 128 256), losses := [] }

theorem u17819 : Upper (D 7) (R 7) [12,288,66,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u17819
end Delivery.IrregularNine14.P07
