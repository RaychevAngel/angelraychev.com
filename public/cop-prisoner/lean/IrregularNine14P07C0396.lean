import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0127

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23760 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 14 392 208 48 67 131 259), lower := (rows 37 98 14 392 208 48 64 128 256), losses := [] }

theorem u23760 : Upper (D 7) (R 7) [36,96,10,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23760 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23761 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 28 11 145 34 448 448 448), lower := (rows 37 98 28 11 145 34 64 128 256), losses := [] }

theorem u23761 : Upper (D 7) (R 7) [36,96,24,3,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23762 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 28 11 145 96 450 386 386), lower := (rows 37 98 28 11 145 96 64 128 256), losses := [] }

theorem u23762 : Upper (D 7) (R 7) [36,96,24,3,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23763 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7),(4,5)], upper := (rows 37 98 28 11 145 160 322 450 322), lower := (rows 37 98 28 11 145 160 64 128 256), losses := [] }

theorem u23763 : Upper (D 7) (R 7) [36,96,24,3,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23764 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 0, region := 194, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 37 98 28 11 145 288 194 194 450), lower := (rows 37 98 28 11 145 288 64 128 256), losses := [] }

theorem u23764 : Upper (D 7) (R 7) [36,96,24,3,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23764 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23765 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 28 11 146 33 448 448 448), lower := (rows 37 98 28 11 146 33 64 128 256), losses := [] }

theorem u23765 : Upper (D 7) (R 7) [36,96,24,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23766 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 28 11 146 96 449 385 385), lower := (rows 37 98 28 11 146 96 64 128 256), losses := [] }

theorem u23766 : Upper (D 7) (R 7) [36,96,24,3,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23767 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,6),(1,7),(2,6),(3,6)], upper := (rows 37 98 28 11 146 160 321 449 321), lower := (rows 37 98 28 11 146 160 64 128 256), losses := [] }

theorem u23767 : Upper (D 7) (R 7) [36,96,24,3,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23768 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 212, targets := 32 },{ cop := 2, region := 481, targets := 2 }], pairs := [(0,1),(2,5),(4,5)], upper := (rows 37 98 28 11 146 288 193 193 449), lower := (rows 37 98 28 11 146 288 64 128 256), losses := [] }

theorem u23768 : Upper (D 7) (R 7) [36,96,24,3,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23768 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23769 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 28 11 208 33 450 386 386), lower := (rows 37 98 28 11 208 33 64 128 256), losses := [] }

theorem u23769 : Upper (D 7) (R 7) [36,96,24,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23770 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 28 11 208 34 449 385 385), lower := (rows 37 98 28 11 208 34 64 128 256), losses := [] }

theorem u23770 : Upper (D 7) (R 7) [36,96,24,3,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23771 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7),(4,5)], upper := (rows 37 98 28 11 208 160 323 387 259), lower := (rows 37 98 28 11 208 160 64 128 256), losses := [] }

theorem u23771 : Upper (D 7) (R 7) [36,96,24,3,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23772 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 37 98 28 11 208 288 195 131 387), lower := (rows 37 98 28 11 208 288 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 300 0 136 264), good := (rows 37 34 445 427 144 288 0 128 288) }] }

theorem u23772 : Upper (D 7) (R 7) [36,96,24,3,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23772 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23773 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 28 11 273 34 192 192 448), lower := (rows 37 98 28 11 273 34 64 128 256), losses := [] }

theorem u23773 : Upper (D 7) (R 7) [36,96,24,3,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23774 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 28 11 273 96 194 130 386), lower := (rows 37 98 28 11 273 96 64 128 256), losses := [] }

theorem u23774 : Upper (D 7) (R 7) [36,96,24,3,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23775 : Route 9 := (fun mask => (mask,id))

def c23775 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23775 : Upper (D 7) (R 7) [36,96,24,3,257,128] 13 := by
  apply FastRouting.sound _ _ [36,96,24,3,257,128] 13 (by decide) (choices 1) [2,128] r23775 c23775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7643
  · exact u7644

def b23776 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 28 11 274 33 192 192 448), lower := (rows 37 98 28 11 274 33 64 128 256), losses := [] }

theorem u23776 : Upper (D 7) (R 7) [36,96,24,3,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23777 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 28 11 274 96 193 129 385), lower := (rows 37 98 28 11 274 96 64 128 256), losses := [] }

theorem u23777 : Upper (D 7) (R 7) [36,96,24,3,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23778 : Route 9 := (fun mask => (mask,id))

def c23778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23778 : Upper (D 7) (R 7) [36,96,24,3,258,128] 13 := by
  apply FastRouting.sound _ _ [36,96,24,3,258,128] 13 (by decide) (choices 1) [1,128] r23778 c23778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7645
  · exact u7646

def b23779 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 28 11 336 33 194 130 386), lower := (rows 37 98 28 11 336 33 64 128 256), losses := [] }

theorem u23779 : Upper (D 7) (R 7) [36,96,24,3,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23780 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 28 11 336 34 193 129 385), lower := (rows 37 98 28 11 336 34 64 128 256), losses := [] }

theorem u23780 : Upper (D 7) (R 7) [36,96,24,3,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23781 : Route 9 := (fun mask => (mask,id))

def c23781 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23781 : Upper (D 7) (R 7) [36,96,24,3,320,128] 13 := by
  apply FastRouting.sound _ _ [36,96,24,3,320,128] 13 (by decide) (choices 1) [1,2,128] r23781 c23781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7647
  · exact u7648
  · exact u7649

def b23782 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 28 11 400 33 194 194 450), lower := (rows 37 98 28 11 400 33 64 128 256), losses := [] }

theorem u23782 : Upper (D 7) (R 7) [36,96,24,3,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23783 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 28 11 400 34 193 193 449), lower := (rows 37 98 28 11 400 34 64 128 256), losses := [] }

theorem u23783 : Upper (D 7) (R 7) [36,96,24,3,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23784 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 28 11 400 96 195 131 387), lower := (rows 37 98 28 11 400 96 64 128 256), losses := [] }

theorem u23784 : Upper (D 7) (R 7) [36,96,24,3,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23785 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7),(4,5)], upper := (rows 37 98 28 11 400 160 67 195 323), lower := (rows 37 98 28 11 400 160 64 128 256), losses := [] }

theorem u23785 : Upper (D 7) (R 7) [36,96,24,3,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23786 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 450, targets := 1 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(3,5)], upper := (rows 37 98 28 73 145 34 450 386 386), lower := (rows 37 98 28 73 145 34 64 128 256), losses := [{ target := 5, region := (rows 1 2 29 9 17 0 98 162 290), good := (rows 477 450 28 93 157 450 64 128 256) }] }

theorem u23786 : Upper (D 7) (R 7) [36,96,24,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23787 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 0, region := 322, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(3,7)], upper := (rows 37 98 28 73 145 160 322 386 258), lower := (rows 37 98 28 73 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 96 61 73 177 160 64 160 256) }] }

theorem u23787 : Upper (D 7) (R 7) [36,96,24,65,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23788 : Route 9 := (fun mask => (mask,id))

def c23788 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23788 : Upper (D 7) (R 7) [36,96,24,65,129,256] 13 := by
  apply FastRouting.sound _ _ [36,96,24,65,129,256] 13 (by decide) (choices 1) [2,128] r23788 c23788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7650
  · exact u7651

def b23789 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 28 73 146 33 450 386 386), lower := (rows 37 98 28 73 146 33 64 128 256), losses := [] }

theorem u23789 : Upper (D 7) (R 7) [36,96,24,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23790 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 456, targets := 34 },{ cop := 3, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,5)], upper := (rows 37 98 28 73 146 34 449 385 385), lower := (rows 37 98 28 73 146 34 64 128 256), losses := [] }

theorem u23790 : Upper (D 7) (R 7) [36,96,24,65,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23791 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 98 28 73 146 160 323 387 259), lower := (rows 37 98 28 73 146 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 96 61 73 176 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 34 61 9 178 160 0 160 256) }] }

theorem u23791 : Upper (D 7) (R 7) [36,96,24,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23792 : Route 9 := (fun mask => (mask,id))

def c23792 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23792 : Upper (D 7) (R 7) [36,96,24,65,130,256] 13 := by
  apply FastRouting.sound _ _ [36,96,24,65,130,256] 13 (by decide) (choices 1) [1,2,128] r23792 c23792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7652
  · exact u7653
  · exact u7654

def b23793 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 194, targets := 1 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(3,5)], upper := (rows 37 98 28 73 273 34 194 130 386), lower := (rows 37 98 28 73 273 34 64 128 256), losses := [{ target := 5, region := (rows 1 2 29 9 17 0 98 162 290), good := (rows 477 450 28 93 285 450 64 128 256) }] }

theorem u23793 : Upper (D 7) (R 7) [36,96,24,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23794 : Route 9 := (fun mask => (mask,id))

def c23794 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23794 : Upper (D 7) (R 7) [36,96,24,65,257,128] 13 := by
  apply FastRouting.sound _ _ [36,96,24,65,257,128] 13 (by decide) (choices 1) [2,128] r23794 c23794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7655
  · exact u7656

def b23795 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 28 73 274 33 194 130 386), lower := (rows 37 98 28 73 274 33 64 128 256), losses := [] }

theorem u23795 : Upper (D 7) (R 7) [36,96,24,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23796 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 3, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,5)], upper := (rows 37 98 28 73 274 34 193 129 385), lower := (rows 37 98 28 73 274 34 64 128 256), losses := [] }

theorem u23796 : Upper (D 7) (R 7) [36,96,24,65,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23797 : Route 9 := (fun mask => (mask,id))

def c23797 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23797 : Upper (D 7) (R 7) [36,96,24,65,258,128] 13 := by
  apply FastRouting.sound _ _ [36,96,24,65,258,128] 13 (by decide) (choices 1) [1,2,128] r23797 c23797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7657
  · exact u7658
  · exact u7659

def b23798 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 28 73 400 33 194 130 386), lower := (rows 37 98 28 73 400 33 64 128 256), losses := [] }

theorem u23798 : Upper (D 7) (R 7) [36,96,24,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23799 : Route 9 := (fun mask => (mask,id))

def c23799 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23799 : Upper (D 7) (R 7) [36,96,24,65,384,2] 13 := by
  apply FastRouting.sound _ _ [36,96,24,65,384,2] 13 (by decide) (choices 1) [1,2,128] r23799 c23799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7660
  · exact u7661
  · exact u7662

def b23800 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 98 28 73 400 160 67 131 259), lower := (rows 37 98 28 73 400 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 96 61 73 432 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 34 61 9 432 160 0 160 256) }] }

theorem u23800 : Upper (D 7) (R 7) [36,96,24,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23801 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 28 137 146 33 322 450 322), lower := (rows 37 98 28 137 146 33 64 128 256), losses := [] }

theorem u23801 : Upper (D 7) (R 7) [36,96,24,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23802 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 0, region := 456, targets := 2 }], pairs := [(0,6),(2,6),(3,1),(3,6)], upper := (rows 37 98 28 137 146 34 321 449 321), lower := (rows 37 98 28 137 146 34 64 128 256), losses := [] }

theorem u23802 : Upper (D 7) (R 7) [36,96,24,129,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23803 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 28 137 146 96 323 387 259), lower := (rows 37 98 28 137 146 96 64 128 256), losses := [] }

theorem u23803 : Upper (D 7) (R 7) [36,96,24,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23804 : Route 9 := (fun mask => (mask,id))

def c23804 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23804 : Upper (D 7) (R 7) [36,96,24,129,130,256] 13 := by
  apply FastRouting.sound _ _ [36,96,24,129,130,256] 13 (by decide) (choices 1) [1,2] r23804 c23804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7663
  · exact u7664

def b23805 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 28 137 208 33 322 386 258), lower := (rows 37 98 28 137 208 33 64 128 256), losses := [] }

theorem u23805 : Upper (D 7) (R 7) [36,96,24,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23805 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23806 : Route 9 := (fun mask => (mask,id))

def c23806 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u23806 : Upper (D 7) (R 7) [36,96,24,129,192,2] 13 := by
  apply FastRouting.sound _ _ [36,96,24,129,192,2] 13 (by decide) (choices 1) [1,2,256] r23806 c23806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7665
  · exact u7666
  · exact u7667

def r23807 : Route 9 := (fun mask => (mask,id))

def c23807 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23807 : Upper (D 7) (R 7) [36,96,24,129,192,256] 13 := by
  apply FastRouting.sound _ _ [36,96,24,129,192,256] 13 (by decide) (choices 1) [1,2] r23807 c23807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7668
  · exact u7669

def b23808 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 194, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(3,5)], upper := (rows 37 98 28 137 273 34 194 194 450), lower := (rows 37 98 28 137 273 34 64 128 256), losses := [{ target := 5, region := (rows 1 2 29 9 17 0 98 162 290), good := (rows 477 450 28 157 285 450 64 128 256) }] }

theorem u23808 : Upper (D 7) (R 7) [36,96,24,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23809 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 28 137 273 96 194 130 386), lower := (rows 37 98 28 137 273 96 64 128 256), losses := [] }

theorem u23809 : Upper (D 7) (R 7) [36,96,24,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23810 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(4,7)], upper := (rows 37 98 28 137 273 160 66 194 322), lower := (rows 37 98 28 137 273 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 61 169 273 160 64 160 256) }] }

theorem u23810 : Upper (D 7) (R 7) [36,96,24,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23811 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 28 137 274 33 194 194 450), lower := (rows 37 98 28 137 274 33 64 128 256), losses := [] }

theorem u23811 : Upper (D 7) (R 7) [36,96,24,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23812 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,5)], upper := (rows 37 98 28 137 274 34 193 193 449), lower := (rows 37 98 28 137 274 34 64 128 256), losses := [] }

theorem u23812 : Upper (D 7) (R 7) [36,96,24,129,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23813 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 28 137 274 96 195 131 387), lower := (rows 37 98 28 137 274 96 64 128 256), losses := [] }

theorem u23813 : Upper (D 7) (R 7) [36,96,24,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23814 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 98 28 137 274 160 67 195 323), lower := (rows 37 98 28 137 274 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 61 169 272 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 34 61 169 274 160 0 160 256) }] }

theorem u23814 : Upper (D 7) (R 7) [36,96,24,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23815 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 28 137 336 33 194 130 386), lower := (rows 37 98 28 137 336 33 64 128 256), losses := [] }

theorem u23815 : Upper (D 7) (R 7) [36,96,24,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23816 : Route 9 := (fun mask => (mask,id))

def c23816 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23816 : Upper (D 7) (R 7) [36,96,24,129,320,2] 13 := by
  apply FastRouting.sound _ _ [36,96,24,129,320,2] 13 (by decide) (choices 1) [1,2,128] r23816 c23816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7670
  · exact u7671
  · exact u7672

def b23817 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 98 28 137 336 160 67 131 259), lower := (rows 37 98 28 137 336 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 61 169 336 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 34 61 169 272 160 0 160 256) }] }

theorem u23817 : Upper (D 7) (R 7) [36,96,24,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23818 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 28 137 400 33 66 194 322), lower := (rows 37 98 28 137 400 33 64 128 256), losses := [] }

theorem u23818 : Upper (D 7) (R 7) [36,96,24,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23819 : Route 9 := (fun mask => (mask,id))

def c23819 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23819 : Upper (D 7) (R 7) [36,96,24,129,384,2] 13 := by
  apply FastRouting.sound _ _ [36,96,24,129,384,2] 13 (by decide) (choices 1) [1,2] r23819 c23819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7673
  · exact u7674

#print axioms u23819
end Delivery.IrregularNine14.P07
