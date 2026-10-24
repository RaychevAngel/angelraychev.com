import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0106
import IrregularNine14P07C0107

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21660 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 13 138 84 33 240 176 432), lower := (rows 35 322 13 138 84 33 64 128 256), losses := [] }

theorem u21660 : Upper (D 7) (R 7) [34,320,9,130,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21661 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 2, region := 240, targets := 2 }], pairs := [(2,6),(3,6),(4,1)], upper := (rows 35 322 13 138 84 48 225 161 417), lower := (rows 35 322 13 138 84 48 64 128 256), losses := [] }

theorem u21661 : Upper (D 7) (R 7) [34,320,9,130,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21661 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21662 : Route 9 := (fun mask => (mask,id))

def c21662 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21662 : Upper (D 7) (R 7) [34,320,9,130,68,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,130,68,128] 13 (by decide) (choices 1) [1,16,32] r21662 c21662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6413
  · exact u6414
  · exact u6415

def b21663 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 13 138 112 33 212 148 404), lower := (rows 35 322 13 138 112 33 64 128 256), losses := [] }

theorem u21663 : Upper (D 7) (R 7) [34,320,9,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21664 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 322 13 138 112 36 209 145 401), lower := (rows 35 322 13 138 112 36 64 128 256), losses := [] }

theorem u21664 : Upper (D 7) (R 7) [34,320,9,130,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21664 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21665 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 13 138 112 48 197 133 389), lower := (rows 35 322 13 138 112 48 64 128 256), losses := [] }

theorem u21665 : Upper (D 7) (R 7) [34,320,9,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21665 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21666 : Route 9 := (fun mask => (mask,id))

def c21666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21666 : Upper (D 7) (R 7) [34,320,9,130,96,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,130,96,128] 13 (by decide) (choices 1) [1,4,16] r21666 c21666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6416
  · exact u6417
  · exact u6418

def b21667 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 322 13 138 145 36 112 240 368), lower := (rows 35 322 13 138 145 36 64 128 256), losses := [] }

theorem u21667 : Upper (D 7) (R 7) [34,320,9,130,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21667 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21668 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 322 13 138 145 48 100 228 356), lower := (rows 35 322 13 138 145 48 64 128 256), losses := [] }

theorem u21668 : Upper (D 7) (R 7) [34,320,9,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21668 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21669 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 138 145 96 116 180 308), lower := (rows 35 322 13 138 145 96 64 128 256), losses := [] }

theorem u21669 : Upper (D 7) (R 7) [34,320,9,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21670 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,6)], upper := (rows 35 322 13 138 148 33 112 240 368), lower := (rows 35 322 13 138 148 33 64 128 256), losses := [] }

theorem u21670 : Upper (D 7) (R 7) [34,320,9,130,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21671 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 322 13 138 148 48 97 225 353), lower := (rows 35 322 13 138 148 48 64 128 256), losses := [] }

theorem u21671 : Upper (D 7) (R 7) [34,320,9,130,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21671 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21672 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 138 148 96 113 177 305), lower := (rows 35 322 13 138 148 96 64 128 256), losses := [] }

theorem u21672 : Upper (D 7) (R 7) [34,320,9,130,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21673 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,6)], upper := (rows 35 322 13 138 176 33 84 212 340), lower := (rows 35 322 13 138 176 33 64 128 256), losses := [] }

theorem u21673 : Upper (D 7) (R 7) [34,320,9,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21674 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 322 13 138 176 36 81 209 337), lower := (rows 35 322 13 138 176 36 64 128 256), losses := [] }

theorem u21674 : Upper (D 7) (R 7) [34,320,9,130,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21674 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21675 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 13 138 176 48 69 197 325), lower := (rows 35 322 13 138 176 48 64 128 256), losses := [] }

theorem u21675 : Upper (D 7) (R 7) [34,320,9,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21675 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21676 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 138 176 96 85 149 277), lower := (rows 35 322 13 138 176 96 64 128 256), losses := [] }

theorem u21676 : Upper (D 7) (R 7) [34,320,9,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21677 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 322 13 138 208 33 116 180 308), lower := (rows 35 322 13 138 208 33 64 128 256), losses := [] }

theorem u21677 : Upper (D 7) (R 7) [34,320,9,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21678 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 322 13 138 208 36 113 177 305), lower := (rows 35 322 13 138 208 36 64 128 256), losses := [] }

theorem u21678 : Upper (D 7) (R 7) [34,320,9,130,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21678 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21679 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 2, region := 240, targets := 2 }], pairs := [(2,6),(3,6),(4,1)], upper := (rows 35 322 13 138 208 48 101 165 293), lower := (rows 35 322 13 138 208 48 64 128 256), losses := [] }

theorem u21679 : Upper (D 7) (R 7) [34,320,9,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21679 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21680 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 140 81 34 240 176 432), lower := (rows 35 322 13 140 81 34 64 128 256), losses := [] }

theorem u21680 : Upper (D 7) (R 7) [34,320,9,132,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21681 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 322 13 140 81 48 226 162 418), lower := (rows 35 322 13 140 81 48 64 128 256), losses := [] }

theorem u21681 : Upper (D 7) (R 7) [34,320,9,132,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21681 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21682 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 4, region := 418, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 35 322 13 140 81 160 114 178 306), lower := (rows 35 322 13 140 81 160 64 128 256), losses := [] }

theorem u21682 : Upper (D 7) (R 7) [34,320,9,132,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21683 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(1,0),(4,0),(4,7)], upper := (rows 35 322 13 140 112 33 210 146 402), lower := (rows 35 322 13 140 112 33 64 128 256), losses := [] }

theorem u21683 : Upper (D 7) (R 7) [34,320,9,132,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21684 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 140 112 34 209 145 401), lower := (rows 35 322 13 140 112 34 64 128 256), losses := [] }

theorem u21684 : Upper (D 7) (R 7) [34,320,9,132,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21685 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 13 140 112 48 195 131 387), lower := (rows 35 322 13 140 112 48 64 128 256), losses := [] }

theorem u21685 : Upper (D 7) (R 7) [34,320,9,132,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21685 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21686 : Route 9 := (fun mask => (mask,id))

def c21686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21686 : Upper (D 7) (R 7) [34,320,9,132,96,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,132,96,128] 13 (by decide) (choices 1) [1,2,16] r21686 c21686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6419
  · exact u6420
  · exact u6421

def b21687 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 35 322 13 140 146 33 112 240 368), lower := (rows 35 322 13 140 146 33 64 128 256), losses := [] }

theorem u21687 : Upper (D 7) (R 7) [34,320,9,132,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21688 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 322 13 140 146 48 97 225 353), lower := (rows 35 322 13 140 146 48 64 128 256), losses := [] }

theorem u21688 : Upper (D 7) (R 7) [34,320,9,132,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21688 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21689 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 140 146 96 113 177 305), lower := (rows 35 322 13 140 146 96 64 128 256), losses := [] }

theorem u21689 : Upper (D 7) (R 7) [34,320,9,132,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21690 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(1,0),(4,0)], upper := (rows 35 322 13 140 176 33 82 210 338), lower := (rows 35 322 13 140 176 33 64 128 256), losses := [] }

theorem u21690 : Upper (D 7) (R 7) [34,320,9,132,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21691 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 140 176 34 81 209 337), lower := (rows 35 322 13 140 176 34 64 128 256), losses := [] }

theorem u21691 : Upper (D 7) (R 7) [34,320,9,132,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21692 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 322 13 140 176 48 67 195 323), lower := (rows 35 322 13 140 176 48 64 128 256), losses := [] }

theorem u21692 : Upper (D 7) (R 7) [34,320,9,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21692 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21693 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 140 176 96 83 147 275), lower := (rows 35 322 13 140 176 96 64 128 256), losses := [] }

theorem u21693 : Upper (D 7) (R 7) [34,320,9,132,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21694 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(1,0),(4,0)], upper := (rows 35 322 13 140 208 33 114 178 306), lower := (rows 35 322 13 140 208 33 64 128 256), losses := [] }

theorem u21694 : Upper (D 7) (R 7) [34,320,9,132,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21695 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 140 208 34 113 177 305), lower := (rows 35 322 13 140 208 34 64 128 256), losses := [] }

theorem u21695 : Upper (D 7) (R 7) [34,320,9,132,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21696 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 322 13 140 208 48 99 163 291), lower := (rows 35 322 13 140 208 48 64 128 256), losses := [] }

theorem u21696 : Upper (D 7) (R 7) [34,320,9,132,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21696 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21697 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 450, targets := 1 }], pairs := [(0,6),(0,7),(1,0),(3,0)], upper := (rows 35 322 13 152 22 33 224 224 480), lower := (rows 35 322 13 152 22 33 64 128 256), losses := [{ target := 0, region := (rows 0 39 4 12 20 32 97 161 289), good := (rows 482 322 478 152 30 482 64 128 256) }] }

theorem u21697 : Upper (D 7) (R 7) [34,320,9,144,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21698 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 152 22 96 225 161 417), lower := (rows 35 322 13 152 22 96 64 128 256), losses := [] }

theorem u21698 : Upper (D 7) (R 7) [34,320,9,144,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21699 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,1),(4,7)], upper := (rows 35 322 13 152 22 160 97 225 353), lower := (rows 35 322 13 152 22 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 189 69 133 261), good := (rows 481 320 493 184 508 160 64 160 256) },{ target := 7, region := (rows 33 39 4 8 20 32 97 0 289), good := (rows 355 322 351 24 22 355 64 0 256) }] }

theorem u21699 : Upper (D 7) (R 7) [34,320,9,144,6,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21700 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 322 13 152 52 33 194 194 450), lower := (rows 35 322 13 152 52 33 64 128 256), losses := [] }

theorem u21700 : Upper (D 7) (R 7) [34,320,9,144,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21701 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 152 52 34 193 193 449), lower := (rows 35 322 13 152 52 34 64 128 256), losses := [] }

theorem u21701 : Upper (D 7) (R 7) [34,320,9,144,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21702 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 152 52 96 195 131 387), lower := (rows 35 322 13 152 52 96 64 128 256), losses := [] }

theorem u21702 : Upper (D 7) (R 7) [34,320,9,144,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21703 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 323, targets := 128 },{ cop := 0, region := 322, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(4,0)], upper := (rows 35 322 13 152 52 160 67 195 323), lower := (rows 35 322 13 152 52 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 34 322 60 184 52 160 64 160 256) }] }

theorem u21703 : Upper (D 7) (R 7) [34,320,9,144,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21704 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 152 81 34 228 164 420), lower := (rows 35 322 13 152 81 34 64 128 256), losses := [] }

theorem u21704 : Upper (D 7) (R 7) [34,320,9,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21705 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 450, targets := 1 }], pairs := [(1,0),(2,6),(3,0)], upper := (rows 35 322 13 152 81 36 226 162 418), lower := (rows 35 322 13 152 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 55 4 24 16 36 101 165 293), good := (rows 482 322 494 154 474 486 64 128 256) },{ target := 6, region := (rows 1 2 20 24 16 60 0 129 257), good := (rows 419 258 429 188 445 36 0 128 256) }] }

theorem u21705 : Upper (D 7) (R 7) [34,320,9,144,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21705 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21706 : Route 9 := (fun mask => (mask,id))

def c21706 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21706 : Upper (D 7) (R 7) [34,320,9,144,65,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,144,65,128] 13 (by decide) (choices 1) [2,4,32] r21706 c21706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6422
  · exact u6423
  · exact u6424

def b21707 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 450, targets := 1 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(3,0)], upper := (rows 35 322 13 152 84 33 226 162 418), lower := (rows 35 322 13 152 84 33 64 128 256), losses := [{ target := 0, region := (rows 0 39 4 12 20 32 97 161 289), good := (rows 482 322 478 152 94 482 64 128 256) }] }

theorem u21707 : Upper (D 7) (R 7) [34,320,9,144,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21708 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 152 84 34 225 161 417), lower := (rows 35 322 13 152 84 34 64 128 256), losses := [] }

theorem u21708 : Upper (D 7) (R 7) [34,320,9,144,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21709 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,7)], upper := (rows 35 322 13 152 84 160 99 163 291), lower := (rows 35 322 13 152 84 160 64 128 256), losses := [{ target := 7, region := (rows 33 39 4 8 20 32 97 0 289), good := (rows 355 322 351 24 86 355 64 0 256) }] }

theorem u21709 : Upper (D 7) (R 7) [34,320,9,144,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21710 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 2, region := 450, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(4,7)], upper := (rows 35 322 13 152 112 33 198 134 390), lower := (rows 35 322 13 152 112 33 64 128 256), losses := [] }

theorem u21710 : Upper (D 7) (R 7) [34,320,9,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21711 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 152 112 34 197 133 389), lower := (rows 35 322 13 152 112 34 64 128 256), losses := [] }

theorem u21711 : Upper (D 7) (R 7) [34,320,9,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21712 : Route 9 := (fun mask => (mask,id))

def c21712 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21712 : Upper (D 7) (R 7) [34,320,9,144,96,4] 13 := by
  apply FastRouting.sound _ _ [34,320,9,144,96,4] 13 (by decide) (choices 1) [1,2,128] r21712 c21712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6425
  · exact u6426
  · exact u6427

def r21713 : Route 9 := (fun mask => (mask,id))

def c21713 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21713 : Upper (D 7) (R 7) [34,320,9,144,96,128] 13 := by
  apply FastRouting.sound _ _ [34,320,9,144,96,128] 13 (by decide) (choices 1) [1,2,4] r21713 c21713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6428
  · exact u6429
  · exact u6430

def b21714 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 322 13 168 22 33 208 208 464), lower := (rows 35 322 13 168 22 33 64 128 256), losses := [] }

theorem u21714 : Upper (D 7) (R 7) [34,320,9,160,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21715 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 35 322 13 168 22 48 193 193 449), lower := (rows 35 322 13 168 22 48 64 128 256), losses := [] }

theorem u21715 : Upper (D 7) (R 7) [34,320,9,160,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21715 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21716 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 156, targets := 64 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 322 13 168 22 96 209 145 401), lower := (rows 35 322 13 168 22 96 64 128 256), losses := [] }

theorem u21716 : Upper (D 7) (R 7) [34,320,9,160,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21717 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 322 13 168 22 160 81 209 337), lower := (rows 35 322 13 168 22 160 64 128 256), losses := [] }

theorem u21717 : Upper (D 7) (R 7) [34,320,9,160,6,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21718 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 322 13 168 81 34 212 148 404), lower := (rows 35 322 13 168 81 34 64 128 256), losses := [] }

theorem u21718 : Upper (D 7) (R 7) [34,320,9,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21719 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 386, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 35 322 13 168 81 36 210 146 402), lower := (rows 35 322 13 168 81 36 64 128 256), losses := [] }

theorem u21719 : Upper (D 7) (R 7) [34,320,9,160,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21719 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u21719
end Delivery.IrregularNine14.P07
