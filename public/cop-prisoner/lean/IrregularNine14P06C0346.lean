import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0101
import IrregularNine14P06C0102

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20760 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 388 56 81 40 71 135 263), lower := (rows 35 70 388 56 81 40 64 128 256), losses := [] }

theorem u20760 : Upper (D 6) (R 6) [34,68,384,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20760 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20761 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 74 52 13 146 33 324 452 324), lower := (rows 35 74 52 13 146 33 64 128 256), losses := [] }

theorem u20761 : Upper (D 6) (R 6) [34,72,48,5,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20762 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 74 52 13 146 36 321 449 321), lower := (rows 35 74 52 13 146 36 64 128 256), losses := [] }

theorem u20762 : Upper (D 6) (R 6) [34,72,48,5,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20763 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 52 13 146 96 325 389 261), lower := (rows 35 74 52 13 146 96 64 128 256), losses := [] }

theorem u20763 : Upper (D 6) (R 6) [34,72,48,5,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20764 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 74 52 13 146 288 69 197 325), lower := (rows 35 74 52 13 146 288 64 128 256), losses := [] }

theorem u20764 : Upper (D 6) (R 6) [34,72,48,5,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20764 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20765 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 74 52 13 208 33 326 390 262), lower := (rows 35 74 52 13 208 33 64 128 256), losses := [] }

theorem u20765 : Upper (D 6) (R 6) [34,72,48,5,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20766 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 52 13 208 34 325 389 261), lower := (rows 35 74 52 13 208 34 64 128 256), losses := [] }

theorem u20766 : Upper (D 6) (R 6) [34,72,48,5,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20767 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 74 52 13 208 36 323 387 259), lower := (rows 35 74 52 13 208 36 64 128 256), losses := [] }

theorem u20767 : Upper (D 6) (R 6) [34,72,48,5,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20768 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 74 52 13 208 288 71 135 263), lower := (rows 35 74 52 13 208 288 64 128 256), losses := [] }

theorem u20768 : Upper (D 6) (R 6) [34,72,48,5,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20768 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20769 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 74 52 13 400 33 70 198 326), lower := (rows 35 74 52 13 400 33 64 128 256), losses := [] }

theorem u20769 : Upper (D 6) (R 6) [34,72,48,5,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20770 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 52 13 400 34 69 197 325), lower := (rows 35 74 52 13 400 34 64 128 256), losses := [] }

theorem u20770 : Upper (D 6) (R 6) [34,72,48,5,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20771 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 74 52 13 400 36 67 195 323), lower := (rows 35 74 52 13 400 36 64 128 256), losses := [] }

theorem u20771 : Upper (D 6) (R 6) [34,72,48,5,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20772 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 52 13 400 96 71 135 263), lower := (rows 35 74 52 13 400 96 64 128 256), losses := [] }

theorem u20772 : Upper (D 6) (R 6) [34,72,48,5,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20773 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 52 14 145 33 324 452 324), lower := (rows 35 74 52 14 145 33 64 128 256), losses := [] }

theorem u20773 : Upper (D 6) (R 6) [34,72,48,6,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20774 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 464, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 74 52 14 145 36 321 449 321), lower := (rows 35 74 52 14 145 36 64 128 256), losses := [] }

theorem u20774 : Upper (D 6) (R 6) [34,72,48,6,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20775 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 52 14 145 96 325 389 261), lower := (rows 35 74 52 14 145 96 64 128 256), losses := [] }

theorem u20775 : Upper (D 6) (R 6) [34,72,48,6,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20776 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 52 14 145 288 69 197 325), lower := (rows 35 74 52 14 145 288 64 128 256), losses := [] }

theorem u20776 : Upper (D 6) (R 6) [34,72,48,6,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20776 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20777 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 52 14 400 33 69 197 325), lower := (rows 35 74 52 14 400 33 64 128 256), losses := [] }

theorem u20777 : Upper (D 6) (R 6) [34,72,48,6,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20778 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 52 14 400 36 65 193 321), lower := (rows 35 74 52 14 400 36 64 128 256), losses := [] }

theorem u20778 : Upper (D 6) (R 6) [34,72,48,6,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20779 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 52 14 400 96 69 133 261), lower := (rows 35 74 52 14 400 96 64 128 256), losses := [] }

theorem u20779 : Upper (D 6) (R 6) [34,72,48,6,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20780 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 52 137 81 34 324 388 260), lower := (rows 35 74 52 137 81 34 64 128 256), losses := [] }

theorem u20780 : Upper (D 6) (R 6) [34,72,48,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20781 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 52 137 81 36 326 390 262), lower := (rows 35 74 52 137 81 36 64 128 256), losses := [] }

theorem u20781 : Upper (D 6) (R 6) [34,72,48,129,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20782 : Route 9 := (fun mask => (mask,id))

def c20782 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20782 : Upper (D 6) (R 6) [34,72,48,129,65,256] 13 := by
  apply FastRouting.sound _ _ [34,72,48,129,65,256] 13 (by decide) (choices 1) [2,4] r20782 c20782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6116
  · exact u6117

def b20783 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 52 137 84 33 326 390 262), lower := (rows 35 74 52 137 84 33 64 128 256), losses := [] }

theorem u20783 : Upper (D 6) (R 6) [34,72,48,129,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20784 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 52 137 84 34 325 389 261), lower := (rows 35 74 52 137 84 34 64 128 256), losses := [] }

theorem u20784 : Upper (D 6) (R 6) [34,72,48,129,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20785 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 52 137 84 36 323 387 259), lower := (rows 35 74 52 137 84 36 64 128 256), losses := [] }

theorem u20785 : Upper (D 6) (R 6) [34,72,48,129,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20786 : Route 9 := (fun mask => (mask,id))

def c20786 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20786 : Upper (D 6) (R 6) [34,72,48,129,68,256] 13 := by
  apply FastRouting.sound _ _ [34,72,48,129,68,256] 13 (by decide) (choices 1) [1,2,4] r20786 c20786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6118
  · exact u6119
  · exact u6120

def b20787 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 52 137 273 34 68 196 324), lower := (rows 35 74 52 137 273 34 64 128 256), losses := [] }

theorem u20787 : Upper (D 6) (R 6) [34,72,48,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20788 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 52 137 273 36 70 198 326), lower := (rows 35 74 52 137 273 36 64 128 256), losses := [] }

theorem u20788 : Upper (D 6) (R 6) [34,72,48,129,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20789 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 52 137 273 96 70 134 262), lower := (rows 35 74 52 137 273 96 64 128 256), losses := [] }

theorem u20789 : Upper (D 6) (R 6) [34,72,48,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20790 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 52 137 274 33 68 196 324), lower := (rows 35 74 52 137 274 33 64 128 256), losses := [] }

theorem u20790 : Upper (D 6) (R 6) [34,72,48,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20791 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 74 52 137 274 36 69 197 325), lower := (rows 35 74 52 137 274 36 64 128 256), losses := [] }

theorem u20791 : Upper (D 6) (R 6) [34,72,48,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20792 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 52 137 274 96 69 133 261), lower := (rows 35 74 52 137 274 96 64 128 256), losses := [] }

theorem u20792 : Upper (D 6) (R 6) [34,72,48,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20793 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 52 137 276 33 70 198 326), lower := (rows 35 74 52 137 276 33 64 128 256), losses := [] }

theorem u20793 : Upper (D 6) (R 6) [34,72,48,129,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20794 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 52 137 276 34 69 197 325), lower := (rows 35 74 52 137 276 34 64 128 256), losses := [] }

theorem u20794 : Upper (D 6) (R 6) [34,72,48,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20795 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 52 137 276 36 67 195 323), lower := (rows 35 74 52 137 276 36 64 128 256), losses := [] }

theorem u20795 : Upper (D 6) (R 6) [34,72,48,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20796 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 52 137 276 96 71 135 263), lower := (rows 35 74 52 137 276 96 64 128 256), losses := [] }

theorem u20796 : Upper (D 6) (R 6) [34,72,48,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20797 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 52 137 336 33 70 134 262), lower := (rows 35 74 52 137 336 33 64 128 256), losses := [] }

theorem u20797 : Upper (D 6) (R 6) [34,72,48,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20798 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 52 137 336 34 69 133 261), lower := (rows 35 74 52 137 336 34 64 128 256), losses := [] }

theorem u20798 : Upper (D 6) (R 6) [34,72,48,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20799 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 52 137 336 36 71 135 263), lower := (rows 35 74 52 137 336 36 64 128 256), losses := [] }

theorem u20799 : Upper (D 6) (R 6) [34,72,48,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20800 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 52 138 84 33 325 389 261), lower := (rows 35 74 52 138 84 33 64 128 256), losses := [] }

theorem u20800 : Upper (D 6) (R 6) [34,72,48,130,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20801 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 52 138 84 36 321 385 257), lower := (rows 35 74 52 138 84 36 64 128 256), losses := [] }

theorem u20801 : Upper (D 6) (R 6) [34,72,48,130,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20802 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 52 138 84 288 69 133 261), lower := (rows 35 74 52 138 84 288 64 128 256), losses := [] }

theorem u20802 : Upper (D 6) (R 6) [34,72,48,130,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20802 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20803 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 52 138 273 33 68 196 324), lower := (rows 35 74 52 138 273 33 64 128 256), losses := [] }

theorem u20803 : Upper (D 6) (R 6) [34,72,48,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20804 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 74 52 138 273 36 69 197 325), lower := (rows 35 74 52 138 273 36 64 128 256), losses := [] }

theorem u20804 : Upper (D 6) (R 6) [34,72,48,130,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20805 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 52 138 273 96 69 133 261), lower := (rows 35 74 52 138 273 96 64 128 256), losses := [] }

theorem u20805 : Upper (D 6) (R 6) [34,72,48,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20806 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 52 138 276 33 69 197 325), lower := (rows 35 74 52 138 276 33 64 128 256), losses := [] }

theorem u20806 : Upper (D 6) (R 6) [34,72,48,130,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20807 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 52 138 276 36 65 193 321), lower := (rows 35 74 52 138 276 36 64 128 256), losses := [] }

theorem u20807 : Upper (D 6) (R 6) [34,72,48,130,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20808 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 52 138 276 96 69 133 261), lower := (rows 35 74 52 138 276 96 64 128 256), losses := [] }

theorem u20808 : Upper (D 6) (R 6) [34,72,48,130,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20809 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 52 138 336 33 69 133 261), lower := (rows 35 74 52 138 336 33 64 128 256), losses := [] }

theorem u20809 : Upper (D 6) (R 6) [34,72,48,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20810 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 52 138 336 36 69 133 261), lower := (rows 35 74 52 138 336 36 64 128 256), losses := [] }

theorem u20810 : Upper (D 6) (R 6) [34,72,48,130,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20811 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 52 140 81 33 326 390 262), lower := (rows 35 74 52 140 81 33 64 128 256), losses := [] }

theorem u20811 : Upper (D 6) (R 6) [34,72,48,132,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20812 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 52 140 81 34 325 389 261), lower := (rows 35 74 52 140 81 34 64 128 256), losses := [] }

theorem u20812 : Upper (D 6) (R 6) [34,72,48,132,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20813 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 52 140 81 36 323 387 259), lower := (rows 35 74 52 140 81 36 64 128 256), losses := [] }

theorem u20813 : Upper (D 6) (R 6) [34,72,48,132,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20814 : Route 9 := (fun mask => (mask,id))

def c20814 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20814 : Upper (D 6) (R 6) [34,72,48,132,65,256] 13 := by
  apply FastRouting.sound _ _ [34,72,48,132,65,256] 13 (by decide) (choices 1) [1,2,4] r20814 c20814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6121
  · exact u6122
  · exact u6123

def b20815 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 52 140 273 33 70 198 326), lower := (rows 35 74 52 140 273 33 64 128 256), losses := [] }

theorem u20815 : Upper (D 6) (R 6) [34,72,48,132,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20816 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 52 140 273 34 69 197 325), lower := (rows 35 74 52 140 273 34 64 128 256), losses := [] }

theorem u20816 : Upper (D 6) (R 6) [34,72,48,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20817 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 52 140 273 36 67 195 323), lower := (rows 35 74 52 140 273 36 64 128 256), losses := [] }

theorem u20817 : Upper (D 6) (R 6) [34,72,48,132,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20818 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 52 140 273 96 71 135 263), lower := (rows 35 74 52 140 273 96 64 128 256), losses := [] }

theorem u20818 : Upper (D 6) (R 6) [34,72,48,132,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20819 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 74 52 140 274 33 69 197 325), lower := (rows 35 74 52 140 274 33 64 128 256), losses := [] }

theorem u20819 : Upper (D 6) (R 6) [34,72,48,132,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20819
end Delivery.IrregularNine14.P06
