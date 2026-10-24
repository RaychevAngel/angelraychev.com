import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0055
import IrregularNine14P06C0056

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14760 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 52 13 400 36 67 195 323), lower := (rows 11 98 52 13 400 36 64 128 256), losses := [] }

theorem u14760 : Upper (D 6) (R 6) [10,96,48,5,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14761 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 13 400 96 71 135 263), lower := (rows 11 98 52 13 400 96 64 128 256), losses := [] }

theorem u14761 : Upper (D 6) (R 6) [10,96,48,5,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14762 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 2, region := 322, targets := 1 }], pairs := [(1,0),(2,6),(4,6)], upper := (rows 11 98 52 76 145 33 326 390 262), lower := (rows 11 98 52 76 145 33 64 128 256), losses := [] }

theorem u14762 : Upper (D 6) (R 6) [10,96,48,68,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14763 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 52 76 145 34 325 389 261), lower := (rows 11 98 52 76 145 34 64 128 256), losses := [] }

theorem u14763 : Upper (D 6) (R 6) [10,96,48,68,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14764 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 52 76 145 36 323 387 259), lower := (rows 11 98 52 76 145 36 64 128 256), losses := [] }

theorem u14764 : Upper (D 6) (R 6) [10,96,48,68,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14765 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 52 76 145 288 71 135 263), lower := (rows 11 98 52 76 145 288 64 128 256), losses := [] }

theorem u14765 : Upper (D 6) (R 6) [10,96,48,68,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14765 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14766 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 52 76 146 33 325 389 261), lower := (rows 11 98 52 76 146 33 64 128 256), losses := [] }

theorem u14766 : Upper (D 6) (R 6) [10,96,48,68,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14767 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 52 76 146 36 321 385 257), lower := (rows 11 98 52 76 146 36 64 128 256), losses := [] }

theorem u14767 : Upper (D 6) (R 6) [10,96,48,68,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14768 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 52 76 146 288 69 133 261), lower := (rows 11 98 52 76 146 288 64 128 256), losses := [] }

theorem u14768 : Upper (D 6) (R 6) [10,96,48,68,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14768 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14769 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 52 76 400 33 71 135 263), lower := (rows 11 98 52 76 400 33 64 128 256), losses := [] }

theorem u14769 : Upper (D 6) (R 6) [10,96,48,68,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14770 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 52 76 400 34 69 133 261), lower := (rows 11 98 52 76 400 34 64 128 256), losses := [] }

theorem u14770 : Upper (D 6) (R 6) [10,96,48,68,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14771 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 52 76 400 36 67 131 259), lower := (rows 11 98 52 76 400 36 64 128 256), losses := [] }

theorem u14771 : Upper (D 6) (R 6) [10,96,48,68,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14772 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 354, targets := 1 }], pairs := [(1,0),(2,6),(4,6)], upper := (rows 11 98 52 137 21 34 324 452 324), lower := (rows 11 98 52 137 21 34 64 128 256), losses := [] }

theorem u14772 : Upper (D 6) (R 6) [10,96,48,129,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14773 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 98 52 137 21 36 322 450 322), lower := (rows 11 98 52 137 21 36 64 128 256), losses := [] }

theorem u14773 : Upper (D 6) (R 6) [10,96,48,129,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14774 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 137 21 96 326 390 262), lower := (rows 11 98 52 137 21 96 64 128 256), losses := [] }

theorem u14774 : Upper (D 6) (R 6) [10,96,48,129,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14775 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 358, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 98 52 137 21 288 70 198 326), lower := (rows 11 98 52 137 21 288 64 128 256), losses := [] }

theorem u14775 : Upper (D 6) (R 6) [10,96,48,129,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14775 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14776 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 98 52 137 81 34 324 388 260), lower := (rows 11 98 52 137 81 34 64 128 256), losses := [] }

theorem u14776 : Upper (D 6) (R 6) [10,96,48,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14777 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 98 52 137 81 36 326 390 262), lower := (rows 11 98 52 137 81 36 64 128 256), losses := [] }

theorem u14777 : Upper (D 6) (R 6) [10,96,48,129,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14778 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 294, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 98 52 137 81 288 70 134 262), lower := (rows 11 98 52 137 81 288 64 128 256), losses := [] }

theorem u14778 : Upper (D 6) (R 6) [10,96,48,129,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14778 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14779 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 6, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 98 52 137 273 34 68 196 324), lower := (rows 11 98 52 137 273 34 64 128 256), losses := [] }

theorem u14779 : Upper (D 6) (R 6) [10,96,48,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14780 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 98 52 137 273 36 70 198 326), lower := (rows 11 98 52 137 273 36 64 128 256), losses := [] }

theorem u14780 : Upper (D 6) (R 6) [10,96,48,129,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14781 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 137 273 96 70 134 262), lower := (rows 11 98 52 137 273 96 64 128 256), losses := [] }

theorem u14781 : Upper (D 6) (R 6) [10,96,48,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14782 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 52 137 274 33 68 196 324), lower := (rows 11 98 52 137 274 33 64 128 256), losses := [] }

theorem u14782 : Upper (D 6) (R 6) [10,96,48,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14783 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 52 137 274 36 69 197 325), lower := (rows 11 98 52 137 274 36 64 128 256), losses := [] }

theorem u14783 : Upper (D 6) (R 6) [10,96,48,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14784 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 137 274 96 69 133 261), lower := (rows 11 98 52 137 274 96 64 128 256), losses := [] }

theorem u14784 : Upper (D 6) (R 6) [10,96,48,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14785 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 52 137 276 33 70 198 326), lower := (rows 11 98 52 137 276 33 64 128 256), losses := [] }

theorem u14785 : Upper (D 6) (R 6) [10,96,48,129,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14786 : Route 9 := (fun mask => (mask,id))

def c14786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14786 : Upper (D 6) (R 6) [10,96,48,129,260,2] 13 := by
  apply FastRouting.sound _ _ [10,96,48,129,260,2] 13 (by decide) (choices 1) [1,4] r14786 c14786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3353
  · exact u3354

def b14787 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 52 137 276 36 67 195 323), lower := (rows 11 98 52 137 276 36 64 128 256), losses := [] }

theorem u14787 : Upper (D 6) (R 6) [10,96,48,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14788 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 137 276 96 71 135 263), lower := (rows 11 98 52 137 276 96 64 128 256), losses := [] }

theorem u14788 : Upper (D 6) (R 6) [10,96,48,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14789 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 52 137 336 33 70 134 262), lower := (rows 11 98 52 137 336 33 64 128 256), losses := [] }

theorem u14789 : Upper (D 6) (R 6) [10,96,48,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14790 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 98 52 137 336 34 69 133 261), lower := (rows 11 98 52 137 336 34 64 128 256), losses := [] }

theorem u14790 : Upper (D 6) (R 6) [10,96,48,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14791 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 98 52 137 336 36 71 135 263), lower := (rows 11 98 52 137 336 36 64 128 256), losses := [] }

theorem u14791 : Upper (D 6) (R 6) [10,96,48,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14792 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 458, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 11 98 52 140 81 33 326 390 262), lower := (rows 11 98 52 140 81 33 64 128 256), losses := [] }

theorem u14792 : Upper (D 6) (R 6) [10,96,48,132,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14793 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 98 52 140 81 34 325 389 261), lower := (rows 11 98 52 140 81 34 64 128 256), losses := [] }

theorem u14793 : Upper (D 6) (R 6) [10,96,48,132,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14794 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 38, targets := 1 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 11 98 52 140 81 36 323 387 259), lower := (rows 11 98 52 140 81 36 64 128 256), losses := [] }

theorem u14794 : Upper (D 6) (R 6) [10,96,48,132,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14795 : Route 9 := (fun mask => (mask,id))

def c14795 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14795 : Upper (D 6) (R 6) [10,96,48,132,65,256] 13 := by
  apply FastRouting.sound _ _ [10,96,48,132,65,256] 13 (by decide) (choices 1) [1,2,4] r14795 c14795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3355
  · exact u3356
  · exact u3357

def b14796 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 202, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 11 98 52 140 273 33 70 198 326), lower := (rows 11 98 52 140 273 33 64 128 256), losses := [] }

theorem u14796 : Upper (D 6) (R 6) [10,96,48,132,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14797 : PairBound 9 := { available := 69, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 98 52 140 273 34 69 197 325), lower := (rows 11 98 52 140 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 66 20 8 16 99 64 128 256), good := (rows 42 98 52 140 308 34 98 128 256) }] }

theorem u14797 : Upper (D 6) (R 6) [10,96,48,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14798 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 52 140 273 36 67 195 323), lower := (rows 11 98 52 140 273 36 64 128 256), losses := [] }

theorem u14798 : Upper (D 6) (R 6) [10,96,48,132,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14799 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 140 273 96 71 135 263), lower := (rows 11 98 52 140 273 96 64 128 256), losses := [] }

theorem u14799 : Upper (D 6) (R 6) [10,96,48,132,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14800 : Route 9 := (fun mask => (mask,id))

def c14800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14800 : Upper (D 6) (R 6) [10,96,48,132,258,1] 13 := by
  apply FastRouting.sound _ _ [10,96,48,132,258,1] 13 (by decide) (choices 1) [1,4] r14800 c14800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3358
  · exact u3359

def b14801 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 52 140 274 36 65 193 321), lower := (rows 11 98 52 140 274 36 64 128 256), losses := [] }

theorem u14801 : Upper (D 6) (R 6) [10,96,48,132,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14802 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 140 274 96 69 133 261), lower := (rows 11 98 52 140 274 96 64 128 256), losses := [] }

theorem u14802 : Upper (D 6) (R 6) [10,96,48,132,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14803 : Route 9 := (fun mask => (mask,id))

def c14803 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14803 : Upper (D 6) (R 6) [10,96,48,132,260,1] 13 := by
  apply FastRouting.sound _ _ [10,96,48,132,260,1] 13 (by decide) (choices 1) [1,2] r14803 c14803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3360
  · exact u3361

def b14804 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 98 52 140 276 34 65 193 321), lower := (rows 11 98 52 140 276 34 64 128 256), losses := [] }

theorem u14804 : Upper (D 6) (R 6) [10,96,48,132,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14805 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 140 276 96 67 131 259), lower := (rows 11 98 52 140 276 96 64 128 256), losses := [] }

theorem u14805 : Upper (D 6) (R 6) [10,96,48,132,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14806 : Route 9 := (fun mask => (mask,id))

def c14806 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14806 : Upper (D 6) (R 6) [10,96,48,132,320,1] 13 := by
  apply FastRouting.sound _ _ [10,96,48,132,320,1] 13 (by decide) (choices 1) [1,2,4] r14806 c14806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3362
  · exact u3363
  · exact u3364

def b14807 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 98 52 140 336 34 69 133 261), lower := (rows 11 98 52 140 336 34 64 128 256), losses := [] }

theorem u14807 : Upper (D 6) (R 6) [10,96,48,132,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14808 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 38, targets := 1 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 11 98 52 140 336 36 67 131 259), lower := (rows 11 98 52 140 336 36 64 128 256), losses := [] }

theorem u14808 : Upper (D 6) (R 6) [10,96,48,132,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14809 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 20, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 98 52 200 21 33 326 390 262), lower := (rows 11 98 52 200 21 33 64 128 256), losses := [] }

theorem u14809 : Upper (D 6) (R 6) [10,96,48,192,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14810 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 52 200 21 34 325 389 261), lower := (rows 11 98 52 200 21 34 64 128 256), losses := [] }

theorem u14810 : Upper (D 6) (R 6) [10,96,48,192,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14811 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 393, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 52 200 21 36 323 387 259), lower := (rows 11 98 52 200 21 36 64 128 256), losses := [] }

theorem u14811 : Upper (D 6) (R 6) [10,96,48,192,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14812 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 52 200 21 288 71 135 263), lower := (rows 11 98 52 200 21 288 64 128 256), losses := [] }

theorem u14812 : Upper (D 6) (R 6) [10,96,48,192,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14812 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14813 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 308, targets := 64 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(2,6),(4,6)], upper := (rows 11 98 52 200 273 33 70 134 262), lower := (rows 11 98 52 200 273 33 64 128 256), losses := [] }

theorem u14813 : Upper (D 6) (R 6) [10,96,48,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14814 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 308, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 52 200 273 34 69 133 261), lower := (rows 11 98 52 200 273 34 64 128 256), losses := [] }

theorem u14814 : Upper (D 6) (R 6) [10,96,48,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14815 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 52 200 273 36 71 135 263), lower := (rows 11 98 52 200 273 36 64 128 256), losses := [] }

theorem u14815 : Upper (D 6) (R 6) [10,96,48,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14816 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 308, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 52 200 274 33 69 133 261), lower := (rows 11 98 52 200 274 33 64 128 256), losses := [] }

theorem u14816 : Upper (D 6) (R 6) [10,96,48,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14817 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 98 52 200 274 36 69 133 261), lower := (rows 11 98 52 200 274 36 64 128 256), losses := [] }

theorem u14817 : Upper (D 6) (R 6) [10,96,48,192,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14818 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 308, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 52 200 276 33 71 135 263), lower := (rows 11 98 52 200 276 33 64 128 256), losses := [] }

theorem u14818 : Upper (D 6) (R 6) [10,96,48,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14819 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 308, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 98 52 200 276 34 69 133 261), lower := (rows 11 98 52 200 276 34 64 128 256), losses := [] }

theorem u14819 : Upper (D 6) (R 6) [10,96,48,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u14819
end Delivery.IrregularNine14.P06
