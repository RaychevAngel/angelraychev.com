import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0055

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14700 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 140 276 96 83 147 275), lower := (rows 11 98 37 140 276 96 64 128 256), losses := [] }

theorem u14700 : Upper (D 6) (R 6) [10,96,33,132,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14701 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 140 336 33 86 150 278), lower := (rows 11 98 37 140 336 33 64 128 256), losses := [] }

theorem u14701 : Upper (D 6) (R 6) [10,96,33,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14702 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 140 336 34 85 149 277), lower := (rows 11 98 37 140 336 34 64 128 256), losses := [] }

theorem u14702 : Upper (D 6) (R 6) [10,96,33,132,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14702 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14703 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 98 37 140 336 36 83 147 275), lower := (rows 11 98 37 140 336 36 64 128 256), losses := [] }

theorem u14703 : Upper (D 6) (R 6) [10,96,33,132,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14704 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 37 140 336 48 71 135 263), lower := (rows 11 98 37 140 336 48 64 128 256), losses := [] }

theorem u14704 : Upper (D 6) (R 6) [10,96,33,132,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14704 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14705 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 152 84 33 326 390 262), lower := (rows 11 98 37 152 84 33 64 128 256), losses := [] }

theorem u14705 : Upper (D 6) (R 6) [10,96,33,144,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14706 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 152 84 34 325 389 261), lower := (rows 11 98 37 152 84 34 64 128 256), losses := [] }

theorem u14706 : Upper (D 6) (R 6) [10,96,33,144,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14707 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 36, targets := 2 },{ cop := 0, region := 36, targets := 64 },{ cop := 2, region := 322, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 98 37 152 84 36 323 387 259), lower := (rows 11 98 37 152 84 36 64 128 256), losses := [] }

theorem u14707 : Upper (D 6) (R 6) [10,96,33,144,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14707 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14708 : Route 9 := (fun mask => (mask,id))

def c14708 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14708 : Upper (D 6) (R 6) [10,96,33,144,68,256] 13 := by
  apply FastRouting.sound _ _ [10,96,33,144,68,256] 13 (by decide) (choices 1) [1,2,4] r14708 c14708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3337
  · exact u3338
  · exact u3339

def b14709 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 152 273 34 68 196 324), lower := (rows 11 98 37 152 273 34 64 128 256), losses := [] }

theorem u14709 : Upper (D 6) (R 6) [10,96,33,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14710 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 98 37 152 273 36 70 198 326), lower := (rows 11 98 37 152 273 36 64 128 256), losses := [] }

theorem u14710 : Upper (D 6) (R 6) [10,96,33,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14711 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 152 273 96 70 134 262), lower := (rows 11 98 37 152 273 96 64 128 256), losses := [] }

theorem u14711 : Upper (D 6) (R 6) [10,96,33,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14712 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 152 274 33 68 196 324), lower := (rows 11 98 37 152 274 33 64 128 256), losses := [] }

theorem u14712 : Upper (D 6) (R 6) [10,96,33,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14712 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14713 : Route 9 := (fun mask => (mask,id))

def c14713 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14713 : Upper (D 6) (R 6) [10,96,33,144,258,4] 13 := by
  apply FastRouting.sound _ _ [10,96,33,144,258,4] 13 (by decide) (choices 1) [1,4] r14713 c14713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3340
  · exact u3341

def b14714 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 152 274 96 69 133 261), lower := (rows 11 98 37 152 274 96 64 128 256), losses := [] }

theorem u14714 : Upper (D 6) (R 6) [10,96,33,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14715 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 152 276 33 70 198 326), lower := (rows 11 98 37 152 276 33 64 128 256), losses := [] }

theorem u14715 : Upper (D 6) (R 6) [10,96,33,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14715 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14716 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 152 276 34 69 197 325), lower := (rows 11 98 37 152 276 34 64 128 256), losses := [] }

theorem u14716 : Upper (D 6) (R 6) [10,96,33,144,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14716 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14717 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 66, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 98 37 152 276 36 67 195 323), lower := (rows 11 98 37 152 276 36 64 128 256), losses := [] }

theorem u14717 : Upper (D 6) (R 6) [10,96,33,144,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14718 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 152 276 96 71 135 263), lower := (rows 11 98 37 152 276 96 64 128 256), losses := [] }

theorem u14718 : Upper (D 6) (R 6) [10,96,33,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14719 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 152 336 33 70 134 262), lower := (rows 11 98 37 152 336 33 64 128 256), losses := [] }

theorem u14719 : Upper (D 6) (R 6) [10,96,33,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14719 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14720 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 152 336 34 69 133 261), lower := (rows 11 98 37 152 336 34 64 128 256), losses := [] }

theorem u14720 : Upper (D 6) (R 6) [10,96,33,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14721 : Route 9 := (fun mask => (mask,id))

def c14721 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14721 : Upper (D 6) (R 6) [10,96,33,144,320,4] 13 := by
  apply FastRouting.sound _ _ [10,96,33,144,320,4] 13 (by decide) (choices 1) [1,2,4] r14721 c14721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3342
  · exact u3343
  · exact u3344

def b14722 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 200 273 34 84 148 276), lower := (rows 11 98 37 200 273 34 64 128 256), losses := [] }

theorem u14722 : Upper (D 6) (R 6) [10,96,33,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14722 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14723 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 308, targets := 64 },{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 11 98 37 200 273 36 86 150 278), lower := (rows 11 98 37 200 273 36 64 128 256), losses := [] }

theorem u14723 : Upper (D 6) (R 6) [10,96,33,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14724 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 37 200 273 48 70 134 262), lower := (rows 11 98 37 200 273 48 64 128 256), losses := [] }

theorem u14724 : Upper (D 6) (R 6) [10,96,33,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14724 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14725 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 200 274 33 84 148 276), lower := (rows 11 98 37 200 274 33 64 128 256), losses := [] }

theorem u14725 : Upper (D 6) (R 6) [10,96,33,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14725 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14726 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 308, targets := 64 },{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 11 98 37 200 274 36 85 149 277), lower := (rows 11 98 37 200 274 36 64 128 256), losses := [] }

theorem u14726 : Upper (D 6) (R 6) [10,96,33,192,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14727 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 37 200 274 48 69 133 261), lower := (rows 11 98 37 200 274 48 64 128 256), losses := [] }

theorem u14727 : Upper (D 6) (R 6) [10,96,33,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14727 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14728 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 200 276 33 86 150 278), lower := (rows 11 98 37 200 276 33 64 128 256), losses := [] }

theorem u14728 : Upper (D 6) (R 6) [10,96,33,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14729 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 200 276 34 85 149 277), lower := (rows 11 98 37 200 276 34 64 128 256), losses := [] }

theorem u14729 : Upper (D 6) (R 6) [10,96,33,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14730 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 308, targets := 64 },{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 11 98 37 200 276 36 83 147 275), lower := (rows 11 98 37 200 276 36 64 128 256), losses := [] }

theorem u14730 : Upper (D 6) (R 6) [10,96,33,192,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14731 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 37 200 276 48 71 135 263), lower := (rows 11 98 37 200 276 48 64 128 256), losses := [] }

theorem u14731 : Upper (D 6) (R 6) [10,96,33,192,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14731 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14732 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 392 22 33 84 212 340), lower := (rows 11 98 37 392 22 33 64 128 256), losses := [] }

theorem u14732 : Upper (D 6) (R 6) [10,96,33,384,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14733 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 37 392 22 36 81 209 337), lower := (rows 11 98 37 392 22 36 64 128 256), losses := [] }

theorem u14733 : Upper (D 6) (R 6) [10,96,33,384,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14734 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 52, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 98 37 392 22 48 69 197 325), lower := (rows 11 98 37 392 22 48 64 128 256), losses := [] }

theorem u14734 : Upper (D 6) (R 6) [10,96,33,384,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14734 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14735 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 392 22 96 85 149 277), lower := (rows 11 98 37 392 22 96 64 128 256), losses := [] }

theorem u14735 : Upper (D 6) (R 6) [10,96,33,384,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14736 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 392 81 34 84 148 276), lower := (rows 11 98 37 392 81 34 64 128 256), losses := [] }

theorem u14736 : Upper (D 6) (R 6) [10,96,33,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14736 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14737 : Route 9 := (fun mask => (mask,id))

def c14737 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14737 : Upper (D 6) (R 6) [10,96,33,384,65,4] 13 := by
  apply FastRouting.sound _ _ [10,96,33,384,65,4] 13 (by decide) (choices 1) [2,4,16] r14737 c14737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3345
  · exact u3346
  · exact u3347

def b14738 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 37 392 81 48 70 134 262), lower := (rows 11 98 37 392 81 48 64 128 256), losses := [] }

theorem u14738 : Upper (D 6) (R 6) [10,96,33,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14738 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14739 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 392 84 33 86 150 278), lower := (rows 11 98 37 392 84 33 64 128 256), losses := [] }

theorem u14739 : Upper (D 6) (R 6) [10,96,33,384,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14740 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 392 84 34 85 149 277), lower := (rows 11 98 37 392 84 34 64 128 256), losses := [] }

theorem u14740 : Upper (D 6) (R 6) [10,96,33,384,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14741 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 98 37 392 84 36 83 147 275), lower := (rows 11 98 37 392 84 36 64 128 256), losses := [] }

theorem u14741 : Upper (D 6) (R 6) [10,96,33,384,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14742 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 37 392 84 48 71 135 263), lower := (rows 11 98 37 392 84 48 64 128 256), losses := [] }

theorem u14742 : Upper (D 6) (R 6) [10,96,33,384,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14742 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14743 : PairBound 9 := { available := 388, camps := [{ cop := 3, region := 464, targets := 34 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 98 52 13 81 34 452 388 388), lower := (rows 11 98 52 13 81 34 64 128 256), losses := [] }

theorem u14743 : Upper (D 6) (R 6) [10,96,48,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14744 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 98 52 13 81 36 450 386 386), lower := (rows 11 98 52 13 81 36 64 128 256), losses := [] }

theorem u14744 : Upper (D 6) (R 6) [10,96,48,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14745 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 98 52 13 81 160 326 390 262), lower := (rows 11 98 52 13 81 160 64 128 256), losses := [] }

theorem u14745 : Upper (D 6) (R 6) [10,96,48,5,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14745 [(5,7)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14746 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 464, targets := 34 },{ cop := 4, region := 358, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 98 52 13 145 34 324 452 324), lower := (rows 11 98 52 13 145 34 64 128 256), losses := [] }

theorem u14746 : Upper (D 6) (R 6) [10,96,48,5,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14747 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 98 52 13 145 36 322 450 322), lower := (rows 11 98 52 13 145 36 64 128 256), losses := [] }

theorem u14747 : Upper (D 6) (R 6) [10,96,48,5,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14748 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 13 145 96 326 390 262), lower := (rows 11 98 52 13 145 96 64 128 256), losses := [] }

theorem u14748 : Upper (D 6) (R 6) [10,96,48,5,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14749 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 358, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 98 52 13 145 288 70 198 326), lower := (rows 11 98 52 13 145 288 64 128 256), losses := [] }

theorem u14749 : Upper (D 6) (R 6) [10,96,48,5,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14749 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14750 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 13 146 33 324 452 324), lower := (rows 11 98 52 13 146 33 64 128 256), losses := [] }

theorem u14750 : Upper (D 6) (R 6) [10,96,48,5,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14751 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 13 146 36 321 449 321), lower := (rows 11 98 52 13 146 36 64 128 256), losses := [] }

theorem u14751 : Upper (D 6) (R 6) [10,96,48,5,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14752 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 52 13 146 96 325 389 261), lower := (rows 11 98 52 13 146 96 64 128 256), losses := [] }

theorem u14752 : Upper (D 6) (R 6) [10,96,48,5,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14753 : Route 9 := (fun mask => (mask,id))

def c14753 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14753 : Upper (D 6) (R 6) [10,96,48,5,130,256] 13 := by
  apply FastRouting.sound _ _ [10,96,48,5,130,256] 13 (by decide) (choices 1) [1,4] r14753 c14753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3348
  · exact u3349

def b14754 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 52 13 208 33 326 390 262), lower := (rows 11 98 52 13 208 33 64 128 256), losses := [] }

theorem u14754 : Upper (D 6) (R 6) [10,96,48,5,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14755 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 464, targets := 34 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 98 52 13 208 34 325 389 261), lower := (rows 11 98 52 13 208 34 64 128 256), losses := [] }

theorem u14755 : Upper (D 6) (R 6) [10,96,48,5,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14756 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 4, region := 38, targets := 1 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 11 98 52 13 208 36 323 387 259), lower := (rows 11 98 52 13 208 36 64 128 256), losses := [] }

theorem u14756 : Upper (D 6) (R 6) [10,96,48,5,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14757 : Route 9 := (fun mask => (mask,id))

def c14757 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14757 : Upper (D 6) (R 6) [10,96,48,5,192,256] 13 := by
  apply FastRouting.sound _ _ [10,96,48,5,192,256] 13 (by decide) (choices 1) [1,2,4] r14757 c14757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3350
  · exact u3351
  · exact u3352

def b14758 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 52 13 400 33 70 198 326), lower := (rows 11 98 52 13 400 33 64 128 256), losses := [] }

theorem u14758 : Upper (D 6) (R 6) [10,96,48,5,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14759 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 464, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 98 52 13 400 34 69 197 325), lower := (rows 11 98 52 13 400 34 64 128 256), losses := [] }

theorem u14759 : Upper (D 6) (R 6) [10,96,48,5,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u14759
end Delivery.IrregularNine14.P06
