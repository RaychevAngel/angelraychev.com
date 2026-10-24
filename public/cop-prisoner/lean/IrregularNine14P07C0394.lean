import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0126

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23640 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 2, region := 417, targets := 2 }], pairs := [(0,1),(0,6),(4,6)], upper := (rows 37 98 14 88 146 288 193 129 385), lower := (rows 37 98 14 88 146 288 64 128 256), losses := [] }

theorem u23640 : Upper (D 7) (R 7) [36,96,10,80,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23640 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23641 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 98 14 88 273 33 194 130 386), lower := (rows 37 98 14 88 273 33 64 128 256), losses := [] }

theorem u23641 : Upper (D 7) (R 7) [36,96,10,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23642 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 88 273 34 193 129 385), lower := (rows 37 98 14 88 273 34 64 128 256), losses := [] }

theorem u23642 : Upper (D 7) (R 7) [36,96,10,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23643 : Route 9 := (fun mask => (mask,id))

def c23643 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23643 : Upper (D 7) (R 7) [36,96,10,80,257,128] 13 := by
  apply FastRouting.sound _ _ [36,96,10,80,257,128] 13 (by decide) (choices 1) [1,2,128] r23643 c23643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7583
  · exact u7584
  · exact u7585

def b23644 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 98 14 88 274 33 193 129 385), lower := (rows 37 98 14 88 274 33 64 128 256), losses := [] }

theorem u23644 : Upper (D 7) (R 7) [36,96,10,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23645 : Route 9 := (fun mask => (mask,id))

def c23645 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23645 : Upper (D 7) (R 7) [36,96,10,80,258,128] 13 := by
  apply FastRouting.sound _ _ [36,96,10,80,258,128] 13 (by decide) (choices 1) [1,128] r23645 c23645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7586
  · exact u7587

def b23646 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 98 14 88 400 33 195 131 387), lower := (rows 37 98 14 88 400 33 64 128 256), losses := [] }

theorem u23646 : Upper (D 7) (R 7) [36,96,10,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23647 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 88 400 34 193 129 385), lower := (rows 37 98 14 88 400 34 64 128 256), losses := [] }

theorem u23647 : Upper (D 7) (R 7) [36,96,10,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23648 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 66, targets := 128 }], pairs := [(0,6),(1,0),(1,7),(4,6)], upper := (rows 37 98 14 88 400 160 67 131 259), lower := (rows 37 98 14 88 400 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 176 64 128 256), good := (rows 36 98 14 126 432 160 64 160 256) }] }

theorem u23648 : Upper (D 7) (R 7) [36,96,10,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23649 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 137 81 34 464 400 400), lower := (rows 37 98 14 137 81 34 64 128 256), losses := [] }

theorem u23649 : Upper (D 7) (R 7) [36,96,10,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23650 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 14 137 81 48 450 386 386), lower := (rows 37 98 14 137 81 48 64 128 256), losses := [] }

theorem u23650 : Upper (D 7) (R 7) [36,96,10,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23650 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23651 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 418, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(4,7)], upper := (rows 37 98 14 137 81 160 338 402 274), lower := (rows 37 98 14 137 81 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 45 169 81 160 64 160 256) }] }

theorem u23651 : Upper (D 7) (R 7) [36,96,10,129,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23652 : Route 9 := (fun mask => (mask,id))

def c23652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23652 : Upper (D 7) (R 7) [36,96,10,129,65,256] 13 := by
  apply FastRouting.sound _ _ [36,96,10,129,65,256] 13 (by decide) (choices 1) [2,16,128] r23652 c23652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7588
  · exact u7589
  · exact u7590

def b23653 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 14 137 146 33 336 464 336), lower := (rows 37 98 14 137 146 33 64 128 256), losses := [] }

theorem u23653 : Upper (D 7) (R 7) [36,96,10,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23654 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 14 137 146 48 321 449 321), lower := (rows 37 98 14 137 146 48 64 128 256), losses := [] }

theorem u23654 : Upper (D 7) (R 7) [36,96,10,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23654 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23655 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 137 146 96 337 401 273), lower := (rows 37 98 14 137 146 96 64 128 256), losses := [] }

theorem u23655 : Upper (D 7) (R 7) [36,96,10,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23656 : Route 9 := (fun mask => (mask,id))

def c23656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23656 : Upper (D 7) (R 7) [36,96,10,129,130,256] 13 := by
  apply FastRouting.sound _ _ [36,96,10,129,130,256] 13 (by decide) (choices 1) [1,16] r23656 c23656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7591
  · exact u7592

def b23657 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 14 137 208 33 338 402 274), lower := (rows 37 98 14 137 208 33 64 128 256), losses := [] }

theorem u23657 : Upper (D 7) (R 7) [36,96,10,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23658 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 137 208 34 337 401 273), lower := (rows 37 98 14 137 208 34 64 128 256), losses := [] }

theorem u23658 : Upper (D 7) (R 7) [36,96,10,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23659 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 14 137 208 48 323 387 259), lower := (rows 37 98 14 137 208 48 64 128 256), losses := [] }

theorem u23659 : Upper (D 7) (R 7) [36,96,10,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23659 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23660 : Route 9 := (fun mask => (mask,id))

def c23660 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23660 : Upper (D 7) (R 7) [36,96,10,129,192,256] 13 := by
  apply FastRouting.sound _ _ [36,96,10,129,192,256] 13 (by decide) (choices 1) [1,2,16] r23660 c23660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7593
  · exact u7594
  · exact u7595

def b23661 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 137 273 34 208 208 464), lower := (rows 37 98 14 137 273 34 64 128 256), losses := [] }

theorem u23661 : Upper (D 7) (R 7) [36,96,10,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23662 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 194, targets := 1 }], pairs := [(1,0),(2,0),(3,5)], upper := (rows 37 98 14 137 273 48 194 194 450), lower := (rows 37 98 14 137 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 51 12 8 16 48 127 191 319), good := (rows 486 482 462 462 498 498 64 128 256) },{ target := 5, region := (rows 1 2 4 9 17 0 70 134 262), good := (rows 477 450 462 153 281 16 64 128 256) }] }

theorem u23662 : Upper (D 7) (R 7) [36,96,10,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23662 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23663 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 137 273 96 210 146 402), lower := (rows 37 98 14 137 273 96 64 128 256), losses := [] }

theorem u23663 : Upper (D 7) (R 7) [36,96,10,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23664 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(4,7)], upper := (rows 37 98 14 137 273 160 82 210 338), lower := (rows 37 98 14 137 273 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 45 169 273 160 64 160 256) }] }

theorem u23664 : Upper (D 7) (R 7) [36,96,10,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23665 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 14 137 274 33 208 208 464), lower := (rows 37 98 14 137 274 33 64 128 256), losses := [] }

theorem u23665 : Upper (D 7) (R 7) [36,96,10,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23666 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 34 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 37 98 14 137 274 48 193 193 449), lower := (rows 37 98 14 137 274 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 20 0 73 137 265), good := (rows 477 66 478 457 274 16 64 128 256) }] }

theorem u23666 : Upper (D 7) (R 7) [36,96,10,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23666 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23667 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 137 274 96 209 145 401), lower := (rows 37 98 14 137 274 96 64 128 256), losses := [] }

theorem u23667 : Upper (D 7) (R 7) [36,96,10,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23668 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 98 14 137 274 160 81 209 337), lower := (rows 37 98 14 137 274 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 45 169 272 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 34 47 169 274 160 0 160 256) }] }

theorem u23668 : Upper (D 7) (R 7) [36,96,10,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23669 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 14 137 336 33 210 146 402), lower := (rows 37 98 14 137 336 33 64 128 256), losses := [] }

theorem u23669 : Upper (D 7) (R 7) [36,96,10,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23670 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 137 336 34 209 145 401), lower := (rows 37 98 14 137 336 34 64 128 256), losses := [] }

theorem u23670 : Upper (D 7) (R 7) [36,96,10,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23671 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 14 137 336 48 195 131 387), lower := (rows 37 98 14 137 336 48 64 128 256), losses := [] }

theorem u23671 : Upper (D 7) (R 7) [36,96,10,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23671 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23672 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 98 14 137 336 160 83 147 275), lower := (rows 37 98 14 137 336 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 45 169 336 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 34 47 169 272 160 0 160 256) }] }

theorem u23672 : Upper (D 7) (R 7) [36,96,10,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23673 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 14 137 400 33 82 210 338), lower := (rows 37 98 14 137 400 33 64 128 256), losses := [] }

theorem u23673 : Upper (D 7) (R 7) [36,96,10,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23674 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 137 400 34 81 209 337), lower := (rows 37 98 14 137 400 34 64 128 256), losses := [] }

theorem u23674 : Upper (D 7) (R 7) [36,96,10,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23675 : Route 9 := (fun mask => (mask,id))

def c23675 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23675 : Upper (D 7) (R 7) [36,96,10,129,384,16] 13 := by
  apply FastRouting.sound _ _ [36,96,10,129,384,16] 13 (by decide) (choices 1) [1,2] r23675 c23675
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7596
  · exact u7597

def b23676 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 137 400 96 83 147 275), lower := (rows 37 98 14 137 400 96 64 128 256), losses := [] }

theorem u23676 : Upper (D 7) (R 7) [36,96,10,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23677 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 0, region := 450, targets := 1 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 14 152 81 33 450 386 386), lower := (rows 37 98 14 152 81 33 64 128 256), losses := [] }

theorem u23677 : Upper (D 7) (R 7) [36,96,10,144,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23678 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 152 81 34 449 385 385), lower := (rows 37 98 14 152 81 34 64 128 256), losses := [] }

theorem u23678 : Upper (D 7) (R 7) [36,96,10,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23679 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 417, targets := 64 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 98 14 152 81 160 323 387 259), lower := (rows 37 98 14 152 81 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 45 184 81 160 64 160 256) }] }

theorem u23679 : Upper (D 7) (R 7) [36,96,10,144,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23680 : Route 9 := (fun mask => (mask,id))

def c23680 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23680 : Upper (D 7) (R 7) [36,96,10,144,65,256] 13 := by
  apply FastRouting.sound _ _ [36,96,10,144,65,256] 13 (by decide) (choices 1) [1,2,128] r23680 c23680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7598
  · exact u7599
  · exact u7600

def b23681 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 14 152 273 33 194 194 450), lower := (rows 37 98 14 152 273 33 64 128 256), losses := [] }

theorem u23681 : Upper (D 7) (R 7) [36,96,10,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23682 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 152 273 34 193 193 449), lower := (rows 37 98 14 152 273 34 64 128 256), losses := [] }

theorem u23682 : Upper (D 7) (R 7) [36,96,10,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23683 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 152 273 96 195 131 387), lower := (rows 37 98 14 152 273 96 64 128 256), losses := [] }

theorem u23683 : Upper (D 7) (R 7) [36,96,10,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23684 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 98 14 152 273 160 67 195 323), lower := (rows 37 98 14 152 273 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 45 184 273 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 34 47 184 273 160 0 160 256) }] }

theorem u23684 : Upper (D 7) (R 7) [36,96,10,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23685 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 98 14 152 274 33 193 193 449), lower := (rows 37 98 14 152 274 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 22 10 18 0 97 161 289), good := (rows 453 478 30 156 286 449 64 128 256) }] }

theorem u23685 : Upper (D 7) (R 7) [36,96,10,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23686 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 152 274 96 193 129 385), lower := (rows 37 98 14 152 274 96 64 128 256), losses := [] }

theorem u23686 : Upper (D 7) (R 7) [36,96,10,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23687 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 98 14 152 274 160 65 193 321), lower := (rows 37 98 14 152 274 160 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 34 47 184 274 160 0 160 256) }] }

theorem u23687 : Upper (D 7) (R 7) [36,96,10,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23688 : Route 9 := (fun mask => (mask,id))

def c23688 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23688 : Upper (D 7) (R 7) [36,96,10,144,320,1] 13 := by
  apply FastRouting.sound _ _ [36,96,10,144,320,1] 13 (by decide) (choices 1) [1,2,128] r23688 c23688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7601
  · exact u7602
  · exact u7603

def b23689 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 152 336 34 193 129 385), lower := (rows 37 98 14 152 336 34 64 128 256), losses := [] }

theorem u23689 : Upper (D 7) (R 7) [36,96,10,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23690 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 98 14 152 336 160 67 131 259), lower := (rows 37 98 14 152 336 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 45 184 336 160 64 160 256) }] }

theorem u23690 : Upper (D 7) (R 7) [36,96,10,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23691 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 98 14 200 145 33 338 402 274), lower := (rows 37 98 14 200 145 33 64 128 256), losses := [] }

theorem u23691 : Upper (D 7) (R 7) [36,96,10,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23692 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 200 145 34 337 401 273), lower := (rows 37 98 14 200 145 34 64 128 256), losses := [] }

theorem u23692 : Upper (D 7) (R 7) [36,96,10,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23693 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,6),(1,7),(4,6)], upper := (rows 37 98 14 200 145 48 323 387 259), lower := (rows 37 98 14 200 145 48 64 128 256), losses := [] }

theorem u23693 : Upper (D 7) (R 7) [36,96,10,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23693 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23694 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 4, region := 354, targets := 128 }], pairs := [(0,6),(1,7),(4,6)], upper := (rows 37 98 14 200 145 288 83 147 275), lower := (rows 37 98 14 200 145 288 64 128 256), losses := [] }

theorem u23694 : Upper (D 7) (R 7) [36,96,10,192,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23694 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23695 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 98 14 200 146 33 337 401 273), lower := (rows 37 98 14 200 146 33 64 128 256), losses := [] }

theorem u23695 : Upper (D 7) (R 7) [36,96,10,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23696 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 54, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 98 14 200 146 48 321 385 257), lower := (rows 37 98 14 200 146 48 64 128 256), losses := [] }

theorem u23696 : Upper (D 7) (R 7) [36,96,10,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23696 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23697 : Route 9 := (fun mask => (mask,id))

def c23697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23697 : Upper (D 7) (R 7) [36,96,10,192,130,256] 13 := by
  apply FastRouting.sound _ _ [36,96,10,192,130,256] 13 (by decide) (choices 1) [1,16] r23697 c23697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7604
  · exact u7605

def b23698 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 98 14 200 273 33 210 146 402), lower := (rows 37 98 14 200 273 33 64 128 256), losses := [] }

theorem u23698 : Upper (D 7) (R 7) [36,96,10,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23699 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 200 273 34 209 145 401), lower := (rows 37 98 14 200 273 34 64 128 256), losses := [] }

theorem u23699 : Upper (D 7) (R 7) [36,96,10,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u23699
end Delivery.IrregularNine14.P07
