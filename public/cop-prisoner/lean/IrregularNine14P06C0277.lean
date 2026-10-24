import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0071

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16620 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 292 104 81 48 71 135 263), lower := (rows 11 134 292 104 81 48 64 128 256), losses := [] }

theorem u16620 : Upper (D 6) (R 6) [10,132,288,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16620 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16621 : Route 9 := (fun mask => (mask,id))

def c16621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16621 : Upper (D 6) (R 6) [10,132,288,96,66,1] 13 := by
  apply FastRouting.sound _ _ [10,132,288,96,66,1] 13 (by decide) (choices 1) [1,4,16] r16621 c16621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4264
  · exact u4265
  · exact u4266

def b16622 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 292 104 82 36 81 145 273), lower := (rows 11 134 292 104 82 36 64 128 256), losses := [] }

theorem u16622 : Upper (D 6) (R 6) [10,132,288,96,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16623 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 292 104 82 48 69 133 261), lower := (rows 11 134 292 104 82 48 64 128 256), losses := [] }

theorem u16623 : Upper (D 6) (R 6) [10,132,288,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16623 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16624 : Route 9 := (fun mask => (mask,id))

def c16624 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16624 : Upper (D 6) (R 6) [10,132,288,96,68,1] 13 := by
  apply FastRouting.sound _ _ [10,132,288,96,68,1] 13 (by decide) (choices 1) [1,2,16] r16624 c16624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4267
  · exact u4268
  · exact u4269

def r16625 : Route 9 := (fun mask => (mask,id))

def c16625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16625 : Upper (D 6) (R 6) [10,132,288,96,68,2] 13 := by
  apply FastRouting.sound _ _ [10,132,288,96,68,2] 13 (by decide) (choices 1) [1,16] r16625 c16625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4270
  · exact u4271

def b16626 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 292 104 84 48 67 131 259), lower := (rows 11 134 292 104 84 48 64 128 256), losses := [] }

theorem u16626 : Upper (D 6) (R 6) [10,132,288,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16626 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16627 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 72, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 146 37 73 276 34 100 228 356), lower := (rows 11 146 37 73 276 34 64 128 256), losses := [] }

theorem u16627 : Upper (D 6) (R 6) [10,144,33,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16628 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 146 37 73 276 36 98 226 354), lower := (rows 11 146 37 73 276 36 64 128 256), losses := [] }

theorem u16628 : Upper (D 6) (R 6) [10,144,33,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16629 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 402, targets := 1 },{ cop := 2, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 146 37 73 276 96 102 166 294), lower := (rows 11 146 37 73 276 96 64 128 256), losses := [] }

theorem u16629 : Upper (D 6) (R 6) [10,144,33,65,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16630 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 72, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 146 37 73 304 34 68 196 324), lower := (rows 11 146 37 73 304 34 64 128 256), losses := [] }

theorem u16630 : Upper (D 6) (R 6) [10,144,33,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16631 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 146 37 73 304 36 70 198 326), lower := (rows 11 146 37 73 304 36 64 128 256), losses := [] }

theorem u16631 : Upper (D 6) (R 6) [10,144,33,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16632 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 402, targets := 1 },{ cop := 2, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 146 37 73 304 96 70 134 262), lower := (rows 11 146 37 73 304 96 64 128 256), losses := [] }

theorem u16632 : Upper (D 6) (R 6) [10,144,33,65,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16633 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(3,1),(4,1)], upper := (rows 11 146 37 76 81 34 356 420 292), lower := (rows 11 146 37 76 81 34 64 128 256), losses := [] }

theorem u16633 : Upper (D 6) (R 6) [10,144,33,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16634 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 466, targets := 4 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 11 146 37 76 81 36 354 418 290), lower := (rows 11 146 37 76 81 36 64 128 256), losses := [] }

theorem u16634 : Upper (D 6) (R 6) [10,144,33,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16635 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 146 37 76 81 288 102 166 294), lower := (rows 11 146 37 76 81 288 64 128 256), losses := [] }

theorem u16635 : Upper (D 6) (R 6) [10,144,33,68,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16635 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16636 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 37 76 112 33 326 390 262), lower := (rows 11 146 37 76 112 33 64 128 256), losses := [] }

theorem u16636 : Upper (D 6) (R 6) [10,144,33,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16637 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 146 37 76 112 34 325 389 261), lower := (rows 11 146 37 76 112 34 64 128 256), losses := [] }

theorem u16637 : Upper (D 6) (R 6) [10,144,33,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16638 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 466, targets := 4 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,2),(4,0),(4,2)], upper := (rows 11 146 37 76 112 36 323 387 259), lower := (rows 11 146 37 76 112 36 64 128 256), losses := [] }

theorem u16638 : Upper (D 6) (R 6) [10,144,33,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16639 : Route 9 := (fun mask => (mask,id))

def c16639 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16639 : Upper (D 6) (R 6) [10,144,33,68,96,256] 13 := by
  apply FastRouting.sound _ _ [10,144,33,68,96,256] 13 (by decide) (choices 1) [1,2,4] r16639 c16639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4272
  · exact u4273
  · exact u4274

def b16640 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 146 37 76 273 34 100 228 356), lower := (rows 11 146 37 76 273 34 64 128 256), losses := [] }

theorem u16640 : Upper (D 6) (R 6) [10,144,33,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16641 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 146 37 76 273 36 98 226 354), lower := (rows 11 146 37 76 273 36 64 128 256), losses := [] }

theorem u16641 : Upper (D 6) (R 6) [10,144,33,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16641 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16642 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 146 37 76 273 96 102 166 294), lower := (rows 11 146 37 76 273 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 144 37 108 277 96 96 128 256) }] }

theorem u16642 : Upper (D 6) (R 6) [10,144,33,68,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16643 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 37 76 274 33 100 228 356), lower := (rows 11 146 37 76 274 33 64 128 256), losses := [] }

theorem u16643 : Upper (D 6) (R 6) [10,144,33,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16644 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 108, targets := 2 },{ cop := 2, region := 466, targets := 4 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 146 37 76 274 36 97 225 353), lower := (rows 11 146 37 76 274 36 64 128 256), losses := [] }

theorem u16644 : Upper (D 6) (R 6) [10,144,33,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16645 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 108, targets := 2 },{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 11 146 37 76 274 96 101 165 293), lower := (rows 11 146 37 76 274 96 64 128 256), losses := [] }

theorem u16645 : Upper (D 6) (R 6) [10,144,33,68,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16646 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 37 76 276 33 98 226 354), lower := (rows 11 146 37 76 276 33 64 128 256), losses := [] }

theorem u16646 : Upper (D 6) (R 6) [10,144,33,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16647 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 146 37 76 276 34 97 225 353), lower := (rows 11 146 37 76 276 34 64 128 256), losses := [] }

theorem u16647 : Upper (D 6) (R 6) [10,144,33,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16648 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 146 37 76 276 96 99 163 291), lower := (rows 11 146 37 76 276 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 144 37 108 276 96 96 128 256) }] }

theorem u16648 : Upper (D 6) (R 6) [10,144,33,68,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16649 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 37 76 304 33 70 198 326), lower := (rows 11 146 37 76 304 33 64 128 256), losses := [] }

theorem u16649 : Upper (D 6) (R 6) [10,144,33,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16650 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 146 37 76 304 34 69 197 325), lower := (rows 11 146 37 76 304 34 64 128 256), losses := [] }

theorem u16650 : Upper (D 6) (R 6) [10,144,33,68,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16651 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 146 37 76 304 36 67 195 323), lower := (rows 11 146 37 76 304 36 64 128 256), losses := [] }

theorem u16651 : Upper (D 6) (R 6) [10,144,33,68,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16652 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 146 37 76 304 96 71 135 263), lower := (rows 11 146 37 76 304 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 144 37 108 304 96 96 128 256) }] }

theorem u16652 : Upper (D 6) (R 6) [10,144,33,68,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16653 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 37 76 336 33 102 166 294), lower := (rows 11 146 37 76 336 33 64 128 256), losses := [] }

theorem u16653 : Upper (D 6) (R 6) [10,144,33,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16654 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 146 37 76 336 34 101 165 293), lower := (rows 11 146 37 76 336 34 64 128 256), losses := [] }

theorem u16654 : Upper (D 6) (R 6) [10,144,33,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16655 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 466, targets := 4 },{ cop := 0, region := 36, targets := 2 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 11 146 37 76 336 36 99 163 291), lower := (rows 11 146 37 76 336 36 64 128 256), losses := [] }

theorem u16655 : Upper (D 6) (R 6) [10,144,33,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16656 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 146 37 104 273 34 68 196 324), lower := (rows 11 146 37 104 273 34 64 128 256), losses := [] }

theorem u16656 : Upper (D 6) (R 6) [10,144,33,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16657 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 146 37 104 273 36 70 198 326), lower := (rows 11 146 37 104 273 36 64 128 256), losses := [] }

theorem u16657 : Upper (D 6) (R 6) [10,144,33,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16658 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 37 104 273 96 70 134 262), lower := (rows 11 146 37 104 273 96 64 128 256), losses := [] }

theorem u16658 : Upper (D 6) (R 6) [10,144,33,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16659 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 37 104 276 33 70 198 326), lower := (rows 11 146 37 104 276 33 64 128 256), losses := [] }

theorem u16659 : Upper (D 6) (R 6) [10,144,33,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16660 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 146 37 104 276 34 69 197 325), lower := (rows 11 146 37 104 276 34 64 128 256), losses := [] }

theorem u16660 : Upper (D 6) (R 6) [10,144,33,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16661 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 146 37 104 276 36 67 195 323), lower := (rows 11 146 37 104 276 36 64 128 256), losses := [] }

theorem u16661 : Upper (D 6) (R 6) [10,144,33,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16662 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 37 104 276 96 71 135 263), lower := (rows 11 146 37 104 276 96 64 128 256), losses := [] }

theorem u16662 : Upper (D 6) (R 6) [10,144,33,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16663 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 210, targets := 1 },{ cop := 2, region := 328, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 146 37 265 84 34 100 228 356), lower := (rows 11 146 37 265 84 34 64 128 256), losses := [] }

theorem u16663 : Upper (D 6) (R 6) [10,144,33,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16664 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 146 37 265 84 36 98 226 354), lower := (rows 11 146 37 265 84 36 64 128 256), losses := [] }

theorem u16664 : Upper (D 6) (R 6) [10,144,33,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16665 : Route 9 := (fun mask => (mask,id))

def c16665 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16665 : Upper (D 6) (R 6) [10,144,33,257,68,64] 13 := by
  apply FastRouting.sound _ _ [10,144,33,257,68,64] 13 (by decide) (choices 1) [2,4,32] r16665 c16665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4275
  · exact u4276
  · exact u4277

def b16666 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 210, targets := 1 },{ cop := 2, region := 328, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 146 37 265 112 34 68 196 324), lower := (rows 11 146 37 265 112 34 64 128 256), losses := [] }

theorem u16666 : Upper (D 6) (R 6) [10,144,33,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16667 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 146 37 265 112 36 70 198 326), lower := (rows 11 146 37 265 112 36 64 128 256), losses := [] }

theorem u16667 : Upper (D 6) (R 6) [10,144,33,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16668 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 37 265 112 96 70 134 262), lower := (rows 11 146 37 265 112 96 64 128 256), losses := [] }

theorem u16668 : Upper (D 6) (R 6) [10,144,33,257,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16669 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 146 37 268 81 34 100 228 356), lower := (rows 11 146 37 268 81 34 64 128 256), losses := [] }

theorem u16669 : Upper (D 6) (R 6) [10,144,33,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16670 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 210, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 146 37 268 81 36 98 226 354), lower := (rows 11 146 37 268 81 36 64 128 256), losses := [] }

theorem u16670 : Upper (D 6) (R 6) [10,144,33,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16671 : Route 9 := (fun mask => (mask,id))

def c16671 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16671 : Upper (D 6) (R 6) [10,144,33,260,65,64] 13 := by
  apply FastRouting.sound _ _ [10,144,33,260,65,64] 13 (by decide) (choices 1) [2,4,32] r16671 c16671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4278
  · exact u4279
  · exact u4280

def b16672 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 37 268 82 33 100 228 356), lower := (rows 11 146 37 268 82 33 64 128 256), losses := [] }

theorem u16672 : Upper (D 6) (R 6) [10,144,33,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16673 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 210, targets := 4 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 146 37 268 82 36 97 225 353), lower := (rows 11 146 37 268 82 36 64 128 256), losses := [] }

theorem u16673 : Upper (D 6) (R 6) [10,144,33,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16674 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 264, targets := 64 }], pairs := [(2,1),(3,1),(3,6)], upper := (rows 11 146 37 268 82 96 101 165 293), lower := (rows 11 146 37 268 82 96 64 128 256), losses := [] }

theorem u16674 : Upper (D 6) (R 6) [10,144,33,260,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16675 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 37 268 84 33 98 226 354), lower := (rows 11 146 37 268 84 33 64 128 256), losses := [] }

theorem u16675 : Upper (D 6) (R 6) [10,144,33,260,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16676 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 146 37 268 84 34 97 225 353), lower := (rows 11 146 37 268 84 34 64 128 256), losses := [] }

theorem u16676 : Upper (D 6) (R 6) [10,144,33,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16677 : Route 9 := (fun mask => (mask,id))

def c16677 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16677 : Upper (D 6) (R 6) [10,144,33,260,68,64] 13 := by
  apply FastRouting.sound _ _ [10,144,33,260,68,64] 13 (by decide) (choices 1) [1,2,32] r16677 c16677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4281
  · exact u4282
  · exact u4283

def b16678 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 37 268 112 33 70 198 326), lower := (rows 11 146 37 268 112 33 64 128 256), losses := [] }

theorem u16678 : Upper (D 6) (R 6) [10,144,33,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16679 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 146 37 268 112 34 69 197 325), lower := (rows 11 146 37 268 112 34 64 128 256), losses := [] }

theorem u16679 : Upper (D 6) (R 6) [10,144,33,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u16679
end Delivery.IrregularNine14.P06
