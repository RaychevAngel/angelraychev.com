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

def b16680 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 210, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 146 37 268 112 36 67 195 323), lower := (rows 11 146 37 268 112 36 64 128 256), losses := [] }

theorem u16680 : Upper (D 6) (R 6) [10,144,33,260,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16680 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16681 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 37 268 112 96 71 135 263), lower := (rows 11 146 37 268 112 96 64 128 256), losses := [] }

theorem u16681 : Upper (D 6) (R 6) [10,144,33,260,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16681 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16682 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 146 37 296 81 34 68 196 324), lower := (rows 11 146 37 296 81 34 64 128 256), losses := [] }

theorem u16682 : Upper (D 6) (R 6) [10,144,33,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16682 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16683 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 146 37 296 81 36 70 198 326), lower := (rows 11 146 37 296 81 36 64 128 256), losses := [] }

theorem u16683 : Upper (D 6) (R 6) [10,144,33,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16683 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16684 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 146 37 296 81 96 70 134 262), lower := (rows 11 146 37 296 81 96 64 128 256), losses := [] }

theorem u16684 : Upper (D 6) (R 6) [10,144,33,288,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16684 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16685 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 37 296 84 33 70 198 326), lower := (rows 11 146 37 296 84 33 64 128 256), losses := [] }

theorem u16685 : Upper (D 6) (R 6) [10,144,33,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16685 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16686 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 146 37 296 84 34 69 197 325), lower := (rows 11 146 37 296 84 34 64 128 256), losses := [] }

theorem u16686 : Upper (D 6) (R 6) [10,144,33,288,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16686 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16687 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 146 37 296 84 36 67 195 323), lower := (rows 11 146 37 296 84 36 64 128 256), losses := [] }

theorem u16687 : Upper (D 6) (R 6) [10,144,33,288,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16687 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16688 : Route 9 := (fun mask => (mask,id))

def c16688 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16688 : Upper (D 6) (R 6) [10,144,33,288,68,64] 13 := by
  apply FastRouting.sound _ _ [10,144,33,288,68,64] 13 (by decide) (choices 1) [1,2,4] r16688 c16688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4284
  · exact u4285
  · exact u4286

def b16689 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 37 328 22 33 100 228 356), lower := (rows 11 146 37 328 22 33 64 128 256), losses := [] }

theorem u16689 : Upper (D 6) (R 6) [10,144,33,320,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16689 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16690 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 146 37 328 22 36 97 225 353), lower := (rows 11 146 37 328 22 36 64 128 256), losses := [] }

theorem u16690 : Upper (D 6) (R 6) [10,144,33,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16690 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16691 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 146, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 11 146 37 328 22 96 101 165 293), lower := (rows 11 146 37 328 22 96 64 128 256), losses := [] }

theorem u16691 : Upper (D 6) (R 6) [10,144,33,320,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16691 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16692 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(3,1),(4,1)], upper := (rows 11 146 37 328 81 34 100 164 292), lower := (rows 11 146 37 328 81 34 64 128 256), losses := [] }

theorem u16692 : Upper (D 6) (R 6) [10,144,33,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16692 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16693 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 166, targets := 64 },{ cop := 0, region := 36, targets := 2 }], pairs := [(1,6),(2,1),(2,6)], upper := (rows 11 146 37 328 81 36 102 166 294), lower := (rows 11 146 37 328 81 36 64 128 256), losses := [] }

theorem u16693 : Upper (D 6) (R 6) [10,144,33,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16693 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16694 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 37 328 84 33 102 166 294), lower := (rows 11 146 37 328 84 33 64 128 256), losses := [] }

theorem u16694 : Upper (D 6) (R 6) [10,144,33,320,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16694 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16695 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 146 37 328 84 34 101 165 293), lower := (rows 11 146 37 328 84 34 64 128 256), losses := [] }

theorem u16695 : Upper (D 6) (R 6) [10,144,33,320,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16695 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16696 : Route 9 := (fun mask => (mask,id))

def c16696 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16696 : Upper (D 6) (R 6) [10,144,33,320,68,4] 13 := by
  apply FastRouting.sound _ _ [10,144,33,320,68,4] 13 (by decide) (choices 1) [1,2,32] r16696 c16696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4287
  · exact u4288
  · exact u4289

def b16697 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 146 37 328 112 33 70 134 262), lower := (rows 11 146 37 328 112 33 64 128 256), losses := [] }

theorem u16697 : Upper (D 6) (R 6) [10,144,33,320,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16697 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16698 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 146 37 328 112 34 69 133 261), lower := (rows 11 146 37 328 112 34 64 128 256), losses := [] }

theorem u16698 : Upper (D 6) (R 6) [10,144,33,320,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16698 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16699 : Route 9 := (fun mask => (mask,id))

def c16699 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16699 : Upper (D 6) (R 6) [10,144,33,320,96,4] 13 := by
  apply FastRouting.sound _ _ [10,144,33,320,96,4] 13 (by decide) (choices 1) [1,2,4] r16699 c16699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4290
  · exact u4291
  · exact u4292

def b16700 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 38 73 84 33 356 420 292), lower := (rows 11 146 38 73 84 33 64 128 256), losses := [] }

theorem u16700 : Upper (D 6) (R 6) [10,144,34,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16700 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16701 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 2, region := 329, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 11 146 38 73 84 36 353 417 289), lower := (rows 11 146 38 73 84 36 64 128 256), losses := [] }

theorem u16701 : Upper (D 6) (R 6) [10,144,34,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16701 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16702 : Route 9 := (fun mask => (mask,id))

def c16702 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16702 : Upper (D 6) (R 6) [10,144,34,65,68,256] 13 := by
  apply FastRouting.sound _ _ [10,144,34,65,68,256] 13 (by decide) (choices 1) [1,4,32] r16702 c16702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4293
  · exact u4294
  · exact u4295

def b16703 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 0, region := 36, targets := 64 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 11 146 38 73 273 36 100 228 356), lower := (rows 11 146 38 73 273 36 64 128 256), losses := [] }

theorem u16703 : Upper (D 6) (R 6) [10,144,34,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16703 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16704 : Route 9 := (fun mask => (mask,id))

def c16704 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16704 : Upper (D 6) (R 6) [10,144,34,65,257,64] 13 := by
  apply FastRouting.sound _ _ [10,144,34,65,257,64] 13 (by decide) (choices 1) [4,32] r16704 c16704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4296
  · exact u4297

def b16705 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 38 73 276 33 100 228 356), lower := (rows 11 146 38 73 276 33 64 128 256), losses := [] }

theorem u16705 : Upper (D 6) (R 6) [10,144,34,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16705 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16706 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 11 146 38 73 276 36 97 225 353), lower := (rows 11 146 38 73 276 36 64 128 256), losses := [] }

theorem u16706 : Upper (D 6) (R 6) [10,144,34,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16706 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16707 : Route 9 := (fun mask => (mask,id))

def c16707 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16707 : Upper (D 6) (R 6) [10,144,34,65,260,64] 13 := by
  apply FastRouting.sound _ _ [10,144,34,65,260,64] 13 (by decide) (choices 1) [1,4,32] r16707 c16707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4298
  · exact u4299
  · exact u4300

def b16708 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 38 73 304 33 68 196 324), lower := (rows 11 146 38 73 304 33 64 128 256), losses := [] }

theorem u16708 : Upper (D 6) (R 6) [10,144,34,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16708 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16709 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(2,0),(2,6)], upper := (rows 11 146 38 73 304 36 69 197 325), lower := (rows 11 146 38 73 304 36 64 128 256), losses := [] }

theorem u16709 : Upper (D 6) (R 6) [10,144,34,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16709 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16710 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(2,0),(3,5)], upper := (rows 11 146 38 73 304 96 69 133 261), lower := (rows 11 146 38 73 304 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 104 64 128 256), good := (rows 46 146 38 108 304 96 96 128 256) }] }

theorem u16710 : Upper (D 6) (R 6) [10,144,34,65,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16710 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16711 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 38 73 336 33 100 164 292), lower := (rows 11 146 38 73 336 33 64 128 256), losses := [] }

theorem u16711 : Upper (D 6) (R 6) [10,144,34,65,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16711 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16712 : Route 9 := (fun mask => (mask,id))

def c16712 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16712 : Upper (D 6) (R 6) [10,144,34,65,320,4] 13 := by
  apply FastRouting.sound _ _ [10,144,34,65,320,4] 13 (by decide) (choices 1) [1,4,32] r16712 c16712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4301
  · exact u4302
  · exact u4303

def b16713 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 328, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 146 38 76 21 33 352 480 352), lower := (rows 11 146 38 76 21 33 64 128 256), losses := [] }

theorem u16713 : Upper (D 6) (R 6) [10,144,34,68,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16713 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16714 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 360, targets := 2 },{ cop := 4, region := 482, targets := 4 }], pairs := [(1,2),(2,0),(3,1)], upper := (rows 11 146 38 76 21 96 353 417 289), lower := (rows 11 146 38 76 21 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 104 64 128 256), good := (rows 46 146 38 108 20 96 96 128 256) }] }

theorem u16714 : Upper (D 6) (R 6) [10,144,34,68,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16714 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16715 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 360, targets := 2 },{ cop := 4, region := 482, targets := 4 }], pairs := [(1,2),(3,1)], upper := (rows 11 146 38 76 21 288 97 225 353), lower := (rows 11 146 38 76 21 288 64 128 256), losses := [] }

theorem u16715 : Upper (D 6) (R 6) [10,144,34,68,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16715 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16716 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 146 38 76 49 33 324 452 324), lower := (rows 11 146 38 76 49 33 64 128 256), losses := [] }

theorem u16716 : Upper (D 6) (R 6) [10,144,34,68,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16716 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16717 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 329, targets := 32 }], pairs := [(0,5),(2,6),(4,6)], upper := (rows 11 146 38 76 49 36 321 449 321), lower := (rows 11 146 38 76 49 36 64 128 256), losses := [] }

theorem u16717 : Upper (D 6) (R 6) [10,144,34,68,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16717 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16718 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 329, targets := 32 },{ cop := 4, region := 390, targets := 64 }], pairs := [(0,5),(1,6),(3,5)], upper := (rows 11 146 38 76 49 96 325 389 261), lower := (rows 11 146 38 76 49 96 64 128 256), losses := [] }

theorem u16718 : Upper (D 6) (R 6) [10,144,34,68,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16718 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16719 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 146 38 76 49 288 69 197 325), lower := (rows 11 146 38 76 49 288 64 128 256), losses := [] }

theorem u16719 : Upper (D 6) (R 6) [10,144,34,68,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16719 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16720 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 328, targets := 3 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 146 38 76 81 33 356 420 292), lower := (rows 11 146 38 76 81 33 64 128 256), losses := [] }

theorem u16720 : Upper (D 6) (R 6) [10,144,34,68,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16721 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 146 38 76 81 36 353 417 289), lower := (rows 11 146 38 76 81 36 64 128 256), losses := [] }

theorem u16721 : Upper (D 6) (R 6) [10,144,34,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16721 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16722 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 146 38 76 81 288 101 165 293), lower := (rows 11 146 38 76 81 288 64 128 256), losses := [] }

theorem u16722 : Upper (D 6) (R 6) [10,144,34,68,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16722 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16723 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 72, targets := 3 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,0),(3,1)], upper := (rows 11 146 38 76 273 33 100 228 356), lower := (rows 11 146 38 76 273 33 64 128 256), losses := [] }

theorem u16723 : Upper (D 6) (R 6) [10,144,34,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16724 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(4,1)], upper := (rows 11 146 38 76 273 36 97 225 353), lower := (rows 11 146 38 76 273 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 65 129 257), good := (rows 505 144 36 108 465 36 64 128 256) }] }

theorem u16724 : Upper (D 6) (R 6) [10,144,34,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16724 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16725 : Route 9 := (fun mask => (mask,id))

def c16725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16725 : Upper (D 6) (R 6) [10,144,34,68,257,64] 13 := by
  apply FastRouting.sound _ _ [10,144,34,68,257,64] 13 (by decide) (choices 1) [1,4,32] r16725 c16725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4304
  · exact u4305
  · exact u4306

def b16726 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 146 38 76 276 33 97 225 353), lower := (rows 11 146 38 76 276 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 33 97 161 289), good := (rows 489 144 508 92 284 481 64 128 256) }] }

theorem u16726 : Upper (D 6) (R 6) [10,144,34,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16727 : Route 9 := (fun mask => (mask,id))

def c16727 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16727 : Upper (D 6) (R 6) [10,144,34,68,260,64] 13 := by
  apply FastRouting.sound _ _ [10,144,34,68,260,64] 13 (by decide) (choices 1) [1,32] r16727 c16727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4307
  · exact u4308

def b16728 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 0, region := 36, targets := 64 }], pairs := [(0,5),(2,6),(3,5)], upper := (rows 11 146 38 76 304 33 69 197 325), lower := (rows 11 146 38 76 304 33 64 128 256), losses := [] }

theorem u16728 : Upper (D 6) (R 6) [10,144,34,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16729 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(2,0),(2,6)], upper := (rows 11 146 38 76 304 36 65 193 321), lower := (rows 11 146 38 76 304 36 64 128 256), losses := [] }

theorem u16729 : Upper (D 6) (R 6) [10,144,34,68,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16730 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(2,0),(3,5)], upper := (rows 11 146 38 76 304 96 69 133 261), lower := (rows 11 146 38 76 304 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 104 64 128 256), good := (rows 46 146 38 108 304 96 96 128 256) }] }

theorem u16730 : Upper (D 6) (R 6) [10,144,34,68,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16731 : Route 9 := (fun mask => (mask,id))

def c16731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16731 : Upper (D 6) (R 6) [10,144,34,68,320,1] 13 := by
  apply FastRouting.sound _ _ [10,144,34,68,320,1] 13 (by decide) (choices 1) [1,4,32] r16731 c16731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4309
  · exact u4310
  · exact u4311

def b16732 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(4,1)], upper := (rows 11 146 38 76 336 36 97 161 289), lower := (rows 11 146 38 76 336 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 65 129 257), good := (rows 505 144 36 108 336 36 64 128 256) }] }

theorem u16732 : Upper (D 6) (R 6) [10,144,34,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16733 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 328, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 146 38 104 21 33 324 452 324), lower := (rows 11 146 38 104 21 33 64 128 256), losses := [] }

theorem u16733 : Upper (D 6) (R 6) [10,144,34,96,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16734 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 329, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 146 38 104 21 36 321 449 321), lower := (rows 11 146 38 104 21 36 64 128 256), losses := [] }

theorem u16734 : Upper (D 6) (R 6) [10,144,34,96,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16735 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 38 104 21 96 325 389 261), lower := (rows 11 146 38 104 21 96 64 128 256), losses := [] }

theorem u16735 : Upper (D 6) (R 6) [10,144,34,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16736 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 360, targets := 2 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(3,1)], upper := (rows 11 146 38 104 21 288 69 197 325), lower := (rows 11 146 38 104 21 288 64 128 256), losses := [] }

theorem u16736 : Upper (D 6) (R 6) [10,144,34,96,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16736 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16737 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 328, targets := 3 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 146 38 104 81 33 324 388 260), lower := (rows 11 146 38 104 81 33 64 128 256), losses := [] }

theorem u16737 : Upper (D 6) (R 6) [10,144,34,96,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16738 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 146 38 104 81 36 325 389 261), lower := (rows 11 146 38 104 81 36 64 128 256), losses := [] }

theorem u16738 : Upper (D 6) (R 6) [10,144,34,96,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16739 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 146 38 104 81 288 69 133 261), lower := (rows 11 146 38 104 81 288 64 128 256), losses := [] }

theorem u16739 : Upper (D 6) (R 6) [10,144,34,96,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16739 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u16739
end Delivery.IrregularNine14.P06
