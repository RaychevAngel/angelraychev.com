import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0009

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7680 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 6, region := 170, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,0)], upper := (rows 37 98 28 200 273 34 65 130 386), lower := (rows 37 98 28 200 273 34 65 128 256), losses := [] }

theorem u7680 : Upper (D 7) (R 7) [36,96,24,192,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7681 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 28 200 273 34 66 129 385), lower := (rows 37 98 28 200 273 34 66 128 256), losses := [] }

theorem u7681 : Upper (D 7) (R 7) [36,96,24,192,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7682 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 98 28 200 273 34 192 131 259), lower := (rows 37 98 28 200 273 34 192 128 256), losses := [] }

theorem u7682 : Upper (D 7) (R 7) [36,96,24,192,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7683 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 28 200 274 33 65 130 386), lower := (rows 37 98 28 200 274 33 65 128 256), losses := [] }

theorem u7683 : Upper (D 7) (R 7) [36,96,24,192,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7684 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 28 200 274 33 66 129 385), lower := (rows 37 98 28 200 274 33 66 128 256), losses := [] }

theorem u7684 : Upper (D 7) (R 7) [36,96,24,192,258,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7685 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 98 28 200 274 33 192 131 259), lower := (rows 37 98 28 200 274 33 192 128 256), losses := [] }

theorem u7685 : Upper (D 7) (R 7) [36,96,24,192,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7686 : Route 9 := (fun mask => (mask,id))

def c7686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7686 : Upper (D 7) (R 7) [36,96,24,192,384,2,1] 13 := by
  apply FastRouting.sound _ _ [36,96,24,192,384,2,1] 13 (by decide) (choices 1) [1,2] r7686 c7686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u582
  · exact u583

def b7687 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 28 200 400 34 66 129 257), lower := (rows 37 98 28 200 400 34 66 128 256), losses := [] }

theorem u7687 : Upper (D 7) (R 7) [36,96,24,192,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7688 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 400, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 98 76 25 146 160 65 386 258), lower := (rows 37 98 76 25 146 160 65 128 256), losses := [] }

theorem u7688 : Upper (D 7) (R 7) [36,96,72,17,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7689 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 417, targets := 66 },{ cop := 5, region := 82, targets := 1 }], pairs := [(0,1),(0,6),(1,0),(4,0)], upper := (rows 37 98 76 25 146 160 66 385 257), lower := (rows 37 98 76 25 146 160 66 128 256), losses := [] }

theorem u7689 : Upper (D 7) (R 7) [36,96,72,17,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7690 : Route 9 := (fun mask => (mask,id))

def c7690 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7690 : Upper (D 7) (R 7) [36,96,72,17,130,128,256] 13 := by
  apply FastRouting.sound _ _ [36,96,72,17,130,128,256] 13 (by decide) (choices 1) [1,2] r7690 c7690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u584
  · exact u585

def b7691 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 98 76 25 146 288 65 130 386), lower := (rows 37 98 76 25 146 288 65 128 256), losses := [] }

theorem u7691 : Upper (D 7) (R 7) [36,96,72,17,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7691 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7692 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 417, targets := 66 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,1),(0,6),(1,0)], upper := (rows 37 98 76 25 146 288 66 129 385), lower := (rows 37 98 76 25 146 288 66 128 256), losses := [] }

theorem u7692 : Upper (D 7) (R 7) [36,96,72,17,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7692 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7693 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,7),(2,0)], upper := (rows 37 98 76 25 146 288 192 131 259), lower := (rows 37 98 76 25 146 288 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 288 208 128 256), good := (rows 36 98 76 92 210 288 192 192 288) }] }

theorem u7693 : Upper (D 7) (R 7) [36,96,72,17,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7693 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7694 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 400, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 98 76 25 274 160 65 130 386), lower := (rows 37 98 76 25 274 160 65 128 256), losses := [] }

theorem u7694 : Upper (D 7) (R 7) [36,96,72,17,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7695 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 5, region := 66, targets := 129 }], pairs := [(0,1),(0,6),(1,0),(1,7)], upper := (rows 37 98 76 25 274 160 66 129 385), lower := (rows 37 98 76 25 274 160 66 128 256), losses := [] }

theorem u7695 : Upper (D 7) (R 7) [36,96,72,17,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7696 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 76 25 274 160 192 131 259), lower := (rows 37 98 76 25 274 160 192 128 256), losses := [] }

theorem u7696 : Upper (D 7) (R 7) [36,96,72,17,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7697 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 111, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 98 76 25 400 34 65 130 386), lower := (rows 37 98 76 25 400 34 65 128 256), losses := [] }

theorem u7697 : Upper (D 7) (R 7) [36,96,72,17,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7698 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 98 76 25 400 34 66 129 385), lower := (rows 37 98 76 25 400 34 66 128 256), losses := [] }

theorem u7698 : Upper (D 7) (R 7) [36,96,72,17,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7699 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 37 98 76 25 400 34 192 131 259), lower := (rows 37 98 76 25 400 34 192 128 256), losses := [{ target := 0, region := (rows 0 222 12 8 16 255 208 128 256), good := (rows 38 98 110 126 498 34 226 226 256) }] }

theorem u7699 : Upper (D 7) (R 7) [36,96,72,17,384,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7700 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 400, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 98 76 25 400 160 65 130 258), lower := (rows 37 98 76 25 400 160 65 128 256), losses := [] }

theorem u7700 : Upper (D 7) (R 7) [36,96,72,17,384,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7701 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 37 98 76 25 400 160 66 131 259), lower := (rows 37 98 76 25 400 160 66 128 256), losses := [{ target := 0, region := (rows 0 187 12 8 16 176 255 128 256), good := (rows 102 98 78 126 498 226 66 226 256) },{ target := 7, region := (rows 1 35 12 8 16 32 107 0 265), good := (rows 359 98 332 351 272 98 66 0 256) }] }

theorem u7701 : Upper (D 7) (R 7) [36,96,72,17,384,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7702 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 66, targets := 128 },{ cop := 2, region := 418, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 37 98 76 26 145 160 65 386 258), lower := (rows 37 98 76 26 145 160 65 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 93 128 256), good := (rows 101 96 77 125 241 160 65 160 256) }] }

theorem u7702 : Upper (D 7) (R 7) [36,96,72,18,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7703 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 98 76 26 145 160 66 385 257), lower := (rows 37 98 76 26 145 160 66 128 256), losses := [] }

theorem u7703 : Upper (D 7) (R 7) [36,96,72,18,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7704 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 37 98 76 26 145 160 320 131 259), lower := (rows 37 98 76 26 145 160 320 128 256), losses := [{ target := 7, region := (rows 1 3 28 24 16 32 345 0 273), good := (rows 359 98 76 350 351 32 320 0 320) }] }

theorem u7704 : Upper (D 7) (R 7) [36,96,72,18,129,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7704 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7705 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 66, targets := 128 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(1,7),(2,1)], upper := (rows 37 98 76 26 145 288 65 130 386), lower := (rows 37 98 76 26 145 288 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 288 81 128 256), good := (rows 101 96 76 92 209 288 65 128 288) }] }

theorem u7705 : Upper (D 7) (R 7) [36,96,72,18,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7705 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7706 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 76 26 145 288 66 129 385), lower := (rows 37 98 76 26 145 288 66 128 256), losses := [] }

theorem u7706 : Upper (D 7) (R 7) [36,96,72,18,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7706 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7707 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,7),(2,0)], upper := (rows 37 98 76 26 145 288 192 131 259), lower := (rows 37 98 76 26 145 288 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 288 208 128 256), good := (rows 36 98 76 94 208 288 192 192 288) }] }

theorem u7707 : Upper (D 7) (R 7) [36,96,72,18,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7707 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7708 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 66, targets := 128 },{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(1,7),(2,1),(2,5)], upper := (rows 37 98 76 26 273 160 65 130 386), lower := (rows 37 98 76 26 273 160 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 160 81 128 256), good := (rows 101 96 76 92 337 160 65 160 256) },{ target := 5, region := (rows 1 2 12 8 16 0 81 138 266), good := (rows 69 450 460 478 337 128 65 128 256) }] }

theorem u7708 : Upper (D 7) (R 7) [36,96,72,18,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7709 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 98 76 26 273 160 66 129 385), lower := (rows 37 98 76 26 273 160 66 128 256), losses := [] }

theorem u7709 : Upper (D 7) (R 7) [36,96,72,18,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7710 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 76 26 273 160 192 131 259), lower := (rows 37 98 76 26 273 160 192 128 256), losses := [] }

theorem u7710 : Upper (D 7) (R 7) [36,96,72,18,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7711 : Route 9 := (fun mask => (mask,id))

def c7711 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7711 : Upper (D 7) (R 7) [36,96,72,18,384,128,1] 13 := by
  apply FastRouting.sound _ _ [36,96,72,18,384,128,1] 13 (by decide) (choices 1) [1,2] r7711 c7711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u586
  · exact u587

def b7712 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 98 76 26 400 160 66 129 257), lower := (rows 37 98 76 26 400 160 66 128 256), losses := [] }

theorem u7712 : Upper (D 7) (R 7) [36,96,72,18,384,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7713 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 1, region := 400, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(4,0)], upper := (rows 37 98 76 137 146 34 65 400 272), lower := (rows 37 98 76 137 146 34 65 128 256), losses := [] }

theorem u7713 : Upper (D 7) (R 7) [36,96,72,129,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7714 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 392, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 37 98 76 137 146 34 80 385 257), lower := (rows 37 98 76 137 146 34 80 128 256), losses := [] }

theorem u7714 : Upper (D 7) (R 7) [36,96,72,129,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7714 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7715 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 76 137 146 34 320 145 273), lower := (rows 37 98 76 137 146 34 320 128 256), losses := [] }

theorem u7715 : Upper (D 7) (R 7) [36,96,72,129,130,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7715 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7716 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 98 76 137 146 48 65 386 258), lower := (rows 37 98 76 137 146 48 65 128 256), losses := [] }

theorem u7716 : Upper (D 7) (R 7) [36,96,72,129,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7716 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7717 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 392, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 37 98 76 137 146 48 66 385 257), lower := (rows 37 98 76 137 146 48 66 128 256), losses := [] }

theorem u7717 : Upper (D 7) (R 7) [36,96,72,129,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7717 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7718 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7),(2,7)], upper := (rows 37 98 76 137 146 48 320 131 259), lower := (rows 37 98 76 137 146 48 320 128 256), losses := [{ target := 7, region := (rows 1 3 12 8 16 48 333 0 265), good := (rows 359 98 332 335 50 48 320 0 320) }] }

theorem u7718 : Upper (D 7) (R 7) [36,96,72,129,130,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7718 [(5,4),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7719 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 98 76 137 146 288 65 146 274), lower := (rows 37 98 76 137 146 288 65 128 256), losses := [] }

theorem u7719 : Upper (D 7) (R 7) [36,96,72,129,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7719 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7720 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(2,0)], upper := (rows 37 98 76 137 146 288 66 145 273), lower := (rows 37 98 76 137 146 288 66 128 256), losses := [{ target := 0, region := (rows 0 291 12 8 24 288 379 128 256), good := (rows 102 98 92 222 210 354 66 128 354) }] }

theorem u7720 : Upper (D 7) (R 7) [36,96,72,129,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7720 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7721 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 98 76 137 146 288 80 131 259), lower := (rows 37 98 76 137 146 288 80 128 256), losses := [] }

theorem u7721 : Upper (D 7) (R 7) [36,96,72,129,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7721 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7722 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 408, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 98 76 137 273 34 66 144 400), lower := (rows 37 98 76 137 273 34 66 128 256), losses := [] }

theorem u7722 : Upper (D 7) (R 7) [36,96,72,129,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7723 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 76 137 273 34 80 130 386), lower := (rows 37 98 76 137 273 34 80 128 256), losses := [] }

theorem u7723 : Upper (D 7) (R 7) [36,96,72,129,257,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7723 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7724 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 37 98 76 137 273 34 192 146 274), lower := (rows 37 98 76 137 273 34 192 128 256), losses := [] }

theorem u7724 : Upper (D 7) (R 7) [36,96,72,129,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7725 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 66, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,0)], upper := (rows 37 98 76 137 273 48 66 130 386), lower := (rows 37 98 76 137 273 48 66 128 256), losses := [{ target := 0, region := (rows 0 51 12 8 16 48 123 251 379), good := (rows 486 482 460 462 498 498 450 128 256) }] }

theorem u7725 : Upper (D 7) (R 7) [36,96,72,129,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7725 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7726 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 98 76 137 273 48 192 130 258), lower := (rows 37 98 76 137 273 48 192 128 256), losses := [] }

theorem u7726 : Upper (D 7) (R 7) [36,96,72,129,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7726 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7727 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 1, region := 400, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(4,0)], upper := (rows 37 98 76 137 274 34 65 144 400), lower := (rows 37 98 76 137 274 34 65 128 256), losses := [] }

theorem u7727 : Upper (D 7) (R 7) [36,96,72,129,258,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7728 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 76 137 274 34 80 129 385), lower := (rows 37 98 76 137 274 34 80 128 256), losses := [] }

theorem u7728 : Upper (D 7) (R 7) [36,96,72,129,258,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7728 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7729 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 37 98 76 137 274 34 192 145 273), lower := (rows 37 98 76 137 274 34 192 128 256), losses := [] }

theorem u7729 : Upper (D 7) (R 7) [36,96,72,129,258,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7730 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 98 76 137 274 48 65 130 386), lower := (rows 37 98 76 137 274 48 65 128 256), losses := [] }

theorem u7730 : Upper (D 7) (R 7) [36,96,72,129,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7730 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7731 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 76 137 274 48 66 129 385), lower := (rows 37 98 76 137 274 48 66 128 256), losses := [] }

theorem u7731 : Upper (D 7) (R 7) [36,96,72,129,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7731 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7732 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 98 76 137 274 48 192 131 259), lower := (rows 37 98 76 137 274 48 192 128 256), losses := [] }

theorem u7732 : Upper (D 7) (R 7) [36,96,72,129,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7732 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7733 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 1, region := 400, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(4,0)], upper := (rows 37 98 76 137 400 34 65 146 274), lower := (rows 37 98 76 137 400 34 65 128 256), losses := [] }

theorem u7733 : Upper (D 7) (R 7) [36,96,72,129,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7734 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 98 76 137 400 34 66 145 273), lower := (rows 37 98 76 137 400 34 66 128 256), losses := [] }

theorem u7734 : Upper (D 7) (R 7) [36,96,72,129,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7735 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 76 137 400 34 80 131 259), lower := (rows 37 98 76 137 400 34 80 128 256), losses := [] }

theorem u7735 : Upper (D 7) (R 7) [36,96,72,129,384,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7735 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7736 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 98 76 137 400 48 65 130 258), lower := (rows 37 98 76 137 400 48 65 128 256), losses := [] }

theorem u7736 : Upper (D 7) (R 7) [36,96,72,129,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7736 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7737 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 98, targets := 129 }], pairs := [(1,0),(1,7),(2,0)], upper := (rows 37 98 76 137 400 48 66 131 259), lower := (rows 37 98 76 137 400 48 66 128 256), losses := [{ target := 0, region := (rows 0 51 12 8 16 48 123 128 256), good := (rows 102 98 76 206 498 114 66 128 256) }] }

theorem u7737 : Upper (D 7) (R 7) [36,96,72,129,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7737 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7738 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 396, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 76 138 145 48 65 386 258), lower := (rows 37 98 76 138 145 48 65 128 256), losses := [] }

theorem u7738 : Upper (D 7) (R 7) [36,96,72,130,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7738 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7739 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 76 138 145 48 66 385 257), lower := (rows 37 98 76 138 145 48 66 128 256), losses := [] }

theorem u7739 : Upper (D 7) (R 7) [36,96,72,130,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7739 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u7739
end Delivery.IrregularNine14.P07
