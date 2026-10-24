import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0087
import IrregularNine14P06C0088

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18120 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 386 37 104 82 48 69 133 261), lower := (rows 11 386 37 104 82 48 64 128 256), losses := [] }

theorem u18120 : Upper (D 6) (R 6) [10,384,33,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18120 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18121 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 386 37 104 84 33 86 150 278), lower := (rows 11 386 37 104 84 33 64 128 256), losses := [] }

theorem u18121 : Upper (D 6) (R 6) [10,384,33,96,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18122 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 88, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 386 37 104 84 34 85 149 277), lower := (rows 11 386 37 104 84 34 64 128 256), losses := [] }

theorem u18122 : Upper (D 6) (R 6) [10,384,33,96,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18123 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 386 37 104 84 36 83 147 275), lower := (rows 11 386 37 104 84 36 64 128 256), losses := [] }

theorem u18123 : Upper (D 6) (R 6) [10,384,33,96,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18124 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 386 37 104 84 48 71 135 263), lower := (rows 11 386 37 104 84 48 64 128 256), losses := [] }

theorem u18124 : Upper (D 6) (R 6) [10,384,33,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18124 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18125 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 386 38 25 84 33 100 228 356), lower := (rows 11 386 38 25 84 33 64 128 256), losses := [] }

theorem u18125 : Upper (D 6) (R 6) [10,384,34,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18126 : Route 9 := (fun mask => (mask,id))

def c18126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18126 : Upper (D 6) (R 6) [10,384,34,17,68,4] 13 := by
  apply FastRouting.sound _ _ [10,384,34,17,68,4] 13 (by decide) (choices 1) [1,32] r18126 c18126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5265
  · exact u5266

def r18127 : Route 9 := (fun mask => (mask,id))

def c18127 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18127 : Upper (D 6) (R 6) [10,384,34,17,68,64] 13 := by
  apply FastRouting.sound _ _ [10,384,34,17,68,64] 13 (by decide) (choices 1) [1,4,32] r18127 c18127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5267
  · exact u5268
  · exact u5269

def b18128 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 386 38 25 112 33 68 196 324), lower := (rows 11 386 38 25 112 33 64 128 256), losses := [] }

theorem u18128 : Upper (D 6) (R 6) [10,384,34,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18129 : Route 9 := (fun mask => (mask,id))

def c18129 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18129 : Upper (D 6) (R 6) [10,384,34,17,96,4] 13 := by
  apply FastRouting.sound _ _ [10,384,34,17,96,4] 13 (by decide) (choices 1) [1,4] r18129 c18129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5270
  · exact u5271

def b18130 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 386 38 25 112 96 69 133 261), lower := (rows 11 386 38 25 112 96 64 128 256), losses := [] }

theorem u18130 : Upper (D 6) (R 6) [10,384,34,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18131 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 454, targets := 1 },{ cop := 0, region := 36, targets := 64 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 11 386 38 28 81 33 100 228 356), lower := (rows 11 386 38 28 81 33 64 128 256), losses := [] }

theorem u18131 : Upper (D 6) (R 6) [10,384,34,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18132 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 386 38 28 81 36 97 225 353), lower := (rows 11 386 38 28 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 63 64 128 256), good := (rows 46 422 38 60 124 36 64 128 256) }] }

theorem u18132 : Upper (D 6) (R 6) [10,384,34,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18132 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18133 : Route 9 := (fun mask => (mask,id))

def c18133 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18133 : Upper (D 6) (R 6) [10,384,34,20,65,64] 13 := by
  apply FastRouting.sound _ _ [10,384,34,20,65,64] 13 (by decide) (choices 1) [1,4,32] r18133 c18133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5272
  · exact u5273
  · exact u5274

def b18134 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 451, targets := 32 },{ cop := 0, region := 36, targets := 64 }], pairs := [(0,5),(1,5),(2,6)], upper := (rows 11 386 38 28 112 33 69 197 325), lower := (rows 11 386 38 28 112 33 64 128 256), losses := [] }

theorem u18134 : Upper (D 6) (R 6) [10,384,34,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18135 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 451, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 386 38 28 112 36 65 193 321), lower := (rows 11 386 38 28 112 36 64 128 256), losses := [] }

theorem u18135 : Upper (D 6) (R 6) [10,384,34,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18136 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 386 38 28 112 96 69 133 261), lower := (rows 11 386 38 28 112 96 64 128 256), losses := [] }

theorem u18136 : Upper (D 6) (R 6) [10,384,34,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18137 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 386 38 56 81 33 68 196 324), lower := (rows 11 386 38 56 81 33 64 128 256), losses := [] }

theorem u18137 : Upper (D 6) (R 6) [10,384,34,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18138 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 386 38 56 81 36 69 197 325), lower := (rows 11 386 38 56 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 55 64 128 256), good := (rows 46 422 38 56 124 36 64 128 256) }] }

theorem u18138 : Upper (D 6) (R 6) [10,384,34,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18139 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 386 38 56 81 96 69 133 261), lower := (rows 11 386 38 56 81 96 64 128 256), losses := [] }

theorem u18139 : Upper (D 6) (R 6) [10,384,34,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18140 : Route 9 := (fun mask => (mask,id))

def c18140 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18140 : Upper (D 6) (R 6) [10,384,34,48,68,1] 13 := by
  apply FastRouting.sound _ _ [10,384,34,48,68,1] 13 (by decide) (choices 1) [1,4] r18140 c18140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5275
  · exact u5276

def b18141 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 451, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 386 38 56 84 36 65 193 321), lower := (rows 11 386 38 56 84 36 64 128 256), losses := [] }

theorem u18141 : Upper (D 6) (R 6) [10,384,34,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18142 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 386 38 56 84 96 69 133 261), lower := (rows 11 386 38 56 84 96 64 128 256), losses := [] }

theorem u18142 : Upper (D 6) (R 6) [10,384,34,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18143 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 454, targets := 1 }], pairs := [(1,0),(2,6),(4,6)], upper := (rows 11 386 38 73 49 36 84 212 340), lower := (rows 11 386 38 73 49 36 64 128 256), losses := [] }

theorem u18143 : Upper (D 6) (R 6) [10,384,34,65,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18144 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 386 38 73 49 48 68 196 324), lower := (rows 11 386 38 73 49 48 64 128 256), losses := [] }

theorem u18144 : Upper (D 6) (R 6) [10,384,34,65,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18144 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18145 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 48, targets := 6 },{ cop := 4, region := 390, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 386 38 73 49 96 84 148 276), lower := (rows 11 386 38 73 49 96 64 128 256), losses := [] }

theorem u18145 : Upper (D 6) (R 6) [10,384,34,65,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18146 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 386 38 73 84 33 116 180 308), lower := (rows 11 386 38 73 84 33 64 128 256), losses := [] }

theorem u18146 : Upper (D 6) (R 6) [10,384,34,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18147 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 386 38 73 84 36 113 177 305), lower := (rows 11 386 38 73 84 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 8 24 63 64 128 256), good := (rows 62 422 38 124 116 36 64 128 256) }] }

theorem u18147 : Upper (D 6) (R 6) [10,384,34,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18148 : PairBound 9 := { available := 37, camps := [], pairs := [(2,0),(4,0)], upper := (rows 11 386 38 73 84 48 101 165 293), lower := (rows 11 386 38 73 84 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 24 57 64 128 256), good := (rows 62 386 38 124 116 48 64 128 256) }] }

theorem u18148 : Upper (D 6) (R 6) [10,384,34,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18148 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18149 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 386 38 73 112 33 84 148 276), lower := (rows 11 386 38 73 112 33 64 128 256), losses := [] }

theorem u18149 : Upper (D 6) (R 6) [10,384,34,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18150 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 386 38 73 112 36 85 149 277), lower := (rows 11 386 38 73 112 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 8 24 47 64 128 256), good := (rows 62 422 38 124 112 36 64 128 256) }] }

theorem u18150 : Upper (D 6) (R 6) [10,384,34,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18151 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 386 38 73 112 48 69 133 261), lower := (rows 11 386 38 73 112 48 64 128 256), losses := [] }

theorem u18151 : Upper (D 6) (R 6) [10,384,34,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18151 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18152 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 104, targets := 2 }], pairs := [(2,6),(3,1),(4,6)], upper := (rows 11 386 38 76 21 33 112 240 368), lower := (rows 11 386 38 76 21 33 64 128 256), losses := [] }

theorem u18152 : Upper (D 6) (R 6) [10,384,34,68,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18153 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 52, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 386 38 76 21 48 97 225 353), lower := (rows 11 386 38 76 21 48 64 128 256), losses := [] }

theorem u18153 : Upper (D 6) (R 6) [10,384,34,68,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18153 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18154 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 104, targets := 2 },{ cop := 4, region := 482, targets := 4 }], pairs := [(1,2),(2,0),(3,1)], upper := (rows 11 386 38 76 21 96 113 177 305), lower := (rows 11 386 38 76 21 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 104 64 128 256), good := (rows 46 386 38 108 20 96 96 128 256) }] }

theorem u18154 : Upper (D 6) (R 6) [10,384,34,68,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18155 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 386 38 76 49 33 84 212 340), lower := (rows 11 386 38 76 49 33 64 128 256), losses := [] }

theorem u18155 : Upper (D 6) (R 6) [10,384,34,68,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18156 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 450, targets := 4 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 11 386 38 76 49 36 81 209 337), lower := (rows 11 386 38 76 49 36 64 128 256), losses := [] }

theorem u18156 : Upper (D 6) (R 6) [10,384,34,68,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18157 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 386 38 76 49 48 69 197 325), lower := (rows 11 386 38 76 49 48 64 128 256), losses := [] }

theorem u18157 : Upper (D 6) (R 6) [10,384,34,68,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18157 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18158 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 390, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 386 38 76 49 96 85 149 277), lower := (rows 11 386 38 76 49 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 104 64 128 256), good := (rows 46 386 38 108 52 96 96 128 256) }] }

theorem u18158 : Upper (D 6) (R 6) [10,384,34,68,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18159 : Route 9 := (fun mask => (mask,id))

def c18159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18159 : Upper (D 6) (R 6) [10,384,34,68,65,1] 13 := by
  apply FastRouting.sound _ _ [10,384,34,68,65,1] 13 (by decide) (choices 1) [4,16,32] r18159 c18159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5277
  · exact u5278
  · exact u5279

def b18160 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 386 38 76 81 36 113 177 305), lower := (rows 11 386 38 76 81 36 64 128 256), losses := [] }

theorem u18160 : Upper (D 6) (R 6) [10,384,34,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18161 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 386 38 76 81 48 101 165 293), lower := (rows 11 386 38 76 81 48 64 128 256), losses := [] }

theorem u18161 : Upper (D 6) (R 6) [10,384,34,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18161 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18162 : Route 9 := (fun mask => (mask,id))

def c18162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18162 : Upper (D 6) (R 6) [10,384,34,68,96,1] 13 := by
  apply FastRouting.sound _ _ [10,384,34,68,96,1] 13 (by decide) (choices 1) [1,4,16] r18162 c18162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5280
  · exact u5281
  · exact u5282

def b18163 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 3, region := 48, targets := 1 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 386 38 76 112 36 81 145 273), lower := (rows 11 386 38 76 112 36 64 128 256), losses := [] }

theorem u18163 : Upper (D 6) (R 6) [10,384,34,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18164 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 386 38 76 112 48 69 133 261), lower := (rows 11 386 38 76 112 48 64 128 256), losses := [] }

theorem u18164 : Upper (D 6) (R 6) [10,384,34,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18164 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18165 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 5, region := 454, targets := 1 }], pairs := [(1,0),(2,6),(4,6)], upper := (rows 11 386 38 88 21 33 100 228 356), lower := (rows 11 386 38 88 21 33 64 128 256), losses := [] }

theorem u18165 : Upper (D 6) (R 6) [10,384,34,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18166 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 0, region := 36, targets := 1 }], pairs := [(2,0),(2,6),(4,6)], upper := (rows 11 386 38 88 21 36 97 225 353), lower := (rows 11 386 38 88 21 36 64 128 256), losses := [] }

theorem u18166 : Upper (D 6) (R 6) [10,384,34,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18167 : Route 9 := (fun mask => (mask,id))

def c18167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18167 : Upper (D 6) (R 6) [10,384,34,80,5,64] 13 := by
  apply FastRouting.sound _ _ [10,384,34,80,5,64] 13 (by decide) (choices 1) [1,4,32] r18167 c18167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5283
  · exact u5284
  · exact u5285

def b18168 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 386 38 88 49 33 68 196 324), lower := (rows 11 386 38 88 49 33 64 128 256), losses := [] }

theorem u18168 : Upper (D 6) (R 6) [10,384,34,80,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18169 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 0, region := 36, targets := 1 }], pairs := [(2,0),(2,6),(4,6)], upper := (rows 11 386 38 88 49 36 69 197 325), lower := (rows 11 386 38 88 49 36 64 128 256), losses := [] }

theorem u18169 : Upper (D 6) (R 6) [10,384,34,80,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18170 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 390, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 386 38 88 49 96 69 133 261), lower := (rows 11 386 38 88 49 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 104 64 128 256), good := (rows 46 386 38 120 52 96 96 128 256) }] }

theorem u18170 : Upper (D 6) (R 6) [10,384,34,80,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18171 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 450, targets := 1 }], pairs := [(1,0),(2,6),(4,6)], upper := (rows 11 386 38 104 21 33 84 212 340), lower := (rows 11 386 38 104 21 33 64 128 256), losses := [] }

theorem u18171 : Upper (D 6) (R 6) [10,384,34,96,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18172 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 450, targets := 4 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 11 386 38 104 21 36 81 209 337), lower := (rows 11 386 38 104 21 36 64 128 256), losses := [] }

theorem u18172 : Upper (D 6) (R 6) [10,384,34,96,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18173 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 52, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 386 38 104 21 48 69 197 325), lower := (rows 11 386 38 104 21 48 64 128 256), losses := [] }

theorem u18173 : Upper (D 6) (R 6) [10,384,34,96,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18173 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18174 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 386 38 104 21 96 85 149 277), lower := (rows 11 386 38 104 21 96 64 128 256), losses := [] }

theorem u18174 : Upper (D 6) (R 6) [10,384,34,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18175 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 40, targets := 6 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(3,1),(3,2)], upper := (rows 11 386 38 104 81 33 84 148 276), lower := (rows 11 386 38 104 81 33 64 128 256), losses := [] }

theorem u18175 : Upper (D 6) (R 6) [10,384,34,96,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18176 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 386 38 104 81 36 85 149 277), lower := (rows 11 386 38 104 81 36 64 128 256), losses := [] }

theorem u18176 : Upper (D 6) (R 6) [10,384,34,96,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18177 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 386 38 104 81 48 69 133 261), lower := (rows 11 386 38 104 81 48 64 128 256), losses := [] }

theorem u18177 : Upper (D 6) (R 6) [10,384,34,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18177 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18178 : Route 9 := (fun mask => (mask,id))

def c18178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18178 : Upper (D 6) (R 6) [10,384,34,96,68,1] 13 := by
  apply FastRouting.sound _ _ [10,384,34,96,68,1] 13 (by decide) (choices 1) [1,4,16] r18178 c18178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5286
  · exact u5287
  · exact u5288

def b18179 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 4, region := 40, targets := 1 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 386 38 104 84 36 81 145 273), lower := (rows 11 386 38 104 84 36 64 128 256), losses := [] }

theorem u18179 : Upper (D 6) (R 6) [10,384,34,96,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u18179
end Delivery.IrregularNine14.P06
