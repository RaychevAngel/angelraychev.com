import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0013

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11040 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 262 44 74 19 160 192 145 273), lower := (rows 97 262 44 74 19 160 192 128 256), losses := [] }

theorem u11040 : Upper (D 7) (R 7) [96,260,40,66,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11041 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 262 44 74 145 48 65 130 386), lower := (rows 97 262 44 74 145 48 65 128 256), losses := [] }

theorem u11041 : Upper (D 7) (R 7) [96,260,40,66,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11041 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11042 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 72, targets := 161 }], pairs := [(3,0),(3,5),(3,7)], upper := (rows 97 262 44 74 145 48 66 129 385), lower := (rows 97 262 44 74 145 48 66 128 256), losses := [] }

theorem u11042 : Upper (D 7) (R 7) [96,260,40,66,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11042 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11043 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 262 44 74 145 48 192 131 259), lower := (rows 97 262 44 74 145 48 192 128 256), losses := [] }

theorem u11043 : Upper (D 7) (R 7) [96,260,40,66,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11043 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11044 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 65, targets := 130 },{ cop := 5, region := 81, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,1)], upper := (rows 97 262 44 74 145 160 65 146 274), lower := (rows 97 262 44 74 145 160 65 128 256), losses := [{ target := 7, region := (rows 37 2 4 10 16 32 119 0 256), good := (rows 97 335 109 74 81 97 65 0 256) }] }

theorem u11044 : Upper (D 7) (R 7) [96,260,40,66,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11045 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 72, targets := 161 },{ cop := 3, region := 177, targets := 2 }], pairs := [(0,1),(3,0),(3,5),(3,7)], upper := (rows 97 262 44 74 145 160 66 145 273), lower := (rows 97 262 44 74 145 160 66 128 256), losses := [] }

theorem u11045 : Upper (D 7) (R 7) [96,260,40,66,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11046 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 262 44 74 145 160 80 131 259), lower := (rows 97 262 44 74 145 160 80 128 256), losses := [] }

theorem u11046 : Upper (D 7) (R 7) [96,260,40,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11046 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11047 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 262 44 74 146 48 65 129 385), lower := (rows 97 262 44 74 146 48 65 128 256), losses := [] }

theorem u11047 : Upper (D 7) (R 7) [96,260,40,66,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11047 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11048 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 262 44 74 146 48 192 129 257), lower := (rows 97 262 44 74 146 48 192 128 256), losses := [] }

theorem u11048 : Upper (D 7) (R 7) [96,260,40,66,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11048 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11049 : Route 9 := (fun mask => (mask,id))

def c11049 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11049 : Upper (D 7) (R 7) [96,260,40,66,130,128,1] 13 := by
  apply FastRouting.sound _ _ [96,260,40,66,130,128,1] 13 (by decide) (choices 1) [1,16] r11049 c11049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u819
  · exact u820

def b11050 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 262 44 74 146 160 80 129 257), lower := (rows 97 262 44 74 146 160 80 128 256), losses := [] }

theorem u11050 : Upper (D 7) (R 7) [96,260,40,66,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11050 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11051 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 262 44 88 19 160 65 130 386), lower := (rows 97 262 44 88 19 160 65 128 256), losses := [] }

theorem u11051 : Upper (D 7) (R 7) [96,260,40,80,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11052 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 165, targets := 2 },{ cop := 4, region := 72, targets := 129 }], pairs := [(0,1),(2,1),(3,0),(3,7)], upper := (rows 97 262 44 88 19 160 66 129 385), lower := (rows 97 262 44 88 19 160 66 128 256), losses := [] }

theorem u11052 : Upper (D 7) (R 7) [96,260,40,80,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11053 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 262 44 88 19 160 192 131 259), lower := (rows 97 262 44 88 19 160 192 128 256), losses := [] }

theorem u11053 : Upper (D 7) (R 7) [96,260,40,80,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11054 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 262 44 88 145 34 65 130 386), lower := (rows 97 262 44 88 145 34 65 128 256), losses := [] }

theorem u11054 : Upper (D 7) (R 7) [96,260,40,80,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11055 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 0, region := 152, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 97 262 44 88 145 34 66 129 385), lower := (rows 97 262 44 88 145 34 66 128 256), losses := [] }

theorem u11055 : Upper (D 7) (R 7) [96,260,40,80,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11056 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 262 44 88 145 34 192 131 259), lower := (rows 97 262 44 88 145 34 192 128 256), losses := [] }

theorem u11056 : Upper (D 7) (R 7) [96,260,40,80,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11057 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 140, targets := 2 },{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 97 262 44 137 19 34 80 192 448), lower := (rows 97 262 44 137 19 34 80 128 256), losses := [] }

theorem u11057 : Upper (D 7) (R 7) [96,260,40,129,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11057 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11058 : Route 9 := (fun mask => (mask,id))

def c11058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11058 : Upper (D 7) (R 7) [96,260,40,129,3,2,128] 13 := by
  apply FastRouting.sound _ _ [96,260,40,129,3,2,128] 13 (by decide) (choices 1) [16,64] r11058 c11058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u821
  · exact u822

def b11059 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 113, targets := 128 },{ cop := 2, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(1,5),(4,7)], upper := (rows 97 262 44 137 82 34 65 144 400), lower := (rows 97 262 44 137 82 34 65 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 20 0 73 150 278), good := (rows 65 406 478 201 466 386 65 128 256) }] }

theorem u11059 : Upper (D 7) (R 7) [96,260,40,129,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11060 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 44 137 82 34 80 129 385), lower := (rows 97 262 44 137 82 34 80 128 256), losses := [] }

theorem u11060 : Upper (D 7) (R 7) [96,260,40,129,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11060 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11061 : Route 9 := (fun mask => (mask,id))

def c11061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11061 : Upper (D 7) (R 7) [96,260,40,129,66,2,128] 13 := by
  apply FastRouting.sound _ _ [96,260,40,129,66,2,128] 13 (by decide) (choices 1) [1,16] r11061 c11061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u823
  · exact u824

def b11062 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 65, targets := 130 }], pairs := [(0,1),(0,7),(1,5),(4,5)], upper := (rows 97 262 44 137 146 34 65 208 336), lower := (rows 97 262 44 137 146 34 65 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 22 0 73 132 260), good := (rows 65 406 478 201 146 18 65 128 256) }] }

theorem u11062 : Upper (D 7) (R 7) [96,260,40,129,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11063 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 140, targets := 2 },{ cop := 0, region := 136, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 97 262 44 137 146 34 80 193 321), lower := (rows 97 262 44 137 146 34 80 128 256), losses := [] }

theorem u11063 : Upper (D 7) (R 7) [96,260,40,129,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11063 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11064 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 262 44 137 146 48 65 194 322), lower := (rows 97 262 44 137 146 48 65 128 256), losses := [] }

theorem u11064 : Upper (D 7) (R 7) [96,260,40,129,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11064 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11065 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 140, targets := 2 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 97 262 44 137 146 48 66 193 321), lower := (rows 97 262 44 137 146 48 66 128 256), losses := [] }

theorem u11065 : Upper (D 7) (R 7) [96,260,40,129,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11065 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11066 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 65, targets := 130 },{ cop := 3, region := 80, targets := 34 }], pairs := [(0,1),(0,7),(4,1),(4,5)], upper := (rows 97 262 44 137 208 34 65 146 274), lower := (rows 97 262 44 137 208 34 65 128 256), losses := [] }

theorem u11066 : Upper (D 7) (R 7) [96,260,40,129,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11067 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 0, region := 152, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 97 262 44 137 208 34 66 145 273), lower := (rows 97 262 44 137 208 34 66 128 256), losses := [] }

theorem u11067 : Upper (D 7) (R 7) [96,260,40,129,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11068 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 44 137 208 34 80 131 259), lower := (rows 97 262 44 137 208 34 80 128 256), losses := [] }

theorem u11068 : Upper (D 7) (R 7) [96,260,40,129,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11068 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11069 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 262 44 138 19 48 65 192 448), lower := (rows 97 262 44 138 19 48 65 128 256), losses := [] }

theorem u11069 : Upper (D 7) (R 7) [96,260,40,130,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11069 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11070 : Route 9 := (fun mask => (mask,id))

def c11070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11070 : Upper (D 7) (R 7) [96,260,40,130,3,16,128] 13 := by
  apply FastRouting.sound _ _ [96,260,40,130,3,16,128] 13 (by decide) (choices 1) [1,64] r11070 c11070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u825
  · exact u826

def b11071 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 44 138 82 33 65 144 400), lower := (rows 97 262 44 138 82 33 65 128 256), losses := [] }

theorem u11071 : Upper (D 7) (R 7) [96,260,40,130,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11072 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 44 138 82 33 80 129 385), lower := (rows 97 262 44 138 82 33 80 128 256), losses := [] }

theorem u11072 : Upper (D 7) (R 7) [96,260,40,130,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11072 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11073 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 33 },{ cop := 3, region := 101, targets := 2 }], pairs := [(0,1),(2,1),(4,0),(4,5)], upper := (rows 97 262 44 138 82 33 192 145 273), lower := (rows 97 262 44 138 82 33 192 128 256), losses := [] }

theorem u11073 : Upper (D 7) (R 7) [96,260,40,130,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11074 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 97 262 44 138 145 33 66 208 336), lower := (rows 97 262 44 138 145 33 66 128 256), losses := [] }

theorem u11074 : Upper (D 7) (R 7) [96,260,40,130,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11075 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 262 44 138 145 33 80 194 322), lower := (rows 97 262 44 138 145 33 80 128 256), losses := [] }

theorem u11075 : Upper (D 7) (R 7) [96,260,40,130,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11075 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11076 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 262 44 138 145 48 65 194 322), lower := (rows 97 262 44 138 145 48 65 128 256), losses := [] }

theorem u11076 : Upper (D 7) (R 7) [96,260,40,130,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11076 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11077 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(1,7)], upper := (rows 97 262 44 138 145 48 66 193 321), lower := (rows 97 262 44 138 145 48 66 128 256), losses := [] }

theorem u11077 : Upper (D 7) (R 7) [96,260,40,130,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11077 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11078 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 44 138 208 33 65 146 274), lower := (rows 97 262 44 138 208 33 65 128 256), losses := [] }

theorem u11078 : Upper (D 7) (R 7) [96,260,40,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11079 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 33 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(4,0),(4,5)], upper := (rows 97 262 44 138 208 33 66 145 273), lower := (rows 97 262 44 138 208 33 66 128 256), losses := [] }

theorem u11079 : Upper (D 7) (R 7) [96,260,40,130,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11080 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 44 138 208 33 80 131 259), lower := (rows 97 262 44 138 208 33 80 128 256), losses := [] }

theorem u11080 : Upper (D 7) (R 7) [96,260,40,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11080 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11081 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 113, targets := 128 },{ cop := 4, region := 200, targets := 34 }], pairs := [(0,7),(3,1),(3,5),(4,7)], upper := (rows 97 262 44 200 19 34 65 144 400), lower := (rows 97 262 44 200 19 34 65 128 256), losses := [] }

theorem u11081 : Upper (D 7) (R 7) [96,260,40,192,3,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11082 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 140, targets := 2 },{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 97 262 44 200 19 34 80 129 385), lower := (rows 97 262 44 200 19 34 80 128 256), losses := [] }

theorem u11082 : Upper (D 7) (R 7) [96,260,40,192,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11082 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11083 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 97 262 44 200 19 34 192 145 273), lower := (rows 97 262 44 200 19 34 192 128 256), losses := [] }

theorem u11083 : Upper (D 7) (R 7) [96,260,40,192,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11084 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 262 44 200 19 48 65 130 386), lower := (rows 97 262 44 200 19 48 65 128 256), losses := [] }

theorem u11084 : Upper (D 7) (R 7) [96,260,40,192,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11084 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11085 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 140, targets := 2 },{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 97 262 44 200 19 48 66 129 385), lower := (rows 97 262 44 200 19 48 66 128 256), losses := [] }

theorem u11085 : Upper (D 7) (R 7) [96,260,40,192,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11085 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11086 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 262 44 200 19 48 192 131 259), lower := (rows 97 262 44 200 19 48 192 128 256), losses := [] }

theorem u11086 : Upper (D 7) (R 7) [96,260,40,192,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11086 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11087 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 65, targets := 130 },{ cop := 4, region := 72, targets := 34 }], pairs := [(0,1),(0,7),(3,1),(3,5)], upper := (rows 97 262 44 200 145 34 65 146 274), lower := (rows 97 262 44 200 145 34 65 128 256), losses := [] }

theorem u11087 : Upper (D 7) (R 7) [96,260,40,192,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11088 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 156, targets := 2 },{ cop := 0, region := 152, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 97 262 44 200 145 34 66 145 273), lower := (rows 97 262 44 200 145 34 66 128 256), losses := [] }

theorem u11088 : Upper (D 7) (R 7) [96,260,40,192,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11089 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 262 44 200 145 34 80 131 259), lower := (rows 97 262 44 200 145 34 80 128 256), losses := [] }

theorem u11089 : Upper (D 7) (R 7) [96,260,40,192,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11089 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11090 : Route 9 := (fun mask => (mask,id))

def c11090 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11090 : Upper (D 7) (R 7) [96,260,40,192,130,2,1] 13 := by
  apply FastRouting.sound _ _ [96,260,40,192,130,2,1] 13 (by decide) (choices 1) [1,16] r11090 c11090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u827
  · exact u828

def b11091 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 262 44 200 146 34 80 129 257), lower := (rows 97 262 44 200 146 34 80 128 256), losses := [] }

theorem u11091 : Upper (D 7) (R 7) [96,260,40,192,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11091 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11092 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 262 44 200 146 48 65 131 259), lower := (rows 97 262 44 200 146 48 65 128 256), losses := [] }

theorem u11092 : Upper (D 7) (R 7) [96,260,40,192,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11092 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11093 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 140, targets := 2 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 97 262 44 200 146 48 66 129 257), lower := (rows 97 262 44 200 146 48 66 128 256), losses := [] }

theorem u11093 : Upper (D 7) (R 7) [96,260,40,192,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11093 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11094 : Route 9 := (fun mask => (mask,id))

def c11094 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11094 : Upper (D 7) (R 7) [96,260,129,3,40,128,2] 13 := by
  apply FastRouting.sound _ _ [96,260,129,3,40,128,2] 13 (by decide) (choices 1) [16,64] r11094 c11094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u829
  · exact u830

def b11095 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 133 11 56 160 80 194 322), lower := (rows 97 262 133 11 56 160 80 128 256), losses := [] }

theorem u11095 : Upper (D 7) (R 7) [96,260,129,3,40,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11095 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11096 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 132, targets := 2 },{ cop := 3, region := 240, targets := 1 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 97 262 133 11 152 34 80 224 352), lower := (rows 97 262 133 11 152 34 80 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 24 46 88 153 281), good := (rows 480 294 422 506 504 34 464 128 256) }] }

theorem u11096 : Upper (D 7) (R 7) [96,260,129,3,136,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11096 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11097 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 262 133 11 152 34 96 208 336), lower := (rows 97 262 133 11 152 34 96 128 256), losses := [] }

theorem u11097 : Upper (D 7) (R 7) [96,260,129,3,136,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11098 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 262 133 11 152 48 96 194 322), lower := (rows 97 262 133 11 152 48 96 128 256), losses := [] }

theorem u11098 : Upper (D 7) (R 7) [96,260,129,3,136,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11098 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11099 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 148, targets := 2 },{ cop := 1, region := 105, targets := 128 }], pairs := [(0,7),(2,1),(4,1)], upper := (rows 97 262 133 11 176 34 72 208 336), lower := (rows 97 262 133 11 176 34 72 128 256), losses := [] }

theorem u11099 : Upper (D 7) (R 7) [96,260,129,3,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11099 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11099
end Delivery.IrregularNine14.P07
