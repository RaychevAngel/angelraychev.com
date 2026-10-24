import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0087

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18060 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 386 22 41 112 33 68 196 324), lower := (rows 11 386 22 41 112 33 64 128 256), losses := [] }

theorem u18060 : Upper (D 6) (R 6) [10,384,18,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18061 : Route 9 := (fun mask => (mask,id))

def c18061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18061 : Upper (D 6) (R 6) [10,384,18,33,96,4] 13 := by
  apply FastRouting.sound _ _ [10,384,18,33,96,4] 13 (by decide) (choices 1) [1,4] r18061 c18061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5263
  · exact u5264

def b18062 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 386 22 41 112 96 69 133 261), lower := (rows 11 386 22 41 112 96 64 128 256), losses := [] }

theorem u18062 : Upper (D 6) (R 6) [10,384,18,33,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18063 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 450, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 386 22 44 81 33 100 228 356), lower := (rows 11 386 22 44 81 33 64 128 256), losses := [] }

theorem u18063 : Upper (D 6) (R 6) [10,384,18,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18064 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 386 22 44 81 36 97 225 353), lower := (rows 11 386 22 44 81 36 64 128 256), losses := [] }

theorem u18064 : Upper (D 6) (R 6) [10,384,18,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18065 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(3,0)], upper := (rows 11 386 22 44 81 96 101 165 293), lower := (rows 11 386 22 44 81 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 112 64 128 256), good := (rows 10 386 62 44 112 96 96 128 256) }] }

theorem u18065 : Upper (D 6) (R 6) [10,384,18,36,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18066 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 451, targets := 32 }], pairs := [(0,5),(0,6),(3,6)], upper := (rows 11 386 22 44 112 33 69 197 325), lower := (rows 11 386 22 44 112 33 64 128 256), losses := [] }

theorem u18066 : Upper (D 6) (R 6) [10,384,18,36,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18067 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 386 22 44 112 36 65 193 321), lower := (rows 11 386 22 44 112 36 64 128 256), losses := [] }

theorem u18067 : Upper (D 6) (R 6) [10,384,18,36,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18068 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 386 22 44 112 96 69 133 261), lower := (rows 11 386 22 44 112 96 64 128 256), losses := [] }

theorem u18068 : Upper (D 6) (R 6) [10,384,18,36,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18069 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 88, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 386 37 25 84 34 100 228 356), lower := (rows 11 386 37 25 84 34 64 128 256), losses := [] }

theorem u18069 : Upper (D 6) (R 6) [10,384,33,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18070 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 386 37 25 84 36 98 226 354), lower := (rows 11 386 37 25 84 36 64 128 256), losses := [] }

theorem u18070 : Upper (D 6) (R 6) [10,384,33,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18071 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 386 37 25 84 96 102 166 294), lower := (rows 11 386 37 25 84 96 64 128 256), losses := [] }

theorem u18071 : Upper (D 6) (R 6) [10,384,33,17,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18072 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 88, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 386 37 28 81 34 100 228 356), lower := (rows 11 386 37 28 81 34 64 128 256), losses := [] }

theorem u18072 : Upper (D 6) (R 6) [10,384,33,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18073 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 386 37 28 81 36 98 226 354), lower := (rows 11 386 37 28 81 36 64 128 256), losses := [] }

theorem u18073 : Upper (D 6) (R 6) [10,384,33,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18074 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 44, targets := 2 },{ cop := 2, region := 386, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 386 37 28 81 96 102 166 294), lower := (rows 11 386 37 28 81 96 64 128 256), losses := [] }

theorem u18074 : Upper (D 6) (R 6) [10,384,33,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18075 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 386 37 28 82 33 100 228 356), lower := (rows 11 386 37 28 82 33 64 128 256), losses := [] }

theorem u18075 : Upper (D 6) (R 6) [10,384,33,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18076 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 386 37 28 82 36 97 225 353), lower := (rows 11 386 37 28 82 36 64 128 256), losses := [] }

theorem u18076 : Upper (D 6) (R 6) [10,384,33,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18077 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 2, region := 386, targets := 64 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 11 386 37 28 82 96 101 165 293), lower := (rows 11 386 37 28 82 96 64 128 256), losses := [{ target := 6, region := (rows 9 14 4 8 16 32 0 132 260), good := (rows 11 386 423 415 18 32 0 128 256) }] }

theorem u18077 : Upper (D 6) (R 6) [10,384,33,20,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18077 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18078 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 386 37 28 112 33 70 198 326), lower := (rows 11 386 37 28 112 33 64 128 256), losses := [] }

theorem u18078 : Upper (D 6) (R 6) [10,384,33,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18079 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 88, targets := 2 },{ cop := 3, region := 451, targets := 32 }], pairs := [(0,5),(3,1),(4,1)], upper := (rows 11 386 37 28 112 34 69 197 325), lower := (rows 11 386 37 28 112 34 64 128 256), losses := [] }

theorem u18079 : Upper (D 6) (R 6) [10,384,33,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18080 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 451, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 386 37 28 112 36 67 195 323), lower := (rows 11 386 37 28 112 36 64 128 256), losses := [] }

theorem u18080 : Upper (D 6) (R 6) [10,384,33,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18081 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 386 37 28 112 96 71 135 263), lower := (rows 11 386 37 28 112 96 64 128 256), losses := [] }

theorem u18081 : Upper (D 6) (R 6) [10,384,33,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18082 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,6),(4,6)], upper := (rows 11 386 37 73 22 36 112 240 368), lower := (rows 11 386 37 73 22 36 64 128 256), losses := [] }

theorem u18082 : Upper (D 6) (R 6) [10,384,33,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18083 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 52, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 386 37 73 22 48 100 228 356), lower := (rows 11 386 37 73 22 48 64 128 256), losses := [] }

theorem u18083 : Upper (D 6) (R 6) [10,384,33,65,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18083 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18084 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 402, targets := 1 },{ cop := 2, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 386 37 73 22 96 116 180 308), lower := (rows 11 386 37 73 22 96 64 128 256), losses := [] }

theorem u18084 : Upper (D 6) (R 6) [10,384,33,65,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18085 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,6),(4,6)], upper := (rows 11 386 37 73 50 36 84 212 340), lower := (rows 11 386 37 73 50 36 64 128 256), losses := [] }

theorem u18085 : Upper (D 6) (R 6) [10,384,33,65,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18086 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 386 37 73 50 48 68 196 324), lower := (rows 11 386 37 73 50 48 64 128 256), losses := [] }

theorem u18086 : Upper (D 6) (R 6) [10,384,33,65,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18086 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18087 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 402, targets := 1 },{ cop := 2, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 386 37 73 50 96 84 148 276), lower := (rows 11 386 37 73 50 96 64 128 256), losses := [] }

theorem u18087 : Upper (D 6) (R 6) [10,384,33,65,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18088 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 88, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 386 37 73 112 34 84 148 276), lower := (rows 11 386 37 73 112 34 64 128 256), losses := [] }

theorem u18088 : Upper (D 6) (R 6) [10,384,33,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18089 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 386 37 73 112 36 86 150 278), lower := (rows 11 386 37 73 112 36 64 128 256), losses := [] }

theorem u18089 : Upper (D 6) (R 6) [10,384,33,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18090 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 386 37 73 112 48 70 134 262), lower := (rows 11 386 37 73 112 48 64 128 256), losses := [] }

theorem u18090 : Upper (D 6) (R 6) [10,384,33,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18090 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18091 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 386 37 76 22 33 112 240 368), lower := (rows 11 386 37 76 22 33 64 128 256), losses := [] }

theorem u18091 : Upper (D 6) (R 6) [10,384,33,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18092 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 52, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 386 37 76 22 48 97 225 353), lower := (rows 11 386 37 76 22 48 64 128 256), losses := [] }

theorem u18092 : Upper (D 6) (R 6) [10,384,33,68,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18092 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18093 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 386 37 76 22 96 113 177 305), lower := (rows 11 386 37 76 22 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 104 64 128 256), good := (rows 45 384 37 108 20 96 96 128 256) }] }

theorem u18093 : Upper (D 6) (R 6) [10,384,33,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18094 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 386 37 76 50 33 84 212 340), lower := (rows 11 386 37 76 50 33 64 128 256), losses := [] }

theorem u18094 : Upper (D 6) (R 6) [10,384,33,68,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18095 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 466, targets := 4 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 11 386 37 76 50 36 81 209 337), lower := (rows 11 386 37 76 50 36 64 128 256), losses := [] }

theorem u18095 : Upper (D 6) (R 6) [10,384,33,68,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18096 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 386 37 76 50 48 69 197 325), lower := (rows 11 386 37 76 50 48 64 128 256), losses := [] }

theorem u18096 : Upper (D 6) (R 6) [10,384,33,68,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18096 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18097 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 402, targets := 64 }], pairs := [(1,6),(4,0),(4,6)], upper := (rows 11 386 37 76 50 96 85 149 277), lower := (rows 11 386 37 76 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 104 64 128 256), good := (rows 58 386 52 108 50 96 96 128 256) }] }

theorem u18097 : Upper (D 6) (R 6) [10,384,33,68,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18098 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 88, targets := 2 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(3,1),(4,1)], upper := (rows 11 386 37 76 81 34 116 180 308), lower := (rows 11 386 37 76 81 34 64 128 256), losses := [] }

theorem u18098 : Upper (D 6) (R 6) [10,384,33,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18099 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 386 37 76 81 36 114 178 306), lower := (rows 11 386 37 76 81 36 64 128 256), losses := [] }

theorem u18099 : Upper (D 6) (R 6) [10,384,33,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18100 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 386 37 76 81 48 102 166 294), lower := (rows 11 386 37 76 81 48 64 128 256), losses := [] }

theorem u18100 : Upper (D 6) (R 6) [10,384,33,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18100 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18101 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 386 37 76 82 33 116 180 308), lower := (rows 11 386 37 76 82 33 64 128 256), losses := [] }

theorem u18101 : Upper (D 6) (R 6) [10,384,33,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18102 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 386 37 76 82 36 113 177 305), lower := (rows 11 386 37 76 82 36 64 128 256), losses := [] }

theorem u18102 : Upper (D 6) (R 6) [10,384,33,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18103 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 72, targets := 2 },{ cop := 2, region := 386, targets := 64 }], pairs := [(1,6),(3,1)], upper := (rows 11 386 37 76 82 48 101 165 293), lower := (rows 11 386 37 76 82 48 64 128 256), losses := [] }

theorem u18103 : Upper (D 6) (R 6) [10,384,33,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18103 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18104 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 386 37 76 112 33 86 150 278), lower := (rows 11 386 37 76 112 33 64 128 256), losses := [] }

theorem u18104 : Upper (D 6) (R 6) [10,384,33,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18105 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 88, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 386 37 76 112 34 85 149 277), lower := (rows 11 386 37 76 112 34 64 128 256), losses := [] }

theorem u18105 : Upper (D 6) (R 6) [10,384,33,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18106 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 386 37 76 112 36 83 147 275), lower := (rows 11 386 37 76 112 36 64 128 256), losses := [] }

theorem u18106 : Upper (D 6) (R 6) [10,384,33,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18107 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 386 37 76 112 48 71 135 263), lower := (rows 11 386 37 76 112 48 64 128 256), losses := [] }

theorem u18107 : Upper (D 6) (R 6) [10,384,33,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18107 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18108 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 386 37 88 22 33 100 228 356), lower := (rows 11 386 37 88 22 33 64 128 256), losses := [] }

theorem u18108 : Upper (D 6) (R 6) [10,384,33,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18109 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 11 386 37 88 22 36 97 225 353), lower := (rows 11 386 37 88 22 36 64 128 256), losses := [] }

theorem u18109 : Upper (D 6) (R 6) [10,384,33,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18110 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 386 37 88 22 96 101 165 293), lower := (rows 11 386 37 88 22 96 64 128 256), losses := [] }

theorem u18110 : Upper (D 6) (R 6) [10,384,33,80,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18110 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18111 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 386 37 88 50 33 68 196 324), lower := (rows 11 386 37 88 50 33 64 128 256), losses := [] }

theorem u18111 : Upper (D 6) (R 6) [10,384,33,80,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18112 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 11 386 37 88 50 36 69 197 325), lower := (rows 11 386 37 88 50 36 64 128 256), losses := [] }

theorem u18112 : Upper (D 6) (R 6) [10,384,33,80,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18112 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18113 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 386 37 88 50 96 69 133 261), lower := (rows 11 386 37 88 50 96 64 128 256), losses := [] }

theorem u18113 : Upper (D 6) (R 6) [10,384,33,80,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18114 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 386 37 104 22 33 84 212 340), lower := (rows 11 386 37 104 22 33 64 128 256), losses := [] }

theorem u18114 : Upper (D 6) (R 6) [10,384,33,96,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18115 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(4,6)], upper := (rows 11 386 37 104 22 36 81 209 337), lower := (rows 11 386 37 104 22 36 64 128 256), losses := [] }

theorem u18115 : Upper (D 6) (R 6) [10,384,33,96,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18116 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 52, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 11 386 37 104 22 48 69 197 325), lower := (rows 11 386 37 104 22 48 64 128 256), losses := [] }

theorem u18116 : Upper (D 6) (R 6) [10,384,33,96,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18116 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18117 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 386 37 104 22 96 85 149 277), lower := (rows 11 386 37 104 22 96 64 128 256), losses := [] }

theorem u18117 : Upper (D 6) (R 6) [10,384,33,96,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18118 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 386 37 104 82 33 84 148 276), lower := (rows 11 386 37 104 82 33 64 128 256), losses := [] }

theorem u18118 : Upper (D 6) (R 6) [10,384,33,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18119 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 386 37 104 82 36 85 149 277), lower := (rows 11 386 37 104 82 36 64 128 256), losses := [] }

theorem u18119 : Upper (D 6) (R 6) [10,384,33,96,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u18119
end Delivery.IrregularNine14.P06
