import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0086

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18960 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 28 104 145 33 450 386 386), lower := (rows 35 70 28 104 145 33 64 128 256), losses := [] }

theorem u18960 : Upper (D 7) (R 7) [34,68,24,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18961 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 28 104 145 34 449 385 385), lower := (rows 35 70 28 104 145 34 64 128 256), losses := [] }

theorem u18961 : Upper (D 7) (R 7) [34,68,24,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18962 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,6),(3,7),(4,5),(4,6)], upper := (rows 35 70 28 104 145 160 323 387 259), lower := (rows 35 70 28 104 145 160 64 128 256), losses := [] }

theorem u18962 : Upper (D 7) (R 7) [34,68,24,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18963 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,6),(4,5),(4,6)], upper := (rows 35 70 28 104 145 288 195 131 387), lower := (rows 35 70 28 104 145 288 64 128 256), losses := [] }

theorem u18963 : Upper (D 7) (R 7) [34,68,24,96,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18963 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18964 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 28 104 273 33 194 130 386), lower := (rows 35 70 28 104 273 33 64 128 256), losses := [] }

theorem u18964 : Upper (D 7) (R 7) [34,68,24,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18965 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 28 104 273 34 193 129 385), lower := (rows 35 70 28 104 273 34 64 128 256), losses := [] }

theorem u18965 : Upper (D 7) (R 7) [34,68,24,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18966 : Route 9 := (fun mask => (mask,id))

def c18966 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18966 : Upper (D 7) (R 7) [34,68,24,96,257,128] 13 := by
  apply FastRouting.sound _ _ [34,68,24,96,257,128] 13 (by decide) (choices 1) [1,2,128] r18966 c18966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5207
  · exact u5208
  · exact u5209

def b18967 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 28 104 400 33 195 131 387), lower := (rows 35 70 28 104 400 33 64 128 256), losses := [] }

theorem u18967 : Upper (D 7) (R 7) [34,68,24,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18968 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 28 104 400 34 193 129 385), lower := (rows 35 70 28 104 400 34 64 128 256), losses := [] }

theorem u18968 : Upper (D 7) (R 7) [34,68,24,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18969 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 72, targets := 128 }], pairs := [(0,6),(3,7),(4,5),(4,6)], upper := (rows 35 70 28 104 400 160 67 131 259), lower := (rows 35 70 28 104 400 160 64 128 256), losses := [] }

theorem u18969 : Upper (D 7) (R 7) [34,68,24,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18970 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,6)], upper := (rows 35 70 28 137 146 33 352 480 352), lower := (rows 35 70 28 137 146 33 64 128 256), losses := [] }

theorem u18970 : Upper (D 7) (R 7) [34,68,24,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18971 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 28 137 146 96 353 417 289), lower := (rows 35 70 28 137 146 96 64 128 256), losses := [] }

theorem u18971 : Upper (D 7) (R 7) [34,68,24,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18972 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,7),(1,7),(3,1)], upper := (rows 35 70 28 137 146 288 97 225 353), lower := (rows 35 70 28 137 146 288 64 128 256), losses := [] }

theorem u18972 : Upper (D 7) (R 7) [34,68,24,129,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18972 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18973 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 35 70 28 137 176 33 322 450 322), lower := (rows 35 70 28 137 176 33 64 128 256), losses := [] }

theorem u18973 : Upper (D 7) (R 7) [34,68,24,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18974 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 28 137 176 34 321 449 321), lower := (rows 35 70 28 137 176 34 64 128 256), losses := [] }

theorem u18974 : Upper (D 7) (R 7) [34,68,24,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18975 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 28 137 176 96 323 387 259), lower := (rows 35 70 28 137 176 96 64 128 256), losses := [] }

theorem u18975 : Upper (D 7) (R 7) [34,68,24,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18976 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 200, targets := 32 }], pairs := [(0,7),(1,7),(3,5)], upper := (rows 35 70 28 137 176 288 67 195 323), lower := (rows 35 70 28 137 176 288 64 128 256), losses := [] }

theorem u18976 : Upper (D 7) (R 7) [34,68,24,129,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18976 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18977 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 28 137 273 34 224 224 480), lower := (rows 35 70 28 137 273 34 64 128 256), losses := [] }

theorem u18977 : Upper (D 7) (R 7) [34,68,24,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18978 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 28 137 273 96 226 162 418), lower := (rows 35 70 28 137 273 96 64 128 256), losses := [] }

theorem u18978 : Upper (D 7) (R 7) [34,68,24,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18979 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 336, targets := 128 },{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0),(1,7),(2,7),(4,7)], upper := (rows 35 70 28 137 273 160 98 226 354), lower := (rows 35 70 28 137 273 160 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 25 32 65 0 257), good := (rows 371 70 30 351 337 32 64 0 256) }] }

theorem u18979 : Upper (D 7) (R 7) [34,68,24,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18980 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 464, targets := 1 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(0,7),(3,1),(4,0)], upper := (rows 35 70 28 137 274 33 224 224 480), lower := (rows 35 70 28 137 274 33 64 128 256), losses := [] }

theorem u18980 : Upper (D 7) (R 7) [34,68,24,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18981 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 136, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 28 137 274 96 225 161 417), lower := (rows 35 70 28 137 274 96 64 128 256), losses := [] }

theorem u18981 : Upper (D 7) (R 7) [34,68,24,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18982 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 200, targets := 2 },{ cop := 0, region := 336, targets := 128 }], pairs := [(1,7),(2,7),(3,1),(4,7)], upper := (rows 35 70 28 137 274 160 97 225 353), lower := (rows 35 70 28 137 274 160 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 25 32 65 0 257), good := (rows 371 70 30 351 274 32 64 0 256) }] }

theorem u18982 : Upper (D 7) (R 7) [34,68,24,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18983 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 194, targets := 33 }], pairs := [(0,6),(0,7),(1,0),(1,5)], upper := (rows 35 70 28 137 304 33 194 194 450), lower := (rows 35 70 28 137 304 33 64 128 256), losses := [] }

theorem u18983 : Upper (D 7) (R 7) [34,68,24,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18984 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 28 137 304 34 193 193 449), lower := (rows 35 70 28 137 304 34 64 128 256), losses := [] }

theorem u18984 : Upper (D 7) (R 7) [34,68,24,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18985 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 136, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 28 137 304 96 195 131 387), lower := (rows 35 70 28 137 304 96 64 128 256), losses := [] }

theorem u18985 : Upper (D 7) (R 7) [34,68,24,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18986 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 200, targets := 32 },{ cop := 0, region := 336, targets := 128 }], pairs := [(1,7),(2,7),(3,5),(4,7)], upper := (rows 35 70 28 137 304 160 67 195 323), lower := (rows 35 70 28 137 304 160 64 128 256), losses := [{ target := 7, region := (rows 1 14 12 8 17 32 73 0 265), good := (rows 371 70 350 351 304 32 64 0 256) }] }

theorem u18986 : Upper (D 7) (R 7) [34,68,24,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18987 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 169, targets := 64 },{ cop := 0, region := 464, targets := 1 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,6),(4,0)], upper := (rows 35 70 28 137 336 33 226 162 418), lower := (rows 35 70 28 137 336 33 64 128 256), losses := [] }

theorem u18987 : Upper (D 7) (R 7) [34,68,24,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18988 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 28 137 336 34 225 161 417), lower := (rows 35 70 28 137 336 34 64 128 256), losses := [] }

theorem u18988 : Upper (D 7) (R 7) [34,68,24,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18989 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 169, targets := 64 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(1,7),(3,6),(4,7)], upper := (rows 35 70 28 137 336 160 99 163 291), lower := (rows 35 70 28 137 336 160 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 25 32 65 0 257), good := (rows 371 70 30 351 336 32 64 0 256) }] }

theorem u18989 : Upper (D 7) (R 7) [34,68,24,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18990 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 464, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,0)], upper := (rows 35 70 28 137 400 33 98 226 354), lower := (rows 35 70 28 137 400 33 64 128 256), losses := [] }

theorem u18990 : Upper (D 7) (R 7) [34,68,24,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18991 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 28 137 400 34 97 225 353), lower := (rows 35 70 28 137 400 34 64 128 256), losses := [] }

theorem u18991 : Upper (D 7) (R 7) [34,68,24,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18992 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 28 137 400 96 99 163 291), lower := (rows 35 70 28 137 400 96 64 128 256), losses := [] }

theorem u18992 : Upper (D 7) (R 7) [34,68,24,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18993 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 200, targets := 1 },{ cop := 0, region := 464, targets := 2 }], pairs := [(0,6),(0,7),(3,0),(4,1)], upper := (rows 35 70 28 138 273 33 224 224 480), lower := (rows 35 70 28 138 273 33 64 128 256), losses := [] }

theorem u18993 : Upper (D 7) (R 7) [34,68,24,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18994 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 28 138 273 96 225 161 417), lower := (rows 35 70 28 138 273 96 64 128 256), losses := [] }

theorem u18994 : Upper (D 7) (R 7) [34,68,24,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18995 : Route 9 := (fun mask => (mask,id))

def c18995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18995 : Upper (D 7) (R 7) [34,68,24,130,257,128] 13 := by
  apply FastRouting.sound _ _ [34,68,24,130,257,128] 13 (by decide) (choices 1) [1,32] r18995 c18995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5210
  · exact u5211

def b18996 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 464, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(0,6),(0,7),(3,5),(4,1)], upper := (rows 35 70 28 138 304 33 193 193 449), lower := (rows 35 70 28 138 304 33 64 128 256), losses := [] }

theorem u18996 : Upper (D 7) (R 7) [34,68,24,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18997 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 28 138 304 96 193 129 385), lower := (rows 35 70 28 138 304 96 64 128 256), losses := [] }

theorem u18997 : Upper (D 7) (R 7) [34,68,24,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18998 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 2 },{ cop := 0, region := 200, targets := 32 },{ cop := 0, region := 336, targets := 128 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(3,5),(4,1),(4,7)], upper := (rows 35 70 28 138 304 160 65 193 321), lower := (rows 35 70 28 138 304 160 64 128 256), losses := [] }

theorem u18998 : Upper (D 7) (R 7) [34,68,24,130,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18999 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 169, targets := 64 },{ cop := 0, region := 464, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,6),(4,1)], upper := (rows 35 70 28 138 336 33 225 161 417), lower := (rows 35 70 28 138 336 33 64 128 256), losses := [] }

theorem u18999 : Upper (D 7) (R 7) [34,68,24,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19000 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 169, targets := 64 },{ cop := 0, region := 336, targets := 2 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,6),(3,6),(4,1),(4,7)], upper := (rows 35 70 28 138 336 160 97 161 289), lower := (rows 35 70 28 138 336 160 64 128 256), losses := [] }

theorem u19000 : Upper (D 7) (R 7) [34,68,24,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19001 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 464, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,1)], upper := (rows 35 70 28 138 400 33 97 225 353), lower := (rows 35 70 28 138 400 33 64 128 256), losses := [] }

theorem u19001 : Upper (D 7) (R 7) [34,68,24,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19002 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 28 138 400 96 97 161 289), lower := (rows 35 70 28 138 400 96 64 128 256), losses := [] }

theorem u19002 : Upper (D 7) (R 7) [34,68,24,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19003 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 194, targets := 33 }], pairs := [(0,6),(0,7),(1,0),(1,5)], upper := (rows 35 70 28 168 273 33 194 194 450), lower := (rows 35 70 28 168 273 33 64 128 256), losses := [] }

theorem u19003 : Upper (D 7) (R 7) [34,68,24,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19004 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 28 168 273 34 193 193 449), lower := (rows 35 70 28 168 273 34 64 128 256), losses := [] }

theorem u19004 : Upper (D 7) (R 7) [34,68,24,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19005 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 32 }], pairs := [(2,6),(3,6),(4,5),(4,6)], upper := (rows 35 70 28 168 273 96 195 131 387), lower := (rows 35 70 28 168 273 96 64 128 256), losses := [] }

theorem u19005 : Upper (D 7) (R 7) [34,68,24,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19006 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 70 28 168 273 160 67 195 323), lower := (rows 35 70 28 168 273 160 64 128 256), losses := [] }

theorem u19006 : Upper (D 7) (R 7) [34,68,24,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19007 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 200, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(0,7),(3,1),(4,5)], upper := (rows 35 70 28 168 274 33 193 193 449), lower := (rows 35 70 28 168 274 33 64 128 256), losses := [] }

theorem u19007 : Upper (D 7) (R 7) [34,68,24,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19008 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 136, targets := 2 }], pairs := [(2,6),(3,1),(3,6),(4,6)], upper := (rows 35 70 28 168 274 96 193 129 385), lower := (rows 35 70 28 168 274 96 64 128 256), losses := [] }

theorem u19008 : Upper (D 7) (R 7) [34,68,24,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19009 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 70 28 168 274 160 65 193 321), lower := (rows 35 70 28 168 274 160 64 128 256), losses := [] }

theorem u19009 : Upper (D 7) (R 7) [34,68,24,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19010 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 169, targets := 64 },{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,6),(4,5)], upper := (rows 35 70 28 168 336 33 195 131 387), lower := (rows 35 70 28 168 336 33 64 128 256), losses := [] }

theorem u19010 : Upper (D 7) (R 7) [34,68,24,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19011 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 28 168 336 34 193 129 385), lower := (rows 35 70 28 168 336 34 64 128 256), losses := [] }

theorem u19011 : Upper (D 7) (R 7) [34,68,24,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19012 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 70 28 168 336 160 67 131 259), lower := (rows 35 70 28 168 336 160 64 128 256), losses := [] }

theorem u19012 : Upper (D 7) (R 7) [34,68,24,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19013 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,5)], upper := (rows 35 70 28 168 400 33 67 195 323), lower := (rows 35 70 28 168 400 33 64 128 256), losses := [] }

theorem u19013 : Upper (D 7) (R 7) [34,68,24,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19014 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 28 168 400 34 65 193 321), lower := (rows 35 70 28 168 400 34 64 128 256), losses := [] }

theorem u19014 : Upper (D 7) (R 7) [34,68,24,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19015 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 28 168 400 96 67 131 259), lower := (rows 35 70 28 168 400 96 64 128 256), losses := [] }

theorem u19015 : Upper (D 7) (R 7) [34,68,24,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19016 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 200, targets := 1 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,0),(4,6)], upper := (rows 35 70 28 200 273 33 226 162 418), lower := (rows 35 70 28 200 273 33 64 128 256), losses := [] }

theorem u19016 : Upper (D 7) (R 7) [34,68,24,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19017 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 28 200 273 34 225 161 417), lower := (rows 35 70 28 200 273 34 64 128 256), losses := [] }

theorem u19017 : Upper (D 7) (R 7) [34,68,24,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19018 : Route 9 := (fun mask => (mask,id))

def c19018 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19018 : Upper (D 7) (R 7) [34,68,24,192,257,128] 13 := by
  apply FastRouting.sound _ _ [34,68,24,192,257,128] 13 (by decide) (choices 1) [1,2,32] r19018 c19018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5212
  · exact u5213
  · exact u5214

def b19019 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 200, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,1),(4,6)], upper := (rows 35 70 28 200 274 33 225 161 417), lower := (rows 35 70 28 200 274 33 64 128 256), losses := [] }

theorem u19019 : Upper (D 7) (R 7) [34,68,24,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u19019
end Delivery.IrregularNine14.P07
