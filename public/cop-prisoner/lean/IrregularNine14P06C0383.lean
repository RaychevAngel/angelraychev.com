import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0117

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22980 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 76 13 112 48 323 387 259), lower := (rows 35 134 76 13 112 48 64 128 256), losses := [] }

theorem u22980 : Upper (D 6) (R 6) [34,132,72,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22980 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22981 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 369, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 134 76 13 112 288 83 147 275), lower := (rows 35 134 76 13 112 288 64 128 256), losses := [] }

theorem u22981 : Upper (D 6) (R 6) [34,132,72,5,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22981 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22982 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 13 273 34 112 240 368), lower := (rows 35 134 76 13 273 34 64 128 256), losses := [] }

theorem u22982 : Upper (D 6) (R 6) [34,132,72,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22983 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 369, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 134 76 13 273 48 98 226 354), lower := (rows 35 134 76 13 273 48 64 128 256), losses := [] }

theorem u22983 : Upper (D 6) (R 6) [34,132,72,5,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22983 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22984 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 0, region := 272, targets := 64 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 134 76 13 273 96 114 178 306), lower := (rows 35 134 76 13 273 96 64 128 256), losses := [] }

theorem u22984 : Upper (D 6) (R 6) [34,132,72,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22985 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 76 13 274 33 112 240 368), lower := (rows 35 134 76 13 274 33 64 128 256), losses := [] }

theorem u22985 : Upper (D 6) (R 6) [34,132,72,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22986 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 76 13 274 48 97 225 353), lower := (rows 35 134 76 13 274 48 64 128 256), losses := [] }

theorem u22986 : Upper (D 6) (R 6) [34,132,72,5,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22986 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22987 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 0, region := 272, targets := 64 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 134 76 13 274 96 113 177 305), lower := (rows 35 134 76 13 274 96 64 128 256), losses := [] }

theorem u22987 : Upper (D 6) (R 6) [34,132,72,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22988 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 76 13 304 33 82 210 338), lower := (rows 35 134 76 13 304 33 64 128 256), losses := [] }

theorem u22988 : Upper (D 6) (R 6) [34,132,72,5,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22989 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 13 304 34 81 209 337), lower := (rows 35 134 76 13 304 34 64 128 256), losses := [] }

theorem u22989 : Upper (D 6) (R 6) [34,132,72,5,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22990 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 134 76 13 304 48 67 195 323), lower := (rows 35 134 76 13 304 48 64 128 256), losses := [] }

theorem u22990 : Upper (D 6) (R 6) [34,132,72,5,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22990 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22991 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 0, region := 272, targets := 64 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 134 76 13 304 96 83 147 275), lower := (rows 35 134 76 13 304 96 64 128 256), losses := [] }

theorem u22991 : Upper (D 6) (R 6) [34,132,72,5,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22992 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 76 13 336 33 114 178 306), lower := (rows 35 134 76 13 336 33 64 128 256), losses := [] }

theorem u22992 : Upper (D 6) (R 6) [34,132,72,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22993 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 13 336 34 113 177 305), lower := (rows 35 134 76 13 336 34 64 128 256), losses := [] }

theorem u22993 : Upper (D 6) (R 6) [34,132,72,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22994 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 369, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 134 76 13 336 48 99 163 291), lower := (rows 35 134 76 13 336 48 64 128 256), losses := [] }

theorem u22994 : Upper (D 6) (R 6) [34,132,72,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22994 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22995 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 76 25 274 33 100 228 356), lower := (rows 35 134 76 25 274 33 64 128 256), losses := [] }

theorem u22995 : Upper (D 6) (R 6) [34,132,72,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22996 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 76 25 274 36 97 225 353), lower := (rows 35 134 76 25 274 36 64 128 256), losses := [] }

theorem u22996 : Upper (D 6) (R 6) [34,132,72,17,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22997 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 100, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 35 134 76 25 274 96 101 165 293), lower := (rows 35 134 76 25 274 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 24 16 100 64 128 256), good := (rows 35 163 104 25 283 96 96 128 256) }] }

theorem u22997 : Upper (D 6) (R 6) [34,132,72,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22998 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 76 25 276 33 98 226 354), lower := (rows 35 134 76 25 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 24 32 65 129 257), good := (rows 482 134 94 478 276 480 64 128 256) }] }

theorem u22998 : Upper (D 6) (R 6) [34,132,72,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22999 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 25 276 34 97 225 353), lower := (rows 35 134 76 25 276 34 64 128 256), losses := [] }

theorem u22999 : Upper (D 6) (R 6) [34,132,72,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23000 : Route 9 := (fun mask => (mask,id))

def c23000 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23000 : Upper (D 6) (R 6) [34,132,72,17,260,64] 13 := by
  apply FastRouting.sound _ _ [34,132,72,17,260,64] 13 (by decide) (choices 1) [1,2,32] r23000 c23000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7046
  · exact u7047
  · exact u7048

def b23001 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 134 76 25 304 33 70 198 326), lower := (rows 35 134 76 25 304 33 64 128 256), losses := [] }

theorem u23001 : Upper (D 6) (R 6) [34,132,72,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23002 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 25 304 34 69 197 325), lower := (rows 35 134 76 25 304 34 64 128 256), losses := [] }

theorem u23002 : Upper (D 6) (R 6) [34,132,72,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23003 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(3,2),(4,2)], upper := (rows 35 134 76 25 304 36 67 195 323), lower := (rows 35 134 76 25 304 36 64 128 256), losses := [] }

theorem u23003 : Upper (D 6) (R 6) [34,132,72,17,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23004 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 134 76 25 304 96 71 135 263), lower := (rows 35 134 76 25 304 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 100 64 128 256), good := (rows 35 163 104 25 304 96 96 128 256) }] }

theorem u23004 : Upper (D 6) (R 6) [34,132,72,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23005 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 76 25 336 33 102 166 294), lower := (rows 35 134 76 25 336 33 64 128 256), losses := [] }

theorem u23005 : Upper (D 6) (R 6) [34,132,72,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23006 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 25 336 34 101 165 293), lower := (rows 35 134 76 25 336 34 64 128 256), losses := [] }

theorem u23006 : Upper (D 6) (R 6) [34,132,72,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23007 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 76 25 336 36 99 163 291), lower := (rows 35 134 76 25 336 36 64 128 256), losses := [] }

theorem u23007 : Upper (D 6) (R 6) [34,132,72,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23008 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 134 76 26 21 33 352 480 352), lower := (rows 35 134 76 26 21 33 64 128 256), losses := [] }

theorem u23008 : Upper (D 6) (R 6) [34,132,72,18,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23009 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 353, targets := 4 }], pairs := [(0,2),(1,6),(2,1)], upper := (rows 35 134 76 26 21 96 353 417 289), lower := (rows 35 134 76 26 21 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 125 81 145 273), good := (rows 481 164 108 508 501 96 96 128 256) },{ target := 6, region := (rows 1 18 4 24 16 32 0 129 257), good := (rows 419 134 12 26 415 32 0 128 256) }] }

theorem u23009 : Upper (D 6) (R 6) [34,132,72,18,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23010 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 353, targets := 4 }], pairs := [(0,2),(2,1)], upper := (rows 35 134 76 26 21 288 97 225 353), lower := (rows 35 134 76 26 21 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 313 81 145 273), good := (rows 481 132 108 508 501 288 64 128 288) }] }

theorem u23010 : Upper (D 6) (R 6) [34,132,72,18,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23010 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23011 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 134 76 26 52 33 321 449 321), lower := (rows 35 134 76 26 52 33 64 128 256), losses := [] }

theorem u23011 : Upper (D 6) (R 6) [34,132,72,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23012 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 134 76 26 52 96 321 385 257), lower := (rows 35 134 76 26 52 96 64 128 256), losses := [] }

theorem u23012 : Upper (D 6) (R 6) [34,132,72,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23013 : Route 9 := (fun mask => (mask,id))

def c23013 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23013 : Upper (D 6) (R 6) [34,132,72,18,36,256] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,36,256] 13 (by decide) (choices 1) [1] r23013 c23013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u7049

def b23014 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 76 26 81 33 356 420 292), lower := (rows 35 134 76 26 81 33 64 128 256), losses := [] }

theorem u23014 : Upper (D 6) (R 6) [34,132,72,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23015 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 76 26 81 36 353 417 289), lower := (rows 35 134 76 26 81 36 64 128 256), losses := [] }

theorem u23015 : Upper (D 6) (R 6) [34,132,72,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23016 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 76 26 81 288 101 165 293), lower := (rows 35 134 76 26 81 288 64 128 256), losses := [] }

theorem u23016 : Upper (D 6) (R 6) [34,132,72,18,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23016 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23017 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 76 26 112 33 325 389 261), lower := (rows 35 134 76 26 112 33 64 128 256), losses := [] }

theorem u23017 : Upper (D 6) (R 6) [34,132,72,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23018 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 35 134 76 26 112 36 321 385 257), lower := (rows 35 134 76 26 112 36 64 128 256), losses := [] }

theorem u23018 : Upper (D 6) (R 6) [34,132,72,18,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23019 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 76 26 112 288 69 133 261), lower := (rows 35 134 76 26 112 288 64 128 256), losses := [] }

theorem u23019 : Upper (D 6) (R 6) [34,132,72,18,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23019 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23020 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 134 76 26 273 33 100 228 356), lower := (rows 35 134 76 26 273 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 72 136 264), good := (rows 33 132 460 508 305 33 64 128 256) }] }

theorem u23020 : Upper (D 6) (R 6) [34,132,72,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23021 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 336, targets := 2 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 35 134 76 26 273 36 97 225 353), lower := (rows 35 134 76 26 273 36 64 128 256), losses := [] }

theorem u23021 : Upper (D 6) (R 6) [34,132,72,18,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23022 : Route 9 := (fun mask => (mask,id))

def c23022 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23022 : Upper (D 6) (R 6) [34,132,72,18,257,64] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,257,64] 13 (by decide) (choices 1) [1,4,32] r23022 c23022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7050
  · exact u7051
  · exact u7052

def r23023 : Route 9 := (fun mask => (mask,id))

def c23023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23023 : Upper (D 6) (R 6) [34,132,72,18,260,1] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,260,1] 13 (by decide) (choices 1) [1,32] r23023 c23023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7053
  · exact u7054

def r23024 : Route 9 := (fun mask => (mask,id))

def c23024 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23024 : Upper (D 6) (R 6) [34,132,72,18,260,64] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,260,64] 13 (by decide) (choices 1) [1,32] r23024 c23024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7055
  · exact u7056

def r23025 : Route 9 := (fun mask => (mask,id))

def c23025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23025 : Upper (D 6) (R 6) [34,132,72,18,288,1] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,288,1] 13 (by decide) (choices 1) [1,4] r23025 c23025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7057
  · exact u7058

def b23026 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 336, targets := 2 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 35 134 76 26 304 36 65 193 321), lower := (rows 35 134 76 26 304 36 64 128 256), losses := [] }

theorem u23026 : Upper (D 6) (R 6) [34,132,72,18,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23027 : Route 9 := (fun mask => (mask,id))

def c23027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23027 : Upper (D 6) (R 6) [34,132,72,18,288,64] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18,288,64] 13 (by decide) (choices 1) [1,4] r23027 c23027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7059
  · exact u7060

def b23028 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 76 26 336 33 101 165 293), lower := (rows 35 134 76 26 336 33 64 128 256), losses := [] }

theorem u23028 : Upper (D 6) (R 6) [34,132,72,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23029 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 76 26 336 36 97 161 289), lower := (rows 35 134 76 26 336 36 64 128 256), losses := [] }

theorem u23029 : Upper (D 6) (R 6) [34,132,72,18,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23030 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 76 28 273 33 98 226 354), lower := (rows 35 134 76 28 273 33 64 128 256), losses := [] }

theorem u23030 : Upper (D 6) (R 6) [34,132,72,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23031 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 28 273 34 97 225 353), lower := (rows 35 134 76 28 273 34 64 128 256), losses := [] }

theorem u23031 : Upper (D 6) (R 6) [34,132,72,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23032 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 0, region := 272, targets := 64 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 134 76 28 273 96 99 163 291), lower := (rows 35 134 76 28 273 96 64 128 256), losses := [] }

theorem u23032 : Upper (D 6) (R 6) [34,132,72,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23033 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 76 28 274 33 97 225 353), lower := (rows 35 134 76 28 274 33 64 128 256), losses := [] }

theorem u23033 : Upper (D 6) (R 6) [34,132,72,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23034 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 0, region := 272, targets := 64 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 134 76 28 274 96 97 161 289), lower := (rows 35 134 76 28 274 96 64 128 256), losses := [] }

theorem u23034 : Upper (D 6) (R 6) [34,132,72,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23035 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 76 28 304 33 67 195 323), lower := (rows 35 134 76 28 304 33 64 128 256), losses := [] }

theorem u23035 : Upper (D 6) (R 6) [34,132,72,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23036 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 28 304 34 65 193 321), lower := (rows 35 134 76 28 304 34 64 128 256), losses := [] }

theorem u23036 : Upper (D 6) (R 6) [34,132,72,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23037 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 0, region := 272, targets := 64 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 134 76 28 304 96 67 131 259), lower := (rows 35 134 76 28 304 96 64 128 256), losses := [] }

theorem u23037 : Upper (D 6) (R 6) [34,132,72,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23038 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 134 76 56 81 33 326 390 262), lower := (rows 35 134 76 56 81 33 64 128 256), losses := [] }

theorem u23038 : Upper (D 6) (R 6) [34,132,72,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23039 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 76 56 81 34 325 389 261), lower := (rows 35 134 76 56 81 34 64 128 256), losses := [] }

theorem u23039 : Upper (D 6) (R 6) [34,132,72,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u23039
end Delivery.IrregularNine14.P06
