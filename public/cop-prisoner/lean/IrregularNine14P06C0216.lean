import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0043

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12960 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 28 112 34 69 197 325), lower := (rows 11 35 388 28 112 34 64 128 256), losses := [] }

theorem u12960 : Upper (D 6) (R 6) [10,33,384,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12961 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 452, targets := 32 }], pairs := [(0,6),(1,6),(2,5)], upper := (rows 11 35 388 28 112 36 67 195 323), lower := (rows 11 35 388 28 112 36 64 128 256), losses := [] }

theorem u12961 : Upper (D 6) (R 6) [10,33,384,20,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12962 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 388 28 112 96 71 135 263), lower := (rows 11 35 388 28 112 96 64 128 256), losses := [] }

theorem u12962 : Upper (D 6) (R 6) [10,33,384,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12963 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 73 52 34 84 212 340), lower := (rows 11 35 388 73 52 34 64 128 256), losses := [] }

theorem u12963 : Upper (D 6) (R 6) [10,33,384,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12964 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 35 388 73 52 36 82 210 338), lower := (rows 11 35 388 73 52 36 64 128 256), losses := [] }

theorem u12964 : Upper (D 6) (R 6) [10,33,384,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12965 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 388 73 52 48 70 198 326), lower := (rows 11 35 388 73 52 48 64 128 256), losses := [] }

theorem u12965 : Upper (D 6) (R 6) [10,33,384,65,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12965 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12966 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 388 73 52 96 86 150 278), lower := (rows 11 35 388 73 52 96 64 128 256), losses := [] }

theorem u12966 : Upper (D 6) (R 6) [10,33,384,65,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12967 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 73 84 34 116 180 308), lower := (rows 11 35 388 73 84 34 64 128 256), losses := [] }

theorem u12967 : Upper (D 6) (R 6) [10,33,384,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12968 : Route 9 := (fun mask => (mask,id))

def c12968 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12968 : Upper (D 6) (R 6) [10,33,384,65,68,4] 13 := by
  apply FastRouting.sound _ _ [10,33,384,65,68,4] 13 (by decide) (choices 1) [2,16,32] r12968 c12968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2598
  · exact u2599
  · exact u2600

def b12969 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 388 73 84 48 102 166 294), lower := (rows 11 35 388 73 84 48 64 128 256), losses := [] }

theorem u12969 : Upper (D 6) (R 6) [10,33,384,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12969 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12970 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 388 76 21 34 112 240 368), lower := (rows 11 35 388 76 21 34 64 128 256), losses := [] }

theorem u12970 : Upper (D 6) (R 6) [10,33,384,68,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12971 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 388 76 21 48 98 226 354), lower := (rows 11 35 388 76 21 48 64 128 256), losses := [] }

theorem u12971 : Upper (D 6) (R 6) [10,33,384,68,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12971 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12972 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 388 76 21 96 114 178 306), lower := (rows 11 35 388 76 21 96 64 128 256), losses := [] }

theorem u12972 : Upper (D 6) (R 6) [10,33,384,68,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12973 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 388 76 22 33 112 240 368), lower := (rows 11 35 388 76 22 33 64 128 256), losses := [] }

theorem u12973 : Upper (D 6) (R 6) [10,33,384,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12974 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 388 76 22 48 97 225 353), lower := (rows 11 35 388 76 22 48 64 128 256), losses := [] }

theorem u12974 : Upper (D 6) (R 6) [10,33,384,68,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12974 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12975 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 388 76 22 96 113 177 305), lower := (rows 11 35 388 76 22 96 64 128 256), losses := [] }

theorem u12975 : Upper (D 6) (R 6) [10,33,384,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12976 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 388 76 52 33 82 210 338), lower := (rows 11 35 388 76 52 33 64 128 256), losses := [] }

theorem u12976 : Upper (D 6) (R 6) [10,33,384,68,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12977 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 388 76 52 34 81 209 337), lower := (rows 11 35 388 76 52 34 64 128 256), losses := [] }

theorem u12977 : Upper (D 6) (R 6) [10,33,384,68,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12978 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 388 76 52 48 67 195 323), lower := (rows 11 35 388 76 52 48 64 128 256), losses := [] }

theorem u12978 : Upper (D 6) (R 6) [10,33,384,68,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12978 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12979 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 48, targets := 1 }], pairs := [(2,6),(4,0),(4,6)], upper := (rows 11 35 388 76 52 96 83 147 275), lower := (rows 11 35 388 76 52 96 64 128 256), losses := [] }

theorem u12979 : Upper (D 6) (R 6) [10,33,384,68,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12980 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 388 76 81 34 116 180 308), lower := (rows 11 35 388 76 81 34 64 128 256), losses := [] }

theorem u12980 : Upper (D 6) (R 6) [10,33,384,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12981 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 80, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 388 76 81 36 114 178 306), lower := (rows 11 35 388 76 81 36 64 128 256), losses := [] }

theorem u12981 : Upper (D 6) (R 6) [10,33,384,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12982 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 388 76 81 48 102 166 294), lower := (rows 11 35 388 76 81 48 64 128 256), losses := [] }

theorem u12982 : Upper (D 6) (R 6) [10,33,384,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12982 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12983 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 388 76 82 33 116 180 308), lower := (rows 11 35 388 76 82 33 64 128 256), losses := [] }

theorem u12983 : Upper (D 6) (R 6) [10,33,384,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12984 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 80, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 388 76 82 36 113 177 305), lower := (rows 11 35 388 76 82 36 64 128 256), losses := [] }

theorem u12984 : Upper (D 6) (R 6) [10,33,384,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12985 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 388 76 82 48 101 165 293), lower := (rows 11 35 388 76 82 48 64 128 256), losses := [] }

theorem u12985 : Upper (D 6) (R 6) [10,33,384,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12985 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12986 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 388 76 112 33 86 150 278), lower := (rows 11 35 388 76 112 33 64 128 256), losses := [] }

theorem u12986 : Upper (D 6) (R 6) [10,33,384,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12987 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 388 76 112 34 85 149 277), lower := (rows 11 35 388 76 112 34 64 128 256), losses := [] }

theorem u12987 : Upper (D 6) (R 6) [10,33,384,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12988 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 11 35 388 76 112 36 83 147 275), lower := (rows 11 35 388 76 112 36 64 128 256), losses := [] }

theorem u12988 : Upper (D 6) (R 6) [10,33,384,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12989 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 35 388 76 112 48 71 135 263), lower := (rows 11 35 388 76 112 48 64 128 256), losses := [] }

theorem u12989 : Upper (D 6) (R 6) [10,33,384,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12989 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12990 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 88 21 34 100 228 356), lower := (rows 11 35 388 88 21 34 64 128 256), losses := [] }

theorem u12990 : Upper (D 6) (R 6) [10,33,384,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12991 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 484, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 11 35 388 88 21 36 98 226 354), lower := (rows 11 35 388 88 21 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 23 24 16 63 67 131 259), good := (rows 494 486 420 124 508 36 64 128 256) }] }

theorem u12991 : Upper (D 6) (R 6) [10,33,384,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12992 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 388 88 21 96 102 166 294), lower := (rows 11 35 388 88 21 96 64 128 256), losses := [] }

theorem u12992 : Upper (D 6) (R 6) [10,33,384,80,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12993 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 88 22 33 100 228 356), lower := (rows 11 35 388 88 22 33 64 128 256), losses := [] }

theorem u12993 : Upper (D 6) (R 6) [10,33,384,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12994 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(0,2),(2,1),(3,1)], upper := (rows 11 35 388 88 22 36 97 225 353), lower := (rows 11 35 388 88 22 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 63 67 131 259), good := (rows 493 485 420 124 508 36 64 128 256) },{ target := 2, region := (rows 17 2 0 24 16 32 66 130 258), good := (rows 459 483 384 89 475 32 64 128 256) }] }

theorem u12994 : Upper (D 6) (R 6) [10,33,384,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12995 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 388 88 22 96 101 165 293), lower := (rows 11 35 388 88 22 96 64 128 256), losses := [] }

theorem u12995 : Upper (D 6) (R 6) [10,33,384,80,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12996 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 88 52 33 70 198 326), lower := (rows 11 35 388 88 52 33 64 128 256), losses := [] }

theorem u12996 : Upper (D 6) (R 6) [10,33,384,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12997 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 388 88 52 34 69 197 325), lower := (rows 11 35 388 88 52 34 64 128 256), losses := [] }

theorem u12997 : Upper (D 6) (R 6) [10,33,384,80,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12998 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 35 388 88 52 36 67 195 323), lower := (rows 11 35 388 88 52 36 64 128 256), losses := [] }

theorem u12998 : Upper (D 6) (R 6) [10,33,384,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12999 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 388 88 52 96 71 135 263), lower := (rows 11 35 388 88 52 96 64 128 256), losses := [] }

theorem u12999 : Upper (D 6) (R 6) [10,33,384,80,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13000 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 69 25 148 34 352 480 352), lower := (rows 11 38 69 25 148 34 64 128 256), losses := [] }

theorem u13000 : Upper (D 6) (R 6) [10,36,65,17,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13001 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 25 148 96 354 418 290), lower := (rows 11 38 69 25 148 96 64 128 256), losses := [] }

theorem u13001 : Upper (D 6) (R 6) [10,36,65,17,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13002 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 434, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 38 69 25 148 288 98 226 354), lower := (rows 11 38 69 25 148 288 64 128 256), losses := [] }

theorem u13002 : Upper (D 6) (R 6) [10,36,65,17,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13002 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13003 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 1, region := 464, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 69 25 400 34 100 228 356), lower := (rows 11 38 69 25 400 34 64 128 256), losses := [] }

theorem u13003 : Upper (D 6) (R 6) [10,36,65,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13004 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 69 25 400 36 98 226 354), lower := (rows 11 38 69 25 400 36 64 128 256), losses := [] }

theorem u13004 : Upper (D 6) (R 6) [10,36,65,17,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13004 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13005 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 25 400 96 102 166 294), lower := (rows 11 38 69 25 400 96 64 128 256), losses := [] }

theorem u13005 : Upper (D 6) (R 6) [10,36,65,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13006 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 496, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 69 28 145 34 352 480 352), lower := (rows 11 38 69 28 145 34 64 128 256), losses := [] }

theorem u13006 : Upper (D 6) (R 6) [10,36,65,20,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13007 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 28 145 96 354 418 290), lower := (rows 11 38 69 28 145 96 64 128 256), losses := [] }

theorem u13007 : Upper (D 6) (R 6) [10,36,65,20,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13008 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 496, targets := 4 },{ cop := 2, region := 290, targets := 1 }], pairs := [(1,0),(4,2)], upper := (rows 11 38 69 28 145 288 98 226 354), lower := (rows 11 38 69 28 145 288 64 128 256), losses := [] }

theorem u13008 : Upper (D 6) (R 6) [10,36,65,20,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13008 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13009 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 69 28 146 33 352 480 352), lower := (rows 11 38 69 28 146 33 64 128 256), losses := [] }

theorem u13009 : Upper (D 6) (R 6) [10,36,65,20,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13010 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 28 146 96 353 417 289), lower := (rows 11 38 69 28 146 96 64 128 256), losses := [] }

theorem u13010 : Upper (D 6) (R 6) [10,36,65,20,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13011 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 0, region := 496, targets := 4 }], pairs := [(2,1),(4,2)], upper := (rows 11 38 69 28 146 288 97 225 353), lower := (rows 11 38 69 28 146 288 64 128 256), losses := [] }

theorem u13011 : Upper (D 6) (R 6) [10,36,65,20,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13011 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13012 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 69 28 176 33 322 450 322), lower := (rows 11 38 69 28 176 33 64 128 256), losses := [] }

theorem u13012 : Upper (D 6) (R 6) [10,36,65,20,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13012 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13013 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 324, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 38 69 28 176 34 321 449 321), lower := (rows 11 38 69 28 176 34 64 128 256), losses := [] }

theorem u13013 : Upper (D 6) (R 6) [10,36,65,20,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13014 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 28 176 96 323 387 259), lower := (rows 11 38 69 28 176 96 64 128 256), losses := [] }

theorem u13014 : Upper (D 6) (R 6) [10,36,65,20,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13015 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 496, targets := 4 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(4,2)], upper := (rows 11 38 69 28 176 288 67 195 323), lower := (rows 11 38 69 28 176 288 64 128 256), losses := [] }

theorem u13015 : Upper (D 6) (R 6) [10,36,65,20,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13015 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13016 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 69 28 400 33 98 226 354), lower := (rows 11 38 69 28 400 33 64 128 256), losses := [] }

theorem u13016 : Upper (D 6) (R 6) [10,36,65,20,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13017 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 496, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 69 28 400 34 97 225 353), lower := (rows 11 38 69 28 400 34 64 128 256), losses := [] }

theorem u13017 : Upper (D 6) (R 6) [10,36,65,20,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13017 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13018 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 69 28 400 96 99 163 291), lower := (rows 11 38 69 28 400 96 64 128 256), losses := [] }

theorem u13018 : Upper (D 6) (R 6) [10,36,65,20,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13019 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 69 56 148 33 322 450 322), lower := (rows 11 38 69 56 148 33 64 128 256), losses := [] }

theorem u13019 : Upper (D 6) (R 6) [10,36,65,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13019
end Delivery.IrregularNine14.P06
