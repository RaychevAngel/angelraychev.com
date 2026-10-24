import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0129

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24960 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 262 44 81 40 85 149 277), lower := (rows 35 194 262 44 81 40 64 128 256), losses := [] }

theorem u24960 : Upper (D 6) (R 6) [34,192,258,36,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24960 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24961 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 262 44 81 48 77 141 269), lower := (rows 35 194 262 44 81 48 64 128 256), losses := [] }

theorem u24961 : Upper (D 6) (R 6) [34,192,258,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24961 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24962 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 194 262 44 84 33 89 153 281), lower := (rows 35 194 262 44 84 33 64 128 256), losses := [] }

theorem u24962 : Upper (D 6) (R 6) [34,192,258,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24963 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 262 44 84 40 81 145 273), lower := (rows 35 194 262 44 84 40 64 128 256), losses := [] }

theorem u24963 : Upper (D 6) (R 6) [34,192,258,36,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24963 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24964 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 194 262 44 84 48 73 137 265), lower := (rows 35 194 262 44 84 48 64 128 256), losses := [] }

theorem u24964 : Upper (D 6) (R 6) [34,192,258,36,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24964 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24965 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 194 262 44 88 33 85 149 277), lower := (rows 35 194 262 44 88 33 64 128 256), losses := [] }

theorem u24965 : Upper (D 6) (R 6) [34,192,258,36,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24966 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 194 262 44 88 36 81 145 273), lower := (rows 35 194 262 44 88 36 64 128 256), losses := [] }

theorem u24966 : Upper (D 6) (R 6) [34,192,258,36,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24967 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 262 44 88 48 69 133 261), lower := (rows 35 194 262 44 88 48 64 128 256), losses := [] }

theorem u24967 : Upper (D 6) (R 6) [34,192,258,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24967 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24968 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 262 56 81 33 76 140 268), lower := (rows 35 194 262 56 81 33 64 128 256), losses := [] }

theorem u24968 : Upper (D 6) (R 6) [34,192,258,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24969 : Route 9 := (fun mask => (mask,id))

def c24969 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24969 : Upper (D 6) (R 6) [34,192,258,48,65,4] 13 := by
  apply FastRouting.sound _ _ [34,192,258,48,65,4] 13 (by decide) (choices 1) [1,4,8] r24969 c24969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7759
  · exact u7760
  · exact u7761

def b24970 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 194 262 56 81 40 69 133 261), lower := (rows 35 194 262 56 81 40 64 128 256), losses := [] }

theorem u24970 : Upper (D 6) (R 6) [34,192,258,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24970 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24971 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 194 262 56 84 33 77 141 269), lower := (rows 35 194 262 56 84 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 24 16 55 64 128 256), good := (rows 35 227 291 56 121 33 64 128 256) }] }

theorem u24971 : Upper (D 6) (R 6) [34,192,258,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24972 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 194 262 56 84 36 73 137 265), lower := (rows 35 194 262 56 84 36 64 128 256), losses := [] }

theorem u24972 : Upper (D 6) (R 6) [34,192,258,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24973 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 194 262 56 84 40 69 133 261), lower := (rows 35 194 262 56 84 40 64 128 256), losses := [] }

theorem u24973 : Upper (D 6) (R 6) [34,192,258,48,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24973 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24974 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 268 13 22 33 112 240 368), lower := (rows 35 194 268 13 22 33 64 128 256), losses := [] }

theorem u24974 : Upper (D 6) (R 6) [34,192,264,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24975 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 268 13 22 48 97 225 353), lower := (rows 35 194 268 13 22 48 64 128 256), losses := [] }

theorem u24975 : Upper (D 6) (R 6) [34,192,264,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24975 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24976 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 268 13 22 96 113 177 305), lower := (rows 35 194 268 13 22 96 64 128 256), losses := [] }

theorem u24976 : Upper (D 6) (R 6) [34,192,264,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24977 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 48, targets := 2 }], pairs := [(0,2),(0,6),(4,1)], upper := (rows 35 194 268 13 52 33 82 210 338), lower := (rows 35 194 268 13 52 33 64 128 256), losses := [] }

theorem u24977 : Upper (D 6) (R 6) [34,192,264,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24978 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 13 52 34 81 209 337), lower := (rows 35 194 268 13 52 34 64 128 256), losses := [] }

theorem u24978 : Upper (D 6) (R 6) [34,192,264,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24979 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 268 13 52 48 67 195 323), lower := (rows 35 194 268 13 52 48 64 128 256), losses := [] }

theorem u24979 : Upper (D 6) (R 6) [34,192,264,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24979 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24980 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 268 13 52 96 83 147 275), lower := (rows 35 194 268 13 52 96 64 128 256), losses := [] }

theorem u24980 : Upper (D 6) (R 6) [34,192,264,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24981 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 13 81 34 116 180 308), lower := (rows 35 194 268 13 81 34 64 128 256), losses := [] }

theorem u24981 : Upper (D 6) (R 6) [34,192,264,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24982 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 194 268 13 81 36 114 178 306), lower := (rows 35 194 268 13 81 36 64 128 256), losses := [] }

theorem u24982 : Upper (D 6) (R 6) [34,192,264,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24983 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 268 13 81 48 102 166 294), lower := (rows 35 194 268 13 81 48 64 128 256), losses := [] }

theorem u24983 : Upper (D 6) (R 6) [34,192,264,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24983 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24984 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 268 13 84 33 114 178 306), lower := (rows 35 194 268 13 84 33 64 128 256), losses := [] }

theorem u24984 : Upper (D 6) (R 6) [34,192,264,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24985 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 13 84 34 113 177 305), lower := (rows 35 194 268 13 84 34 64 128 256), losses := [] }

theorem u24985 : Upper (D 6) (R 6) [34,192,264,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24986 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 268 13 84 48 99 163 291), lower := (rows 35 194 268 13 84 48 64 128 256), losses := [] }

theorem u24986 : Upper (D 6) (R 6) [34,192,264,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24986 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24987 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 268 13 112 33 86 150 278), lower := (rows 35 194 268 13 112 33 64 128 256), losses := [] }

theorem u24987 : Upper (D 6) (R 6) [34,192,264,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24988 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 13 112 34 85 149 277), lower := (rows 35 194 268 13 112 34 64 128 256), losses := [] }

theorem u24988 : Upper (D 6) (R 6) [34,192,264,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24989 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 194 268 13 112 36 83 147 275), lower := (rows 35 194 268 13 112 36 64 128 256), losses := [] }

theorem u24989 : Upper (D 6) (R 6) [34,192,264,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24990 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 268 13 112 48 71 135 263), lower := (rows 35 194 268 13 112 48 64 128 256), losses := [] }

theorem u24990 : Upper (D 6) (R 6) [34,192,264,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24990 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24991 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 49, targets := 64 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 194 268 14 21 33 112 240 368), lower := (rows 35 194 268 14 21 33 64 128 256), losses := [] }

theorem u24991 : Upper (D 6) (R 6) [34,192,264,6,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24992 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 194 268 14 21 48 97 225 353), lower := (rows 35 194 268 14 21 48 64 128 256), losses := [] }

theorem u24992 : Upper (D 6) (R 6) [34,192,264,6,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24992 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24993 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 268 14 21 96 113 177 305), lower := (rows 35 194 268 14 21 96 64 128 256), losses := [] }

theorem u24993 : Upper (D 6) (R 6) [34,192,264,6,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24994 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 49, targets := 64 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 194 268 14 52 33 81 209 337), lower := (rows 35 194 268 14 52 33 64 128 256), losses := [] }

theorem u24994 : Upper (D 6) (R 6) [34,192,264,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24995 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 268 14 52 48 65 193 321), lower := (rows 35 194 268 14 52 48 64 128 256), losses := [] }

theorem u24995 : Upper (D 6) (R 6) [34,192,264,6,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24995 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24996 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 268 14 52 96 81 145 273), lower := (rows 35 194 268 14 52 96 64 128 256), losses := [] }

theorem u24996 : Upper (D 6) (R 6) [34,192,264,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24997 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 268 14 81 33 116 180 308), lower := (rows 35 194 268 14 81 33 64 128 256), losses := [] }

theorem u24997 : Upper (D 6) (R 6) [34,192,264,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24998 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 194 268 14 81 36 113 177 305), lower := (rows 35 194 268 14 81 36 64 128 256), losses := [] }

theorem u24998 : Upper (D 6) (R 6) [34,192,264,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24999 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 268 14 81 48 101 165 293), lower := (rows 35 194 268 14 81 48 64 128 256), losses := [] }

theorem u24999 : Upper (D 6) (R 6) [34,192,264,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24999 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25000 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 163, targets := 4 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 194 268 14 84 33 113 177 305), lower := (rows 35 194 268 14 84 33 64 128 256), losses := [] }

theorem u25000 : Upper (D 6) (R 6) [34,192,264,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25001 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 268 14 84 48 97 161 289), lower := (rows 35 194 268 14 84 48 64 128 256), losses := [] }

theorem u25001 : Upper (D 6) (R 6) [34,192,264,6,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25001 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25002 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 268 14 112 33 85 149 277), lower := (rows 35 194 268 14 112 33 64 128 256), losses := [] }

theorem u25002 : Upper (D 6) (R 6) [34,192,264,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25003 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 194 268 14 112 36 81 145 273), lower := (rows 35 194 268 14 112 36 64 128 256), losses := [] }

theorem u25003 : Upper (D 6) (R 6) [34,192,264,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25004 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 268 14 112 48 69 133 261), lower := (rows 35 194 268 14 112 48 64 128 256), losses := [] }

theorem u25004 : Upper (D 6) (R 6) [34,192,264,6,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25004 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25005 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 194 268 25 22 33 100 228 356), lower := (rows 35 194 268 25 22 33 64 128 256), losses := [] }

theorem u25005 : Upper (D 6) (R 6) [34,192,264,17,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25005 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25006 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 194 268 25 22 36 97 225 353), lower := (rows 35 194 268 25 22 36 64 128 256), losses := [] }

theorem u25006 : Upper (D 6) (R 6) [34,192,264,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25006 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25007 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 268 25 22 96 101 165 293), lower := (rows 35 194 268 25 22 96 64 128 256), losses := [] }

theorem u25007 : Upper (D 6) (R 6) [34,192,264,17,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25007 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25008 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 268 25 52 33 70 198 326), lower := (rows 35 194 268 25 52 33 64 128 256), losses := [] }

theorem u25008 : Upper (D 6) (R 6) [34,192,264,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25009 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 25 52 34 69 197 325), lower := (rows 35 194 268 25 52 34 64 128 256), losses := [] }

theorem u25009 : Upper (D 6) (R 6) [34,192,264,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25009 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25010 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 268 25 52 36 67 195 323), lower := (rows 35 194 268 25 52 36 64 128 256), losses := [] }

theorem u25010 : Upper (D 6) (R 6) [34,192,264,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25010 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25011 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 268 25 52 96 71 135 263), lower := (rows 35 194 268 25 52 96 64 128 256), losses := [] }

theorem u25011 : Upper (D 6) (R 6) [34,192,264,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25011 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25012 : Route 9 := (fun mask => (mask,id))

def c25012 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25012 : Upper (D 6) (R 6) [34,192,264,17,68,1] 13 := by
  apply FastRouting.sound _ _ [34,192,264,17,68,1] 13 (by decide) (choices 1) [2,4,32] r25012 c25012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7762
  · exact u7763
  · exact u7764

def b25013 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 25 84 34 101 165 293), lower := (rows 35 194 268 25 84 34 64 128 256), losses := [] }

theorem u25013 : Upper (D 6) (R 6) [34,192,264,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25013 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25014 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(2,6)], upper := (rows 35 194 268 25 84 36 99 163 291), lower := (rows 35 194 268 25 84 36 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 60 0 129 257), good := (rows 419 130 300 445 52 36 0 128 256) }] }

theorem u25014 : Upper (D 6) (R 6) [34,192,264,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25014 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25015 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 268 25 112 33 70 134 262), lower := (rows 35 194 268 25 112 33 64 128 256), losses := [] }

theorem u25015 : Upper (D 6) (R 6) [34,192,264,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25015 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25016 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 268 25 112 34 69 133 261), lower := (rows 35 194 268 25 112 34 64 128 256), losses := [] }

theorem u25016 : Upper (D 6) (R 6) [34,192,264,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25016 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25017 : Route 9 := (fun mask => (mask,id))

def c25017 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25017 : Upper (D 6) (R 6) [34,192,264,17,96,4] 13 := by
  apply FastRouting.sound _ _ [34,192,264,17,96,4] 13 (by decide) (choices 1) [1,2,4] r25017 c25017
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7765
  · exact u7766
  · exact u7767

def b25018 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 194 268 26 21 33 100 228 356), lower := (rows 35 194 268 26 21 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 88 152 280), good := (rows 33 192 460 508 501 33 64 128 256) }] }

theorem u25018 : Upper (D 6) (R 6) [34,192,264,18,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25019 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 35 194 268 26 21 36 97 225 353), lower := (rows 35 194 268 26 21 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 60 81 145 273), good := (rows 481 192 300 508 501 36 64 128 256) }] }

theorem u25019 : Upper (D 6) (R 6) [34,192,264,18,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u25019
end Delivery.IrregularNine14.P06
