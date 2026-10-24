import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0019

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10080 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 388 28 82 40 97 225 353), lower := (rows 7 35 388 28 82 40 64 128 256), losses := [] }

theorem u10080 : Upper (D 6) (R 6) [6,33,384,20,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10080
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10081 : Route 9 := (fun mask => (mask,id))

def c10081 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10081 : Upper (D 6) (R 6) [6,33,384,20,66,64] 13 := by
  apply FastRouting.sound _ _ [6,33,384,20,66,64] 13 (by decide) (choices 1) [1,8,32] r10081 c10081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1172
  · exact u1173
  · exact u1174

def b10082 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 388 28 88 33 98 226 354), lower := (rows 7 35 388 28 88 33 64 128 256), losses := [] }

theorem u10082 : Upper (D 6) (R 6) [6,33,384,20,72,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10082
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10083 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 388 28 88 34 97 225 353), lower := (rows 7 35 388 28 88 34 64 128 256), losses := [] }

theorem u10083 : Upper (D 6) (R 6) [6,33,384,20,72,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10083
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10084 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 388 28 88 96 99 163 291), lower := (rows 7 35 388 28 88 96 64 128 256), losses := [] }

theorem u10084 : Upper (D 6) (R 6) [6,33,384,20,72,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10084
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10085 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 388 28 112 33 74 202 330), lower := (rows 7 35 388 28 112 33 64 128 256), losses := [] }

theorem u10085 : Upper (D 6) (R 6) [6,33,384,20,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10085
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10086 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 388 28 112 34 73 201 329), lower := (rows 7 35 388 28 112 34 64 128 256), losses := [] }

theorem u10086 : Upper (D 6) (R 6) [6,33,384,20,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10086
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10087 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 388 28 112 40 67 195 323), lower := (rows 7 35 388 28 112 40 64 128 256), losses := [] }

theorem u10087 : Upper (D 6) (R 6) [6,33,384,20,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10087
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10088 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 388 28 112 96 75 139 267), lower := (rows 7 35 388 28 112 96 64 128 256), losses := [] }

theorem u10088 : Upper (D 6) (R 6) [6,33,384,20,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10088
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10089 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 388 44 81 34 88 216 344), lower := (rows 7 35 388 44 81 34 64 128 256), losses := [] }

theorem u10089 : Upper (D 6) (R 6) [6,33,384,36,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10089
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10090 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 388 44 81 40 82 210 338), lower := (rows 7 35 388 44 81 40 64 128 256), losses := [] }

theorem u10090 : Upper (D 6) (R 6) [6,33,384,36,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10090
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10091 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 388 44 81 48 74 202 330), lower := (rows 7 35 388 44 81 48 64 128 256), losses := [] }

theorem u10091 : Upper (D 6) (R 6) [6,33,384,36,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10091
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10092 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 3, targets := 64 },{ cop := 4, region := 34, targets := 4 }], pairs := [(0,6),(1,2),(1,6)], upper := (rows 7 35 388 44 81 96 90 154 282), lower := (rows 7 35 388 44 81 96 64 128 256), losses := [] }

theorem u10092 : Upper (D 6) (R 6) [6,33,384,36,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10092
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10093 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 388 44 82 33 88 216 344), lower := (rows 7 35 388 44 82 33 64 128 256), losses := [] }

theorem u10093 : Upper (D 6) (R 6) [6,33,384,36,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10093
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10094 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 388 44 82 40 81 209 337), lower := (rows 7 35 388 44 82 40 64 128 256), losses := [] }

theorem u10094 : Upper (D 6) (R 6) [6,33,384,36,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10094
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10095 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 388 44 82 48 73 201 329), lower := (rows 7 35 388 44 82 48 64 128 256), losses := [] }

theorem u10095 : Upper (D 6) (R 6) [6,33,384,36,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10095
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10096 : Route 9 := (fun mask => (mask,id))

def c10096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10096 : Upper (D 6) (R 6) [6,33,384,36,66,64] 13 := by
  apply FastRouting.sound _ _ [6,33,384,36,66,64] 13 (by decide) (choices 1) [1,8,16] r10096 c10096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1175
  · exact u1176
  · exact u1177

def b10097 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 388 44 88 33 82 210 338), lower := (rows 7 35 388 44 88 33 64 128 256), losses := [] }

theorem u10097 : Upper (D 6) (R 6) [6,33,384,36,72,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10097
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10098 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 388 44 88 34 81 209 337), lower := (rows 7 35 388 44 88 34 64 128 256), losses := [] }

theorem u10098 : Upper (D 6) (R 6) [6,33,384,36,72,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10098
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10099 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 388 44 88 48 67 195 323), lower := (rows 7 35 388 44 88 48 64 128 256), losses := [] }

theorem u10099 : Upper (D 6) (R 6) [6,33,384,36,72,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10099
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10100 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 388 44 88 96 83 147 275), lower := (rows 7 35 388 44 88 96 64 128 256), losses := [{ target := 6, region := (rows 25 10 20 8 16 32 0 144 272), good := (rows 7 35 388 47 415 32 0 128 256) }] }

theorem u10100 : Upper (D 6) (R 6) [6,33,384,36,72,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10100
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10101 : PairBound 9 := { available := 76, camps := [{ cop := 4, region := 42, targets := 68 }], pairs := [(1,2),(1,6),(3,2)], upper := (rows 7 35 388 56 81 34 76 204 332), lower := (rows 7 35 388 56 81 34 64 128 256), losses := [] }

theorem u10101 : Upper (D 6) (R 6) [6,33,384,48,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10101
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10102 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 88, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 388 56 81 36 74 202 330), lower := (rows 7 35 388 56 81 36 64 128 256), losses := [] }

theorem u10102 : Upper (D 6) (R 6) [6,33,384,48,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10102
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10103 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 42, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 7 35 388 56 81 40 70 198 326), lower := (rows 7 35 388 56 81 40 64 128 256), losses := [] }

theorem u10103 : Upper (D 6) (R 6) [6,33,384,48,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10103
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10104 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 388 56 81 96 78 142 270), lower := (rows 7 35 388 56 81 96 64 128 256), losses := [] }

theorem u10104 : Upper (D 6) (R 6) [6,33,384,48,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10104
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10105 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 388 56 82 33 76 204 332), lower := (rows 7 35 388 56 82 33 64 128 256), losses := [] }

theorem u10105 : Upper (D 6) (R 6) [6,33,384,48,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10105
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10106 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 88, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 388 56 82 36 73 201 329), lower := (rows 7 35 388 56 82 36 64 128 256), losses := [] }

theorem u10106 : Upper (D 6) (R 6) [6,33,384,48,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10106
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10107 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 388 56 82 40 69 197 325), lower := (rows 7 35 388 56 82 40 64 128 256), losses := [] }

theorem u10107 : Upper (D 6) (R 6) [6,33,384,48,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10107
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10108 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 388 56 82 96 77 141 269), lower := (rows 7 35 388 56 82 96 64 128 256), losses := [] }

theorem u10108 : Upper (D 6) (R 6) [6,33,384,48,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10108
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10109 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 388 56 84 33 74 202 330), lower := (rows 7 35 388 56 84 33 64 128 256), losses := [] }

theorem u10109 : Upper (D 6) (R 6) [6,33,384,48,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10109
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10110 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 388 56 84 34 73 201 329), lower := (rows 7 35 388 56 84 34 64 128 256), losses := [] }

theorem u10110 : Upper (D 6) (R 6) [6,33,384,48,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10110
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10111 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 388 56 84 40 67 195 323), lower := (rows 7 35 388 56 84 40 64 128 256), losses := [] }

theorem u10111 : Upper (D 6) (R 6) [6,33,384,48,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10111
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10112 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 388 56 84 96 75 139 267), lower := (rows 7 35 388 56 84 96 64 128 256), losses := [] }

theorem u10112 : Upper (D 6) (R 6) [6,33,384,48,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10112
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10113 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 388 56 88 33 70 198 326), lower := (rows 7 35 388 56 88 33 64 128 256), losses := [] }

theorem u10113 : Upper (D 6) (R 6) [6,33,384,48,72,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10113
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10114 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 388 56 88 34 69 197 325), lower := (rows 7 35 388 56 88 34 64 128 256), losses := [] }

theorem u10114 : Upper (D 6) (R 6) [6,33,384,48,72,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10114
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10115 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 88, targets := 4 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(3,2),(4,2)], upper := (rows 7 35 388 56 88 36 67 195 323), lower := (rows 7 35 388 56 88 36 64 128 256), losses := [] }

theorem u10115 : Upper (D 6) (R 6) [6,33,384,48,72,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10115
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10116 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 388 56 88 96 71 135 263), lower := (rows 7 35 388 56 88 96 64 128 256), losses := [] }

theorem u10116 : Upper (D 6) (R 6) [6,33,384,48,72,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10116
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10117 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 88, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 388 73 82 36 120 184 312), lower := (rows 7 35 388 73 82 36 64 128 256), losses := [] }

theorem u10117 : Upper (D 6) (R 6) [6,33,384,65,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10117
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10118 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 388 73 82 40 116 180 308), lower := (rows 7 35 388 73 82 40 64 128 256), losses := [] }

theorem u10118 : Upper (D 6) (R 6) [6,33,384,65,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10118
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10119 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 388 73 82 48 108 172 300), lower := (rows 7 35 388 73 82 48 64 128 256), losses := [] }

theorem u10119 : Upper (D 6) (R 6) [6,33,384,65,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10119
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10120 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 388 73 84 34 120 184 312), lower := (rows 7 35 388 73 84 34 64 128 256), losses := [] }

theorem u10120 : Upper (D 6) (R 6) [6,33,384,65,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10120
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10121 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 388 73 84 40 114 178 306), lower := (rows 7 35 388 73 84 40 64 128 256), losses := [] }

theorem u10121 : Upper (D 6) (R 6) [6,33,384,65,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10121
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10122 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 388 73 84 48 106 170 298), lower := (rows 7 35 388 73 84 48 64 128 256), losses := [] }

theorem u10122 : Upper (D 6) (R 6) [6,33,384,65,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10122
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10123 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 388 73 112 34 92 156 284), lower := (rows 7 35 388 73 112 34 64 128 256), losses := [] }

theorem u10123 : Upper (D 6) (R 6) [6,33,384,65,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10123
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10124 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 88, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 388 73 112 36 90 154 282), lower := (rows 7 35 388 73 112 36 64 128 256), losses := [] }

theorem u10124 : Upper (D 6) (R 6) [6,33,384,65,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10124
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10125 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 388 73 112 40 86 150 278), lower := (rows 7 35 388 73 112 40 64 128 256), losses := [] }

theorem u10125 : Upper (D 6) (R 6) [6,33,384,65,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10125
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10126 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 388 73 112 48 78 142 270), lower := (rows 7 35 388 73 112 48 64 128 256), losses := [] }

theorem u10126 : Upper (D 6) (R 6) [6,33,384,65,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10126
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10127 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 388 74 84 33 120 184 312), lower := (rows 7 35 388 74 84 33 64 128 256), losses := [] }

theorem u10127 : Upper (D 6) (R 6) [6,33,384,66,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10127
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10128 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 35 388 74 84 40 113 177 305), lower := (rows 7 35 388 74 84 40 64 128 256), losses := [] }

theorem u10128 : Upper (D 6) (R 6) [6,33,384,66,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10128
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10129 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 388 74 84 48 105 169 297), lower := (rows 7 35 388 74 84 48 64 128 256), losses := [] }

theorem u10129 : Upper (D 6) (R 6) [6,33,384,66,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10129
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10130 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 388 74 112 33 92 156 284), lower := (rows 7 35 388 74 112 33 64 128 256), losses := [] }

theorem u10130 : Upper (D 6) (R 6) [6,33,384,66,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10130
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10131 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 88, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 388 74 112 36 89 153 281), lower := (rows 7 35 388 74 112 36 64 128 256), losses := [] }

theorem u10131 : Upper (D 6) (R 6) [6,33,384,66,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10131
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10132 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 388 74 112 40 85 149 277), lower := (rows 7 35 388 74 112 40 64 128 256), losses := [] }

theorem u10132 : Upper (D 6) (R 6) [6,33,384,66,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10132
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10133 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 388 74 112 48 77 141 269), lower := (rows 7 35 388 74 112 48 64 128 256), losses := [] }

theorem u10133 : Upper (D 6) (R 6) [6,33,384,66,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10133
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10134 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 388 76 112 33 90 154 282), lower := (rows 7 35 388 76 112 33 64 128 256), losses := [] }

theorem u10134 : Upper (D 6) (R 6) [6,33,384,68,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10134
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10135 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 388 76 112 34 89 153 281), lower := (rows 7 35 388 76 112 34 64 128 256), losses := [] }

theorem u10135 : Upper (D 6) (R 6) [6,33,384,68,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10135
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10136 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 388 76 112 40 83 147 275), lower := (rows 7 35 388 76 112 40 64 128 256), losses := [] }

theorem u10136 : Upper (D 6) (R 6) [6,33,384,68,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10136
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10137 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 388 76 112 48 75 139 267), lower := (rows 7 35 388 76 112 48 64 128 256), losses := [] }

theorem u10137 : Upper (D 6) (R 6) [6,33,384,68,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10137
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10138 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 52 73 400 33 70 198 326), lower := (rows 7 42 52 73 400 33 64 128 256), losses := [] }

theorem u10138 : Upper (D 6) (R 6) [6,40,48,65,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10138
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10139 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 52 73 400 34 69 197 325), lower := (rows 7 42 52 73 400 34 64 128 256), losses := [] }

theorem u10139 : Upper (D 6) (R 6) [6,40,48,65,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10139
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u10139
end Delivery.IrregularNine14.P06
