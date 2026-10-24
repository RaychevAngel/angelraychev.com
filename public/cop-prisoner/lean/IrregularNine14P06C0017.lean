import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0000

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1020 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 76 152 274 96 96 133 261), lower := (rows 7 35 76 152 274 96 96 128 256), losses := [] }

theorem u1020 : Upper (D 6) (R 6) [6,33,72,144,258,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1020
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1021 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 168 81 288 66 148 276), lower := (rows 7 35 76 168 81 288 66 128 256), losses := [] }

theorem u1021 : Upper (D 6) (R 6) [6,33,72,160,65,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1021
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1022 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 290, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 7 35 76 168 81 288 68 146 274), lower := (rows 7 35 76 168 81 288 68 128 256), losses := [] }

theorem u1022 : Upper (D 6) (R 6) [6,33,72,160,65,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1022
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1023 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 168 81 288 80 134 262), lower := (rows 7 35 76 168 81 288 80 128 256), losses := [] }

theorem u1023 : Upper (D 6) (R 6) [6,33,72,160,65,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1023
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1024 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 168 82 288 65 148 276), lower := (rows 7 35 76 168 82 288 65 128 256), losses := [] }

theorem u1024 : Upper (D 6) (R 6) [6,33,72,160,66,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1024
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1025 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 168 82 288 68 145 273), lower := (rows 7 35 76 168 82 288 68 128 256), losses := [] }

theorem u1025 : Upper (D 6) (R 6) [6,33,72,160,66,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1025
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1026 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 76 168 82 288 80 133 261), lower := (rows 7 35 76 168 82 288 80 128 256), losses := [] }

theorem u1026 : Upper (D 6) (R 6) [6,33,72,160,66,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1026
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1027 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 133 26 84 96 72 416 288), lower := (rows 7 35 133 26 84 96 72 128 256), losses := [] }

theorem u1027 : Upper (D 6) (R 6) [6,33,129,18,68,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1027
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1028 : PairBound 9 := { available := 264, camps := [{ cop := 3, region := 389, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 35 133 26 84 96 96 392 264), lower := (rows 7 35 133 26 84 96 96 128 256), losses := [] }

theorem u1028 : Upper (D 6) (R 6) [6,33,129,18,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1028
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1029 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 26 84 96 320 168 296), lower := (rows 7 35 133 26 84 96 320 128 256), losses := [] }

theorem u1029 : Upper (D 6) (R 6) [6,33,129,18,68,64,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1029
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1030 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 26 276 96 72 224 352), lower := (rows 7 35 133 26 276 96 72 128 256), losses := [] }

theorem u1030 : Upper (D 6) (R 6) [6,33,129,18,260,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1030
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1031 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 133 26 276 96 96 200 328), lower := (rows 7 35 133 26 276 96 96 128 256), losses := [] }

theorem u1031 : Upper (D 6) (R 6) [6,33,129,18,260,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1031
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1032 : Route 9 := (fun mask => (mask,id))

def c1032 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1032 : Upper (D 6) (R 6) [6,33,129,18,320,64,4] 13 := by
  apply FastRouting.sound _ _ [6,33,129,18,320,64,4] 13 (by decide) (choices 1) [8,32] r1032 c1032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u52
  · exact u53

def b1033 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 133 26 336 96 72 164 292), lower := (rows 7 35 133 26 336 96 72 128 256), losses := [] }

theorem u1033 : Upper (D 6) (R 6) [6,33,129,18,320,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1033
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1034 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 133, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 35 133 26 336 96 96 140 268), lower := (rows 7 35 133 26 336 96 96 128 256), losses := [] }

theorem u1034 : Upper (D 6) (R 6) [6,33,129,18,320,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1034
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1035 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 133 28 82 96 72 416 288), lower := (rows 7 35 133 28 82 96 72 128 256), losses := [] }

theorem u1035 : Upper (D 6) (R 6) [6,33,129,20,66,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1035
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1036 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 397, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 35 133 28 82 96 96 392 264), lower := (rows 7 35 133 28 82 96 96 128 256), losses := [] }

theorem u1036 : Upper (D 6) (R 6) [6,33,129,20,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1036
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1037 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 28 82 96 320 168 296), lower := (rows 7 35 133 28 82 96 320 128 256), losses := [] }

theorem u1037 : Upper (D 6) (R 6) [6,33,129,20,66,64,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1037
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1038 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 28 274 96 72 224 352), lower := (rows 7 35 133 28 274 96 72 128 256), losses := [] }

theorem u1038 : Upper (D 6) (R 6) [6,33,129,20,258,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1038
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1039 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 133 28 274 96 96 200 328), lower := (rows 7 35 133 28 274 96 96 128 256), losses := [] }

theorem u1039 : Upper (D 6) (R 6) [6,33,129,20,258,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1039
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1040 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 133 28 304 96 66 200 328), lower := (rows 7 35 133 28 304 96 66 128 256), losses := [] }

theorem u1040 : Upper (D 6) (R 6) [6,33,129,20,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1040
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1041 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 28 304 96 72 194 322), lower := (rows 7 35 133 28 304 96 72 128 256), losses := [] }

theorem u1041 : Upper (D 6) (R 6) [6,33,129,20,288,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1041
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1042 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 133 28 336 96 66 168 296), lower := (rows 7 35 133 28 336 96 66 128 256), losses := [] }

theorem u1042 : Upper (D 6) (R 6) [6,33,129,20,320,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1042
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1043 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 133 28 336 96 72 162 290), lower := (rows 7 35 133 28 336 96 72 128 256), losses := [] }

theorem u1043 : Upper (D 6) (R 6) [6,33,129,20,320,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1043
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1044 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 133 28 336 96 96 138 266), lower := (rows 7 35 133 28 336 96 96 128 256), losses := [] }

theorem u1044 : Upper (D 6) (R 6) [6,33,129,20,320,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1044
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1045 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 133 56 274 96 68 200 328), lower := (rows 7 35 133 56 274 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 103 69 128 256), good := (rows 101 97 229 56 312 96 100 128 256) }] }

theorem u1045 : Upper (D 6) (R 6) [6,33,129,48,258,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1045
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1046 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 133 56 274 96 72 196 324), lower := (rows 7 35 133 56 274 96 72 128 256), losses := [] }

theorem u1046 : Upper (D 6) (R 6) [6,33,129,48,258,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1046
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1047 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 133 56 276 96 66 200 328), lower := (rows 7 35 133 56 276 96 66 128 256), losses := [] }

theorem u1047 : Upper (D 6) (R 6) [6,33,129,48,260,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1047
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1048 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 133 56 276 96 72 194 322), lower := (rows 7 35 133 56 276 96 72 128 256), losses := [] }

theorem u1048 : Upper (D 6) (R 6) [6,33,129,48,260,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1048
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1049 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 407, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 133 74 276 96 72 176 304), lower := (rows 7 35 133 74 276 96 72 128 256), losses := [] }

theorem u1049 : Upper (D 6) (R 6) [6,33,129,66,260,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1049
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1050 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 74 276 96 80 168 296), lower := (rows 7 35 133 74 276 96 80 128 256), losses := [] }

theorem u1050 : Upper (D 6) (R 6) [6,33,129,66,260,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1050
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1051 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 405, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 35 133 74 276 96 96 152 280), lower := (rows 7 35 133 74 276 96 96 128 256), losses := [] }

theorem u1051 : Upper (D 6) (R 6) [6,33,129,66,260,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1051
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1052 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 304, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 133 74 280 96 68 176 304), lower := (rows 7 35 133 74 280 96 68 128 256), losses := [] }

theorem u1052 : Upper (D 6) (R 6) [6,33,129,66,264,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1052
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1053 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 133 74 280 96 80 164 292), lower := (rows 7 35 133 74 280 96 80 128 256), losses := [] }

theorem u1053 : Upper (D 6) (R 6) [6,33,129,66,264,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1053
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1054 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 405, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 35 133 74 280 96 96 148 276), lower := (rows 7 35 133 74 280 96 96 128 256), losses := [] }

theorem u1054 : Upper (D 6) (R 6) [6,33,129,66,264,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1054
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1055 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 304, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 133 74 304 96 68 152 280), lower := (rows 7 35 133 74 304 96 68 128 256), losses := [] }

theorem u1055 : Upper (D 6) (R 6) [6,33,129,66,288,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1055
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1056 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 407, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 133 74 304 96 72 148 276), lower := (rows 7 35 133 74 304 96 72 128 256), losses := [] }

theorem u1056 : Upper (D 6) (R 6) [6,33,129,66,288,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1056
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1057 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 133, targets := 96 }], pairs := [(0,5),(0,6)], upper := (rows 7 35 133 74 304 96 80 140 268), lower := (rows 7 35 133 74 304 96 80 128 256), losses := [] }

theorem u1057 : Upper (D 6) (R 6) [6,33,129,66,288,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1057
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1058 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 407, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 133 76 274 96 72 176 304), lower := (rows 7 35 133 76 274 96 72 128 256), losses := [] }

theorem u1058 : Upper (D 6) (R 6) [6,33,129,68,258,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1058
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1059 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 76 274 96 80 168 296), lower := (rows 7 35 133 76 274 96 80 128 256), losses := [] }

theorem u1059 : Upper (D 6) (R 6) [6,33,129,68,258,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1059
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1060 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 104, targets := 2 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 133 76 274 96 96 152 280), lower := (rows 7 35 133 76 274 96 96 128 256), losses := [] }

theorem u1060 : Upper (D 6) (R 6) [6,33,129,68,258,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1060
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1061 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 304, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 133 76 280 96 66 176 304), lower := (rows 7 35 133 76 280 96 66 128 256), losses := [] }

theorem u1061 : Upper (D 6) (R 6) [6,33,129,68,264,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1061
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1062 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 133 76 280 96 80 162 290), lower := (rows 7 35 133 76 280 96 80 128 256), losses := [] }

theorem u1062 : Upper (D 6) (R 6) [6,33,129,68,264,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1062
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1063 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 104, targets := 2 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 133 76 280 96 96 146 274), lower := (rows 7 35 133 76 280 96 96 128 256), losses := [] }

theorem u1063 : Upper (D 6) (R 6) [6,33,129,68,264,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1063
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1064 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 304, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 133 76 304 96 66 152 280), lower := (rows 7 35 133 76 304 96 66 128 256), losses := [] }

theorem u1064 : Upper (D 6) (R 6) [6,33,129,68,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1064
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1065 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 407, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 133 76 304 96 72 146 274), lower := (rows 7 35 133 76 304 96 72 128 256), losses := [] }

theorem u1065 : Upper (D 6) (R 6) [6,33,129,68,288,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1065
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1066 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 133 76 304 96 80 138 266), lower := (rows 7 35 133 76 304 96 80 128 256), losses := [] }

theorem u1066 : Upper (D 6) (R 6) [6,33,129,68,288,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1066
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1067 : Route 9 := (fun mask => (mask,id))

def c1067 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1067 : Upper (D 6) (R 6) [6,33,129,80,258,64,4] 13 := by
  apply FastRouting.sound _ _ [6,33,129,80,258,64,4] 13 (by decide) (choices 1) [8,32] r1067 c1067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u54
  · exact u55

def b1068 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 133 88 274 96 72 164 292), lower := (rows 7 35 133 88 274 96 72 128 256), losses := [] }

theorem u1068 : Upper (D 6) (R 6) [6,33,129,80,258,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1068
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1069 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 133 88 274 96 96 140 268), lower := (rows 7 35 133 88 274 96 96 128 256), losses := [] }

theorem u1069 : Upper (D 6) (R 6) [6,33,129,80,258,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1069
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1070 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 133 88 276 96 66 168 296), lower := (rows 7 35 133 88 276 96 66 128 256), losses := [] }

theorem u1070 : Upper (D 6) (R 6) [6,33,129,80,260,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1070
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1071 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 133 88 276 96 72 162 290), lower := (rows 7 35 133 88 276 96 72 128 256), losses := [] }

theorem u1071 : Upper (D 6) (R 6) [6,33,129,80,260,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1071
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1072 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 133 88 276 96 96 138 266), lower := (rows 7 35 133 88 276 96 96 128 256), losses := [] }

theorem u1072 : Upper (D 6) (R 6) [6,33,129,80,260,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1072
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1073 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 133 88 304 96 66 140 268), lower := (rows 7 35 133 88 304 96 66 128 256), losses := [] }

theorem u1073 : Upper (D 6) (R 6) [6,33,129,80,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1073
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1074 : Route 9 := (fun mask => (mask,id))

def c1074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1074 : Upper (D 6) (R 6) [6,33,129,80,288,64,4] 13 := by
  apply FastRouting.sound _ _ [6,33,129,80,288,64,4] 13 (by decide) (choices 1) [2,8] r1074 c1074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u56
  · exact u57

def b1075 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 133 88 304 96 72 134 262), lower := (rows 7 35 133 88 304 96 72 128 256), losses := [] }

theorem u1075 : Upper (D 6) (R 6) [6,33,129,80,288,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1075
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1076 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 368, targets := 2 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,0),(4,1)], upper := (rows 7 35 140 26 336 96 65 164 292), lower := (rows 7 35 140 26 336 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 15 10 112 112 64 202 330), good := (rows 398 446 396 446 496 496 500 128 256) }] }

theorem u1076 : Upper (D 6) (R 6) [6,33,136,18,320,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1076
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1077 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 368, targets := 2 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 7 35 140 26 336 96 68 161 289), lower := (rows 7 35 140 26 336 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 127 77 131 259), good := (rows 501 497 252 508 368 96 100 128 256) },{ target := 6, region := (rows 9 2 12 8 16 32 0 130 258), good := (rows 391 419 141 415 272 32 4 128 256) }] }

theorem u1077 : Upper (D 6) (R 6) [6,33,136,18,320,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1077
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1078 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 133, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 35 140 26 336 96 96 133 261), lower := (rows 7 35 140 26 336 96 96 128 256), losses := [] }

theorem u1078 : Upper (D 6) (R 6) [6,33,136,18,320,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1078
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1079 : Route 9 := (fun mask => (mask,id))

def c1079 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1079 : Upper (D 6) (R 6) [6,33,136,20,288,64,1] 13 := by
  apply FastRouting.sound _ _ [6,33,136,20,288,64,1] 13 (by decide) (choices 1) [2,64] r1079 c1079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u58
  · exact u59

#print axioms u1079
end Delivery.IrregularNine14.P06
