import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0002

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1020 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 14 7 280 144 160 98 226 354), lower := (rows 113 14 7 280 144 160 64 128 256), losses := [] }

theorem u1020 : Upper (D 1) (R 1) [112,12,3,272,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1020
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1021 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 7 392 18 160 112 240 368), lower := (rows 113 14 7 392 18 160 64 128 256), losses := [] }

theorem u1021 : Upper (D 1) (R 1) [112,12,3,384,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1021
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1022 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 7 392 48 160 82 210 338), lower := (rows 113 14 7 392 48 160 64 128 256), losses := [] }

theorem u1022 : Upper (D 1) (R 1) [112,12,3,384,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1022
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1023 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 7 392 80 160 114 178 306), lower := (rows 113 14 7 392 80 160 64 128 256), losses := [] }

theorem u1023 : Upper (D 1) (R 1) [112,12,3,384,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1023
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1024 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 22 265 144 34 224 224 480), lower := (rows 113 14 22 265 144 34 64 128 256), losses := [] }

theorem u1024 : Upper (D 1) (R 1) [112,12,18,257,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1024
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1025 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 22 265 144 96 226 162 418), lower := (rows 113 14 22 265 144 96 64 128 256), losses := [] }

theorem u1025 : Upper (D 1) (R 1) [112,12,18,257,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1025
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1026 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 14 22 265 144 160 98 226 354), lower := (rows 113 14 22 265 144 160 64 128 256), losses := [] }

theorem u1026 : Upper (D 1) (R 1) [112,12,18,257,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1026
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1027 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 14 22 296 144 33 194 194 450), lower := (rows 113 14 22 296 144 33 64 128 256), losses := [] }

theorem u1027 : Upper (D 1) (R 1) [112,12,18,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1027
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1028 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 22 296 144 34 193 193 449), lower := (rows 113 14 22 296 144 34 64 128 256), losses := [] }

theorem u1028 : Upper (D 1) (R 1) [112,12,18,288,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1028
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1029 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 22 296 144 96 195 131 387), lower := (rows 113 14 22 296 144 96 64 128 256), losses := [] }

theorem u1029 : Upper (D 1) (R 1) [112,12,18,288,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1029
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1030 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 14 22 296 144 160 67 195 323), lower := (rows 113 14 22 296 144 160 64 128 256), losses := [] }

theorem u1030 : Upper (D 1) (R 1) [112,12,18,288,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1030
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1031 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 133 266 18 160 112 240 368), lower := (rows 113 14 133 266 18 160 64 128 256), losses := [] }

theorem u1031 : Upper (D 1) (R 1) [112,12,129,258,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1031
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1032 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 133 266 48 160 82 210 338), lower := (rows 113 14 133 266 48 160 64 128 256), losses := [] }

theorem u1032 : Upper (D 1) (R 1) [112,12,129,258,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1032
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1033 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 133 266 80 160 114 178 306), lower := (rows 113 14 133 266 80 160 64 128 256), losses := [] }

theorem u1033 : Upper (D 1) (R 1) [112,12,129,258,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1033
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1034 : PairBound 9 := { available := 98, camps := [], pairs := [(2,4)], upper := (rows 113 14 133 280 144 34 98 226 354), lower := (rows 113 14 133 280 144 34 64 128 256), losses := [{ target := 4, region := (rows 1 2 5 8 0 34 98 162 290), good := (rows 485 494 133 264 128 482 64 128 256) }] }

theorem u1034 : Upper (D 1) (R 1) [112,12,129,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1034
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1035 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 133 280 144 96 98 162 290), lower := (rows 113 14 133 280 144 96 64 128 256), losses := [] }

theorem u1035 : Upper (D 1) (R 1) [112,12,129,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1035
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1036 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 134 265 18 160 112 240 368), lower := (rows 113 14 134 265 18 160 64 128 256), losses := [] }

theorem u1036 : Upper (D 1) (R 1) [112,12,130,257,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1036
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1037 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 134 265 48 160 82 210 338), lower := (rows 113 14 134 265 48 160 64 128 256), losses := [] }

theorem u1037 : Upper (D 1) (R 1) [112,12,130,257,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1037
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1038 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 134 265 80 160 114 178 306), lower := (rows 113 14 134 265 80 160 64 128 256), losses := [] }

theorem u1038 : Upper (D 1) (R 1) [112,12,130,257,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1038
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1039 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 14 134 280 144 33 98 226 354), lower := (rows 113 14 134 280 144 33 64 128 256), losses := [] }

theorem u1039 : Upper (D 1) (R 1) [112,12,130,272,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1039
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1040 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1)], upper := (rows 113 14 134 280 144 34 97 225 353), lower := (rows 113 14 134 280 144 34 64 128 256), losses := [] }

theorem u1040 : Upper (D 1) (R 1) [112,12,130,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1040
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1041 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 134 280 144 96 99 163 291), lower := (rows 113 14 134 280 144 96 64 128 256), losses := [] }

theorem u1041 : Upper (D 1) (R 1) [112,12,130,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1041
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1042 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 14 148 296 18 33 194 194 450), lower := (rows 113 14 148 296 18 33 64 128 256), losses := [] }

theorem u1042 : Upper (D 1) (R 1) [112,12,144,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1042
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1043 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 132, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 148 296 18 34 193 193 449), lower := (rows 113 14 148 296 18 34 64 128 256), losses := [] }

theorem u1043 : Upper (D 1) (R 1) [112,12,144,288,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1043
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1044 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 148 296 18 96 195 131 387), lower := (rows 113 14 148 296 18 96 64 128 256), losses := [] }

theorem u1044 : Upper (D 1) (R 1) [112,12,144,288,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1044
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1045 : Route 9 := (fun mask => (mask,id))

def c1045 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1045 : Upper (D 1) (R 1) [112,12,144,288,2,128] 13 := by
  apply FastRouting.sound _ _ [112,12,144,288,2,128] 13 (by decide) (choices 1) [1,2] r1045 c1045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u122
  · exact u123

def b1046 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1)], upper := (rows 113 22 14 265 144 34 224 224 480), lower := (rows 113 22 14 265 144 34 64 128 256), losses := [] }

theorem u1046 : Upper (D 1) (R 1) [112,20,10,257,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1046
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1047 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 14 265 144 96 226 162 418), lower := (rows 113 22 14 265 144 96 64 128 256), losses := [] }

theorem u1047 : Upper (D 1) (R 1) [112,20,10,257,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1047
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1048 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 22 14 265 144 160 98 226 354), lower := (rows 113 22 14 265 144 160 64 128 256), losses := [] }

theorem u1048 : Upper (D 1) (R 1) [112,20,10,257,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1048
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1049 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 22 14 296 144 33 194 194 450), lower := (rows 113 22 14 296 144 33 64 128 256), losses := [] }

theorem u1049 : Upper (D 1) (R 1) [112,20,10,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1049
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1050 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1)], upper := (rows 113 22 14 296 144 34 193 193 449), lower := (rows 113 22 14 296 144 34 64 128 256), losses := [] }

theorem u1050 : Upper (D 1) (R 1) [112,20,10,288,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1050
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1051 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 14 296 144 96 195 131 387), lower := (rows 113 22 14 296 144 96 64 128 256), losses := [] }

theorem u1051 : Upper (D 1) (R 1) [112,20,10,288,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1051
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1052 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 22 14 296 144 160 67 195 323), lower := (rows 113 22 14 296 144 160 64 128 256), losses := [] }

theorem u1052 : Upper (D 1) (R 1) [112,20,10,288,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1052
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1053 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 22 44 266 144 33 194 194 450), lower := (rows 113 22 44 266 144 33 64 128 256), losses := [] }

theorem u1053 : Upper (D 1) (R 1) [112,20,40,258,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1053
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1054 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 44 266 144 34 193 193 449), lower := (rows 113 22 44 266 144 34 64 128 256), losses := [] }

theorem u1054 : Upper (D 1) (R 1) [112,20,40,258,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1054
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1055 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 44 266 144 96 195 131 387), lower := (rows 113 22 44 266 144 96 64 128 256), losses := [] }

theorem u1055 : Upper (D 1) (R 1) [112,20,40,258,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1055
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1056 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 22 44 266 144 160 67 195 323), lower := (rows 113 22 44 266 144 160 64 128 256), losses := [] }

theorem u1056 : Upper (D 1) (R 1) [112,20,40,258,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1056
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1057 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 113 22 44 328 144 33 194 130 386), lower := (rows 113 22 44 328 144 33 64 128 256), losses := [] }

theorem u1057 : Upper (D 1) (R 1) [112,20,40,320,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1057
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1058 : Route 9 := (fun mask => (mask,id))

def c1058 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1058 : Upper (D 1) (R 1) [112,20,40,320,128,2] 13 := by
  apply FastRouting.sound _ _ [112,20,40,320,128,2] 13 (by decide) (choices 1) [1,2,128] r1058 c1058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u124
  · exact u125
  · exact u126

def b1059 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 22 44 328 144 160 67 131 259), lower := (rows 113 22 44 328 144 160 64 128 256), losses := [] }

theorem u1059 : Upper (D 1) (R 1) [112,20,40,320,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1059
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1060 : PairBound 9 := { available := 104, camps := [{ cop := 5, region := 217, targets := 2 }], pairs := [(0,1)], upper := (rows 113 22 262 137 144 34 104 232 360), lower := (rows 113 22 262 137 144 34 64 128 256), losses := [] }

theorem u1060 : Upper (D 1) (R 1) [112,20,258,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1060
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1061 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 22 262 137 144 40 98 226 354), lower := (rows 113 22 262 137 144 40 64 128 256), losses := [] }

theorem u1061 : Upper (D 1) (R 1) [112,20,258,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1061
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1062 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 262 137 144 96 106 170 298), lower := (rows 113 22 262 137 144 96 64 128 256), losses := [] }

theorem u1062 : Upper (D 1) (R 1) [112,20,258,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1062
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1063 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 22 262 168 144 33 74 202 330), lower := (rows 113 22 262 168 144 33 64 128 256), losses := [] }

theorem u1063 : Upper (D 1) (R 1) [112,20,258,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1063
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1064 : PairBound 9 := { available := 73, camps := [{ cop := 5, region := 217, targets := 2 }], pairs := [(0,1)], upper := (rows 113 22 262 168 144 34 73 201 329), lower := (rows 113 22 262 168 144 34 64 128 256), losses := [] }

theorem u1064 : Upper (D 1) (R 1) [112,20,258,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1064
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1065 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 22 262 168 144 40 67 195 323), lower := (rows 113 22 262 168 144 40 64 128 256), losses := [] }

theorem u1065 : Upper (D 1) (R 1) [112,20,258,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1065
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1066 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 262 168 144 96 75 139 267), lower := (rows 113 22 262 168 144 96 64 128 256), losses := [] }

theorem u1066 : Upper (D 1) (R 1) [112,20,258,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1066
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1067 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 22 268 42 144 33 194 194 450), lower := (rows 113 22 268 42 144 33 64 128 256), losses := [] }

theorem u1067 : Upper (D 1) (R 1) [112,20,264,34,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1067
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1068 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 268 42 144 34 193 193 449), lower := (rows 113 22 268 42 144 34 64 128 256), losses := [] }

theorem u1068 : Upper (D 1) (R 1) [112,20,264,34,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1068
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1069 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 268 42 144 96 195 131 387), lower := (rows 113 22 268 42 144 96 64 128 256), losses := [] }

theorem u1069 : Upper (D 1) (R 1) [112,20,264,34,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1069
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1070 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 22 268 42 144 160 67 195 323), lower := (rows 113 22 268 42 144 160 64 128 256), losses := [] }

theorem u1070 : Upper (D 1) (R 1) [112,20,264,34,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1070
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1071 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 113 22 292 74 144 33 202 138 394), lower := (rows 113 22 292 74 144 33 64 128 256), losses := [] }

theorem u1071 : Upper (D 1) (R 1) [112,20,288,66,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1071
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1072 : Route 9 := (fun mask => (mask,id))

def c1072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1072 : Upper (D 1) (R 1) [112,20,288,66,128,2] 13 := by
  apply FastRouting.sound _ _ [112,20,288,66,128,2] 13 (by decide) (choices 1) [1,8,128] r1072 c1072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u127
  · exact u128
  · exact u129

def b1073 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 113 22 292 74 144 40 195 131 387), lower := (rows 113 22 292 74 144 40 64 128 256), losses := [] }

theorem u1073 : Upper (D 1) (R 1) [112,20,288,66,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1073
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1074 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 22 292 74 144 160 75 139 267), lower := (rows 113 22 292 74 144 160 64 128 256), losses := [] }

theorem u1074 : Upper (D 1) (R 1) [112,20,288,66,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1074
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1075 : Route 9 := (fun mask => (mask,id))

def c1075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1075 : Upper (D 1) (R 1) [112,20,288,129,128,2] 13 := by
  apply FastRouting.sound _ _ [112,20,288,129,128,2] 13 (by decide) (choices 1) [2,8] r1075 c1075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u130
  · exact u131

def b1076 : PairBound 9 := { available := 66, camps := [], pairs := [], upper := (rows 113 22 292 137 144 40 66 194 322), lower := (rows 113 22 292 137 144 40 64 128 256), losses := [] }

theorem u1076 : Upper (D 1) (R 1) [112,20,288,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1076
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1077 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 292 137 144 96 74 138 266), lower := (rows 113 22 292 137 144 96 64 128 256), losses := [] }

theorem u1077 : Upper (D 1) (R 1) [112,20,288,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1077
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1078 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 22 292 138 144 33 74 202 330), lower := (rows 113 22 292 138 144 33 64 128 256), losses := [] }

theorem u1078 : Upper (D 1) (R 1) [112,20,288,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1078
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1079 : Route 9 := (fun mask => (mask,id))

def c1079 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1079 : Upper (D 1) (R 1) [112,20,288,130,128,2] 13 := by
  apply FastRouting.sound _ _ [112,20,288,130,128,2] 13 (by decide) (choices 1) [1,8] r1079 c1079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u132
  · exact u133

#print axioms u1079
end Delivery.IrregularNine14.P01
