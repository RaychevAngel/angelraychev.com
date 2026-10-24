import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0002

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1020 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 28 140 273 96 225 161 417), lower := (rows 35 67 28 140 273 96 64 128 256), losses := [] }

theorem u1020 : Upper (D 3) (R 3) [34,65,24,132,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1020
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1021 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 140 273 160 97 225 353), lower := (rows 35 67 28 140 273 160 64 128 256), losses := [] }

theorem u1021 : Upper (D 3) (R 3) [34,65,24,132,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1021
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1022 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 168 273 33 196 196 452), lower := (rows 35 67 28 168 273 33 64 128 256), losses := [] }

theorem u1022 : Upper (D 3) (R 3) [34,65,24,160,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1022
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1023 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 67 28 168 273 36 193 193 449), lower := (rows 35 67 28 168 273 36 64 128 256), losses := [] }

theorem u1023 : Upper (D 3) (R 3) [34,65,24,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1023
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1024 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 28 168 273 96 197 133 389), lower := (rows 35 67 28 168 273 96 64 128 256), losses := [] }

theorem u1024 : Upper (D 3) (R 3) [34,65,24,160,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1024
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1025 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 168 273 160 69 197 325), lower := (rows 35 67 28 168 273 160 64 128 256), losses := [] }

theorem u1025 : Upper (D 3) (R 3) [34,65,24,160,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1025
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1026 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 168 336 33 197 133 389), lower := (rows 35 67 28 168 336 33 64 128 256), losses := [] }

theorem u1026 : Upper (D 3) (R 3) [34,65,24,160,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1026
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1027 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 28 168 336 36 193 129 385), lower := (rows 35 67 28 168 336 36 64 128 256), losses := [] }

theorem u1027 : Upper (D 3) (R 3) [34,65,24,160,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1027
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1028 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 168 336 160 69 133 261), lower := (rows 35 67 28 168 336 160 64 128 256), losses := [] }

theorem u1028 : Upper (D 3) (R 3) [34,65,24,160,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1028
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1029 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 200 273 33 228 164 420), lower := (rows 35 67 28 200 273 33 64 128 256), losses := [] }

theorem u1029 : Upper (D 3) (R 3) [34,65,24,192,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1029
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1030 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 28 200 273 36 225 161 417), lower := (rows 35 67 28 200 273 36 64 128 256), losses := [] }

theorem u1030 : Upper (D 3) (R 3) [34,65,24,192,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1030
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1031 : Route 9 := (fun mask => (mask,id))

def c1031 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1031 : Upper (D 3) (R 3) [34,65,24,192,257,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,192,257,128] 13 (by decide) (choices 1) [1,4,32] r1031 c1031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u168
  · exact u169
  · exact u170

def b1032 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 200 304 33 197 133 389), lower := (rows 35 67 28 200 304 33 64 128 256), losses := [] }

theorem u1032 : Upper (D 3) (R 3) [34,65,24,192,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1032
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1033 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 28 200 304 36 193 129 385), lower := (rows 35 67 28 200 304 36 64 128 256), losses := [] }

theorem u1033 : Upper (D 3) (R 3) [34,65,24,192,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1033
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1034 : Route 9 := (fun mask => (mask,id))

def c1034 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1034 : Upper (D 3) (R 3) [34,65,24,192,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,192,288,128] 13 (by decide) (choices 1) [1,4] r1034 c1034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u171
  · exact u172

def b1035 : PairBound 9 := { available := 388, camps := [{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 88 145 33 452 388 388), lower := (rows 35 67 44 88 145 33 64 128 256), losses := [] }

theorem u1035 : Upper (D 3) (R 3) [34,65,40,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1035
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1036 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 35 67 44 88 145 36 449 385 385), lower := (rows 35 67 44 88 145 36 64 128 256), losses := [] }

theorem u1036 : Upper (D 3) (R 3) [34,65,40,80,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1036
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1037 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 88 145 160 325 389 261), lower := (rows 35 67 44 88 145 160 64 128 256), losses := [] }

theorem u1037 : Upper (D 3) (R 3) [34,65,40,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1037
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1038 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 67 44 88 145 288 197 133 389), lower := (rows 35 67 44 88 145 288 64 128 256), losses := [] }

theorem u1038 : Upper (D 3) (R 3) [34,65,40,80,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1038
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1039 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 88 273 33 196 132 388), lower := (rows 35 67 44 88 273 33 64 128 256), losses := [] }

theorem u1039 : Upper (D 3) (R 3) [34,65,40,80,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1039
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1040 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 44 88 273 36 193 129 385), lower := (rows 35 67 44 88 273 36 64 128 256), losses := [] }

theorem u1040 : Upper (D 3) (R 3) [34,65,40,80,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1040
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1041 : Route 9 := (fun mask => (mask,id))

def c1041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1041 : Upper (D 3) (R 3) [34,65,40,80,257,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,257,128] 13 (by decide) (choices 1) [1,4,128] r1041 c1041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u173
  · exact u174
  · exact u175

def b1042 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 88 400 33 197 133 389), lower := (rows 35 67 44 88 400 33 64 128 256), losses := [] }

theorem u1042 : Upper (D 3) (R 3) [34,65,40,80,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1042
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1043 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 44 88 400 36 193 129 385), lower := (rows 35 67 44 88 400 36 64 128 256), losses := [] }

theorem u1043 : Upper (D 3) (R 3) [34,65,40,80,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1043
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1044 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 88 400 160 69 133 261), lower := (rows 35 67 44 88 400 160 64 128 256), losses := [] }

theorem u1044 : Upper (D 3) (R 3) [34,65,40,80,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1044
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1045 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 137 84 33 464 400 400), lower := (rows 35 67 44 137 84 33 64 128 256), losses := [] }

theorem u1045 : Upper (D 3) (R 3) [34,65,40,129,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1045
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1046 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 35 67 44 137 84 48 449 385 385), lower := (rows 35 67 44 137 84 48 64 128 256), losses := [] }

theorem u1046 : Upper (D 3) (R 3) [34,65,40,129,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1046
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1047 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 137 84 160 337 401 273), lower := (rows 35 67 44 137 84 160 64 128 256), losses := [] }

theorem u1047 : Upper (D 3) (R 3) [34,65,40,129,68,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1047
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1048 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 67 44 137 84 288 209 145 401), lower := (rows 35 67 44 137 84 288 64 128 256), losses := [] }

theorem u1048 : Upper (D 3) (R 3) [34,65,40,129,68,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1048
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1049 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 137 208 33 340 404 276), lower := (rows 35 67 44 137 208 33 64 128 256), losses := [] }

theorem u1049 : Upper (D 3) (R 3) [34,65,40,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1049
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1050 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 35 67 44 137 208 36 337 401 273), lower := (rows 35 67 44 137 208 36 64 128 256), losses := [] }

theorem u1050 : Upper (D 3) (R 3) [34,65,40,129,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1050
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1051 : PairBound 9 := { available := 261, camps := [], pairs := [], upper := (rows 35 67 44 137 208 48 325 389 261), lower := (rows 35 67 44 137 208 48 64 128 256), losses := [] }

theorem u1051 : Upper (D 3) (R 3) [34,65,40,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1051
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1052 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 35 67 44 137 208 288 85 149 277), lower := (rows 35 67 44 137 208 288 64 128 256), losses := [] }

theorem u1052 : Upper (D 3) (R 3) [34,65,40,129,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1052
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1053 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 35 67 44 137 273 36 208 208 464), lower := (rows 35 67 44 137 273 36 64 128 256), losses := [] }

theorem u1053 : Upper (D 3) (R 3) [34,65,40,129,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1053
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1054 : PairBound 9 := { available := 196, camps := [], pairs := [], upper := (rows 35 67 44 137 273 48 196 196 452), lower := (rows 35 67 44 137 273 48 64 128 256), losses := [] }

theorem u1054 : Upper (D 3) (R 3) [34,65,40,129,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1054
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1055 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 137 273 96 212 148 404), lower := (rows 35 67 44 137 273 96 64 128 256), losses := [] }

theorem u1055 : Upper (D 3) (R 3) [34,65,40,129,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1055
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1056 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 137 273 160 84 212 340), lower := (rows 35 67 44 137 273 160 64 128 256), losses := [] }

theorem u1056 : Upper (D 3) (R 3) [34,65,40,129,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1056
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1057 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 137 276 33 208 208 464), lower := (rows 35 67 44 137 276 33 64 128 256), losses := [] }

theorem u1057 : Upper (D 3) (R 3) [34,65,40,129,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1057
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1058 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 67 44 137 276 48 193 193 449), lower := (rows 35 67 44 137 276 48 64 128 256), losses := [] }

theorem u1058 : Upper (D 3) (R 3) [34,65,40,129,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1058
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1059 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 137 276 96 209 145 401), lower := (rows 35 67 44 137 276 96 64 128 256), losses := [] }

theorem u1059 : Upper (D 3) (R 3) [34,65,40,129,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1059
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1060 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 137 276 160 81 209 337), lower := (rows 35 67 44 137 276 160 64 128 256), losses := [] }

theorem u1060 : Upper (D 3) (R 3) [34,65,40,129,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1060
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1061 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 137 336 33 212 148 404), lower := (rows 35 67 44 137 336 33 64 128 256), losses := [] }

theorem u1061 : Upper (D 3) (R 3) [34,65,40,129,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1061
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1062 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 67 44 137 336 36 209 145 401), lower := (rows 35 67 44 137 336 36 64 128 256), losses := [] }

theorem u1062 : Upper (D 3) (R 3) [34,65,40,129,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1062
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1063 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 67 44 137 336 48 197 133 389), lower := (rows 35 67 44 137 336 48 64 128 256), losses := [] }

theorem u1063 : Upper (D 3) (R 3) [34,65,40,129,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1063
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1064 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 137 336 160 85 149 277), lower := (rows 35 67 44 137 336 160 64 128 256), losses := [] }

theorem u1064 : Upper (D 3) (R 3) [34,65,40,129,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1064
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1065 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 137 400 33 84 212 340), lower := (rows 35 67 44 137 400 33 64 128 256), losses := [] }

theorem u1065 : Upper (D 3) (R 3) [34,65,40,129,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1065
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1066 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 67 44 137 400 36 81 209 337), lower := (rows 35 67 44 137 400 36 64 128 256), losses := [] }

theorem u1066 : Upper (D 3) (R 3) [34,65,40,129,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1066
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1067 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 35 67 44 137 400 48 69 197 325), lower := (rows 35 67 44 137 400 48 64 128 256), losses := [] }

theorem u1067 : Upper (D 3) (R 3) [34,65,40,129,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1067
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1068 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 137 400 96 85 149 277), lower := (rows 35 67 44 137 400 96 64 128 256), losses := [] }

theorem u1068 : Upper (D 3) (R 3) [34,65,40,129,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1068
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1069 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 152 273 33 196 196 452), lower := (rows 35 67 44 152 273 33 64 128 256), losses := [] }

theorem u1069 : Upper (D 3) (R 3) [34,65,40,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1069
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1070 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 67 44 152 273 36 193 193 449), lower := (rows 35 67 44 152 273 36 64 128 256), losses := [] }

theorem u1070 : Upper (D 3) (R 3) [34,65,40,144,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1070
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1071 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 152 273 96 197 133 389), lower := (rows 35 67 44 152 273 96 64 128 256), losses := [] }

theorem u1071 : Upper (D 3) (R 3) [34,65,40,144,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1071
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1072 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 152 273 160 69 197 325), lower := (rows 35 67 44 152 273 160 64 128 256), losses := [] }

theorem u1072 : Upper (D 3) (R 3) [34,65,40,144,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1072
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1073 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 152 336 33 197 133 389), lower := (rows 35 67 44 152 336 33 64 128 256), losses := [] }

theorem u1073 : Upper (D 3) (R 3) [34,65,40,144,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1073
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1074 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 44 152 336 36 193 129 385), lower := (rows 35 67 44 152 336 36 64 128 256), losses := [] }

theorem u1074 : Upper (D 3) (R 3) [34,65,40,144,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1074
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1075 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 152 336 160 69 133 261), lower := (rows 35 67 44 152 336 160 64 128 256), losses := [] }

theorem u1075 : Upper (D 3) (R 3) [34,65,40,144,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1075
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1076 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 200 145 33 340 404 276), lower := (rows 35 67 44 200 145 33 64 128 256), losses := [] }

theorem u1076 : Upper (D 3) (R 3) [34,65,40,192,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1076
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1077 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 35 67 44 200 145 36 337 401 273), lower := (rows 35 67 44 200 145 36 64 128 256), losses := [] }

theorem u1077 : Upper (D 3) (R 3) [34,65,40,192,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1077
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1078 : PairBound 9 := { available := 261, camps := [], pairs := [], upper := (rows 35 67 44 200 145 48 325 389 261), lower := (rows 35 67 44 200 145 48 64 128 256), losses := [] }

theorem u1078 : Upper (D 3) (R 3) [34,65,40,192,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1078
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1079 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 35 67 44 200 145 288 85 149 277), lower := (rows 35 67 44 200 145 288 64 128 256), losses := [] }

theorem u1079 : Upper (D 3) (R 3) [34,65,40,192,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1079
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1079
end Delivery.IrregularNine14.P03
