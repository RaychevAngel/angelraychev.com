import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0000
import IrregularNine14P08C0001

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1080 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 7 35 196 104 304 48 201 137 393), lower := (rows 7 35 196 104 304 48 64 128 256), losses := [] }

theorem u1080 : Upper (D 8) (R 8) [6,33,192,96,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1080 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1081 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 7 35 196 104 304 160 89 153 281), lower := (rows 7 35 196 104 304 160 64 128 256), losses := [] }

theorem u1081 : Upper (D 8) (R 8) [6,33,192,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1082 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 104 400 33 120 184 312), lower := (rows 7 35 196 104 400 33 64 128 256), losses := [] }

theorem u1082 : Upper (D 8) (R 8) [6,33,192,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1082 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1083 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 35 196 104 400 40 113 177 305), lower := (rows 7 35 196 104 400 40 64 128 256), losses := [] }

theorem u1083 : Upper (D 8) (R 8) [6,33,192,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1083 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1084 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 7 35 196 104 400 48 105 169 297), lower := (rows 7 35 196 104 400 48 64 128 256), losses := [] }

theorem u1084 : Upper (D 8) (R 8) [6,33,192,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1084 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1085 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 56 208 33 224 224 480), lower := (rows 7 35 268 56 208 33 64 128 256), losses := [] }

theorem u1085 : Upper (D 8) (R 8) [6,33,264,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1085 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1086 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 56 208 96 225 161 417), lower := (rows 7 35 268 56 208 96 64 128 256), losses := [] }

theorem u1086 : Upper (D 8) (R 8) [6,33,264,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1087 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 88 176 33 224 224 480), lower := (rows 7 35 268 88 176 33 64 128 256), losses := [] }

theorem u1087 : Upper (D 8) (R 8) [6,33,264,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1088 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 268 88 176 96 225 161 417), lower := (rows 7 35 268 88 176 96 64 128 256), losses := [] }

theorem u1088 : Upper (D 8) (R 8) [6,33,264,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1088 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1089 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 268 88 176 160 97 225 353), lower := (rows 7 35 268 88 176 160 64 128 256), losses := [] }

theorem u1089 : Upper (D 8) (R 8) [6,33,264,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1089 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1090 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 104 176 33 208 208 464), lower := (rows 7 35 268 104 176 33 64 128 256), losses := [] }

theorem u1090 : Upper (D 8) (R 8) [6,33,264,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1091 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 35 268 104 176 48 193 193 449), lower := (rows 7 35 268 104 176 48 64 128 256), losses := [] }

theorem u1091 : Upper (D 8) (R 8) [6,33,264,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1091 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1092 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 104 176 96 209 145 401), lower := (rows 7 35 268 104 176 96 64 128 256), losses := [] }

theorem u1092 : Upper (D 8) (R 8) [6,33,264,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1093 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 268 104 176 160 81 209 337), lower := (rows 7 35 268 104 176 160 64 128 256), losses := [] }

theorem u1093 : Upper (D 8) (R 8) [6,33,264,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1094 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 104 208 33 240 176 432), lower := (rows 7 35 268 104 208 33 64 128 256), losses := [] }

theorem u1094 : Upper (D 8) (R 8) [6,33,264,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1094 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1095 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 268 104 208 48 225 161 417), lower := (rows 7 35 268 104 208 48 64 128 256), losses := [] }

theorem u1095 : Upper (D 8) (R 8) [6,33,264,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1095 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1096 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 268 104 208 160 113 177 305), lower := (rows 7 35 268 104 208 160 64 128 256), losses := [] }

theorem u1096 : Upper (D 8) (R 8) [6,33,264,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1097 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 200 112 33 240 176 432), lower := (rows 7 35 268 200 112 33 64 128 256), losses := [] }

theorem u1097 : Upper (D 8) (R 8) [6,33,264,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1098 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 268 200 112 48 225 161 417), lower := (rows 7 35 268 200 112 48 64 128 256), losses := [] }

theorem u1098 : Upper (D 8) (R 8) [6,33,264,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1098 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1099 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 7 35 268 200 112 160 113 177 305), lower := (rows 7 35 268 200 112 160 64 128 256), losses := [] }

theorem u1099 : Upper (D 8) (R 8) [6,33,264,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1099 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1100 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 56 152 33 224 224 480), lower := (rows 7 35 324 56 152 33 64 128 256), losses := [] }

theorem u1100 : Upper (D 8) (R 8) [6,33,320,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1101 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 56 152 96 225 161 417), lower := (rows 7 35 324 56 152 96 64 128 256), losses := [] }

theorem u1101 : Upper (D 8) (R 8) [6,33,320,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1102 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 324 56 152 160 97 225 353), lower := (rows 7 35 324 56 152 160 64 128 256), losses := [] }

theorem u1102 : Upper (D 8) (R 8) [6,33,320,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1103 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 56 208 33 232 168 424), lower := (rows 7 35 324 56 208 33 64 128 256), losses := [] }

theorem u1103 : Upper (D 8) (R 8) [6,33,320,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1103 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1104 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 324 56 208 40 225 161 417), lower := (rows 7 35 324 56 208 40 64 128 256), losses := [] }

theorem u1104 : Upper (D 8) (R 8) [6,33,320,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1104 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1105 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 324 56 208 160 105 169 297), lower := (rows 7 35 324 56 208 160 64 128 256), losses := [] }

theorem u1105 : Upper (D 8) (R 8) [6,33,320,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1105 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1106 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 88 176 33 232 168 424), lower := (rows 7 35 324 88 176 33 64 128 256), losses := [] }

theorem u1106 : Upper (D 8) (R 8) [6,33,320,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1106 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1107 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 324 88 176 40 225 161 417), lower := (rows 7 35 324 88 176 40 64 128 256), losses := [] }

theorem u1107 : Upper (D 8) (R 8) [6,33,320,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1107 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1108 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 324 88 176 160 105 169 297), lower := (rows 7 35 324 88 176 160 64 128 256), losses := [] }

theorem u1108 : Upper (D 8) (R 8) [6,33,320,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1109 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 104 152 33 240 176 432), lower := (rows 7 35 324 104 152 33 64 128 256), losses := [] }

theorem u1109 : Upper (D 8) (R 8) [6,33,320,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1110 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 324 104 152 48 225 161 417), lower := (rows 7 35 324 104 152 48 64 128 256), losses := [] }

theorem u1110 : Upper (D 8) (R 8) [6,33,320,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1110 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1111 : Route 9 := (fun mask => (mask,id))

def c1111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1111 : Upper (D 8) (R 8) [6,33,320,96,136,128] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96,136,128] 13 (by decide) (choices 1) [1,16,32] r1111 c1111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u59
  · exact u60
  · exact u61

def b1112 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 104 176 33 216 152 408), lower := (rows 7 35 324 104 176 33 64 128 256), losses := [] }

theorem u1112 : Upper (D 8) (R 8) [6,33,320,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1113 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 7 35 324 104 176 40 209 145 401), lower := (rows 7 35 324 104 176 40 64 128 256), losses := [] }

theorem u1113 : Upper (D 8) (R 8) [6,33,320,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1113 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1114 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 7 35 324 104 176 48 201 137 393), lower := (rows 7 35 324 104 176 48 64 128 256), losses := [] }

theorem u1114 : Upper (D 8) (R 8) [6,33,320,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1114 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1115 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 324 104 176 160 89 153 281), lower := (rows 7 35 324 104 176 160 64 128 256), losses := [] }

theorem u1115 : Upper (D 8) (R 8) [6,33,320,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1116 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 168 208 33 120 184 312), lower := (rows 7 35 324 168 208 33 64 128 256), losses := [] }

theorem u1116 : Upper (D 8) (R 8) [6,33,320,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1117 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 35 324 168 208 40 113 177 305), lower := (rows 7 35 324 168 208 40 64 128 256), losses := [] }

theorem u1117 : Upper (D 8) (R 8) [6,33,320,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1117 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1118 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 7 35 324 168 208 48 105 169 297), lower := (rows 7 35 324 168 208 48 64 128 256), losses := [] }

theorem u1118 : Upper (D 8) (R 8) [6,33,320,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1118 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1119 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 52 73 400 33 224 224 480), lower := (rows 7 42 52 73 400 33 64 128 256), losses := [] }

theorem u1119 : Upper (D 8) (R 8) [6,40,48,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1120 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 52 73 400 96 225 161 417), lower := (rows 7 42 52 73 400 96 64 128 256), losses := [] }

theorem u1120 : Upper (D 8) (R 8) [6,40,48,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1120 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1121 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 52 73 400 160 97 225 353), lower := (rows 7 42 52 73 400 160 64 128 256), losses := [] }

theorem u1121 : Upper (D 8) (R 8) [6,40,48,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1121 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1122 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 52 200 273 33 224 224 480), lower := (rows 7 42 52 200 273 33 64 128 256), losses := [] }

theorem u1122 : Upper (D 8) (R 8) [6,40,48,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1123 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 52 200 273 96 225 161 417), lower := (rows 7 42 52 200 273 96 64 128 256), losses := [] }

theorem u1123 : Upper (D 8) (R 8) [6,40,48,192,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1124 : Route 9 := (fun mask => (mask,id))

def c1124 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1124 : Upper (D 8) (R 8) [6,40,48,192,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,320,1] 13 (by decide) (choices 1) [1,32,128] r1124 c1124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u62
  · exact u63
  · exact u64

def b1125 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 52 200 336 160 97 161 289), lower := (rows 7 42 52 200 336 160 64 128 256), losses := [] }

theorem u1125 : Upper (D 8) (R 8) [6,40,48,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1126 : PairBound 9 := { available := 416, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 152 112 33 480 416 416), lower := (rows 7 42 69 152 112 33 64 128 256), losses := [] }

theorem u1126 : Upper (D 8) (R 8) [6,40,65,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1126 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1127 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 69 152 112 160 353 417 289), lower := (rows 7 42 69 152 112 160 64 128 256), losses := [] }

theorem u1127 : Upper (D 8) (R 8) [6,40,65,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1127 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1128 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 42 69 152 112 288 225 161 417), lower := (rows 7 42 69 152 112 288 64 128 256), losses := [] }

theorem u1128 : Upper (D 8) (R 8) [6,40,65,144,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1128 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1129 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 152 304 33 224 224 480), lower := (rows 7 42 69 152 304 33 64 128 256), losses := [] }

theorem u1129 : Upper (D 8) (R 8) [6,40,65,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1130 : Route 9 := (fun mask => (mask,id))

def c1130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1130 : Upper (D 8) (R 8) [6,40,65,144,288,64] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,288,64] 13 (by decide) (choices 1) [1,32,128] r1130 c1130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u65
  · exact u66
  · exact u67

def b1131 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 69 152 304 160 97 225 353), lower := (rows 7 42 69 152 304 160 64 128 256), losses := [] }

theorem u1131 : Upper (D 8) (R 8) [6,40,65,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1132 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 152 336 33 224 160 416), lower := (rows 7 42 69 152 336 33 64 128 256), losses := [] }

theorem u1132 : Upper (D 8) (R 8) [6,40,65,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1133 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 69 152 336 160 97 161 289), lower := (rows 7 42 69 152 336 160 64 128 256), losses := [] }

theorem u1133 : Upper (D 8) (R 8) [6,40,65,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1134 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 280 112 33 224 160 416), lower := (rows 7 42 69 280 112 33 64 128 256), losses := [] }

theorem u1134 : Upper (D 8) (R 8) [6,40,65,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1135 : Route 9 := (fun mask => (mask,id))

def c1135 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1135 : Upper (D 8) (R 8) [6,40,65,272,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272,96,128] 13 (by decide) (choices 1) [1,32,128] r1135 c1135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u68
  · exact u69
  · exact u70

def b1136 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 280 176 33 224 224 480), lower := (rows 7 42 69 280 176 33 64 128 256), losses := [] }

theorem u1136 : Upper (D 8) (R 8) [6,40,65,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1136 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1137 : Route 9 := (fun mask => (mask,id))

def c1137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1137 : Upper (D 8) (R 8) [6,40,65,272,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272,160,64] 13 (by decide) (choices 1) [1,32,128] r1137 c1137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u71
  · exact u72
  · exact u73

def b1138 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 69 280 176 160 97 225 353), lower := (rows 7 42 69 280 176 160 64 128 256), losses := [] }

theorem u1138 : Upper (D 8) (R 8) [6,40,65,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1139 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 280 208 33 224 160 416), lower := (rows 7 42 69 280 208 33 64 128 256), losses := [] }

theorem u1139 : Upper (D 8) (R 8) [6,40,65,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1139 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u1139
end Delivery.IrregularNine14.P08
