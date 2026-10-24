import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0000

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1020 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 7 35 76 152 304 160 97 225 353), lower := (rows 7 35 76 152 304 160 64 128 256), losses := [] }

theorem u1020 : Upper (D 8) (R 8) [6,33,72,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1020 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1021 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 168 112 33 464 400 400), lower := (rows 7 35 76 168 112 33 64 128 256), losses := [] }

theorem u1021 : Upper (D 8) (R 8) [6,33,72,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1022 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 7 35 76 168 112 48 449 385 385), lower := (rows 7 35 76 168 112 48 64 128 256), losses := [] }

theorem u1022 : Upper (D 8) (R 8) [6,33,72,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1022 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1023 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 168 112 160 337 401 273), lower := (rows 7 35 76 168 112 160 64 128 256), losses := [] }

theorem u1023 : Upper (D 8) (R 8) [6,33,72,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1023 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1024 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 7 35 76 168 112 288 209 145 401), lower := (rows 7 35 76 168 112 288 64 128 256), losses := [] }

theorem u1024 : Upper (D 8) (R 8) [6,33,72,160,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1024 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1025 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 168 208 33 368 432 304), lower := (rows 7 35 76 168 208 33 64 128 256), losses := [] }

theorem u1025 : Upper (D 8) (R 8) [6,33,72,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1025 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1026 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 7 35 76 168 208 48 353 417 289), lower := (rows 7 35 76 168 208 48 64 128 256), losses := [] }

theorem u1026 : Upper (D 8) (R 8) [6,33,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1026 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1027 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 35 76 168 208 288 113 177 305), lower := (rows 7 35 76 168 208 288 64 128 256), losses := [] }

theorem u1027 : Upper (D 8) (R 8) [6,33,72,160,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1027 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1028 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 168 304 33 208 208 464), lower := (rows 7 35 76 168 304 33 64 128 256), losses := [] }

theorem u1028 : Upper (D 8) (R 8) [6,33,72,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1028 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1029 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 35 76 168 304 48 193 193 449), lower := (rows 7 35 76 168 304 48 64 128 256), losses := [] }

theorem u1029 : Upper (D 8) (R 8) [6,33,72,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1029 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1030 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 168 304 96 209 145 401), lower := (rows 7 35 76 168 304 96 64 128 256), losses := [] }

theorem u1030 : Upper (D 8) (R 8) [6,33,72,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1031 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 168 304 160 81 209 337), lower := (rows 7 35 76 168 304 160 64 128 256), losses := [] }

theorem u1031 : Upper (D 8) (R 8) [6,33,72,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1032 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 168 336 33 240 176 432), lower := (rows 7 35 76 168 336 33 64 128 256), losses := [] }

theorem u1032 : Upper (D 8) (R 8) [6,33,72,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1033 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 76 168 336 48 225 161 417), lower := (rows 7 35 76 168 336 48 64 128 256), losses := [] }

theorem u1033 : Upper (D 8) (R 8) [6,33,72,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1033 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1034 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 168 336 160 113 177 305), lower := (rows 7 35 76 168 336 160 64 128 256), losses := [] }

theorem u1034 : Upper (D 8) (R 8) [6,33,72,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1035 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 168 400 33 112 240 368), lower := (rows 7 35 76 168 400 33 64 128 256), losses := [] }

theorem u1035 : Upper (D 8) (R 8) [6,33,72,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1036 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 35 76 168 400 48 97 225 353), lower := (rows 7 35 76 168 400 48 64 128 256), losses := [] }

theorem u1036 : Upper (D 8) (R 8) [6,33,72,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1036 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1037 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 168 400 96 113 177 305), lower := (rows 7 35 76 168 400 96 64 128 256), losses := [] }

theorem u1037 : Upper (D 8) (R 8) [6,33,72,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1038 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 280 176 33 224 224 480), lower := (rows 7 35 76 280 176 33 64 128 256), losses := [] }

theorem u1038 : Upper (D 8) (R 8) [6,33,72,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1038 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1039 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 280 176 96 225 161 417), lower := (rows 7 35 76 280 176 96 64 128 256), losses := [] }

theorem u1039 : Upper (D 8) (R 8) [6,33,72,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1040 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 280 176 160 97 225 353), lower := (rows 7 35 76 280 176 160 64 128 256), losses := [] }

theorem u1040 : Upper (D 8) (R 8) [6,33,72,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1040 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1041 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 296 112 33 208 144 400), lower := (rows 7 35 76 296 112 33 64 128 256), losses := [] }

theorem u1041 : Upper (D 8) (R 8) [6,33,72,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1042 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 76 296 112 48 193 129 385), lower := (rows 7 35 76 296 112 48 64 128 256), losses := [] }

theorem u1042 : Upper (D 8) (R 8) [6,33,72,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1042 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1043 : Route 9 := (fun mask => (mask,id))

def c1043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1043 : Upper (D 8) (R 8) [6,33,72,288,96,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,96,128] 13 (by decide) (choices 1) [1,16,128] r1043 c1043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u53
  · exact u54
  · exact u55

def b1044 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 296 176 33 208 208 464), lower := (rows 7 35 76 296 176 33 64 128 256), losses := [] }

theorem u1044 : Upper (D 8) (R 8) [6,33,72,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1044 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1045 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 35 76 296 176 48 193 193 449), lower := (rows 7 35 76 296 176 48 64 128 256), losses := [] }

theorem u1045 : Upper (D 8) (R 8) [6,33,72,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1045 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1046 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 296 176 96 209 145 401), lower := (rows 7 35 76 296 176 96 64 128 256), losses := [] }

theorem u1046 : Upper (D 8) (R 8) [6,33,72,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1047 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 296 176 160 81 209 337), lower := (rows 7 35 76 296 176 160 64 128 256), losses := [] }

theorem u1047 : Upper (D 8) (R 8) [6,33,72,288,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1048 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 296 208 33 240 176 432), lower := (rows 7 35 76 296 208 33 64 128 256), losses := [] }

theorem u1048 : Upper (D 8) (R 8) [6,33,72,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1049 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 76 296 208 48 225 161 417), lower := (rows 7 35 76 296 208 48 64 128 256), losses := [] }

theorem u1049 : Upper (D 8) (R 8) [6,33,72,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1049 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1050 : Route 9 := (fun mask => (mask,id))

def c1050 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1050 : Upper (D 8) (R 8) [6,33,72,288,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288,192,128] 13 (by decide) (choices 1) [1,16,32] r1050 c1050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u56
  · exact u57
  · exact u58

def b1051 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 392 112 33 240 176 432), lower := (rows 7 35 76 392 112 33 64 128 256), losses := [] }

theorem u1051 : Upper (D 8) (R 8) [6,33,72,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1052 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 76 392 112 48 225 161 417), lower := (rows 7 35 76 392 112 48 64 128 256), losses := [] }

theorem u1052 : Upper (D 8) (R 8) [6,33,72,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1052 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1053 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 7 35 76 392 112 160 113 177 305), lower := (rows 7 35 76 392 112 160 64 128 256), losses := [] }

theorem u1053 : Upper (D 8) (R 8) [6,33,72,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1054 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 392 176 33 112 240 368), lower := (rows 7 35 76 392 176 33 64 128 256), losses := [] }

theorem u1054 : Upper (D 8) (R 8) [6,33,72,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1055 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 35 76 392 176 48 97 225 353), lower := (rows 7 35 76 392 176 48 64 128 256), losses := [] }

theorem u1055 : Upper (D 8) (R 8) [6,33,72,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1055 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1056 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 392 176 96 113 177 305), lower := (rows 7 35 76 392 176 96 64 128 256), losses := [] }

theorem u1056 : Upper (D 8) (R 8) [6,33,72,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1056 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1057 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 392 208 33 112 176 304), lower := (rows 7 35 76 392 208 33 64 128 256), losses := [] }

theorem u1057 : Upper (D 8) (R 8) [6,33,72,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1058 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 35 76 392 208 48 97 161 289), lower := (rows 7 35 76 392 208 48 64 128 256), losses := [] }

theorem u1058 : Upper (D 8) (R 8) [6,33,72,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1058 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1059 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 56 280 33 224 224 480), lower := (rows 7 35 196 56 280 33 64 128 256), losses := [] }

theorem u1059 : Upper (D 8) (R 8) [6,33,192,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1060 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 56 280 96 225 161 417), lower := (rows 7 35 196 56 280 96 64 128 256), losses := [] }

theorem u1060 : Upper (D 8) (R 8) [6,33,192,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1061 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 56 336 33 232 168 424), lower := (rows 7 35 196 56 336 33 64 128 256), losses := [] }

theorem u1061 : Upper (D 8) (R 8) [6,33,192,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1061 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1062 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 196 56 336 40 225 161 417), lower := (rows 7 35 196 56 336 40 64 128 256), losses := [] }

theorem u1062 : Upper (D 8) (R 8) [6,33,192,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1062 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1063 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 7 35 196 56 336 160 105 169 297), lower := (rows 7 35 196 56 336 160 64 128 256), losses := [] }

theorem u1063 : Upper (D 8) (R 8) [6,33,192,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1064 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 88 176 33 360 424 296), lower := (rows 7 35 196 88 176 33 64 128 256), losses := [] }

theorem u1064 : Upper (D 8) (R 8) [6,33,192,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1065 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 7 35 196 88 176 40 353 417 289), lower := (rows 7 35 196 88 176 40 64 128 256), losses := [] }

theorem u1065 : Upper (D 8) (R 8) [6,33,192,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1065 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1066 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 7 35 196 88 176 288 105 169 297), lower := (rows 7 35 196 88 176 288 64 128 256), losses := [] }

theorem u1066 : Upper (D 8) (R 8) [6,33,192,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1066 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1067 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 88 304 33 232 168 424), lower := (rows 7 35 196 88 304 33 64 128 256), losses := [] }

theorem u1067 : Upper (D 8) (R 8) [6,33,192,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1067 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1068 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 196 88 304 40 225 161 417), lower := (rows 7 35 196 88 304 40 64 128 256), losses := [] }

theorem u1068 : Upper (D 8) (R 8) [6,33,192,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1068 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1069 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 7 35 196 88 304 160 105 169 297), lower := (rows 7 35 196 88 304 160 64 128 256), losses := [] }

theorem u1069 : Upper (D 8) (R 8) [6,33,192,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1070 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 88 400 33 104 168 296), lower := (rows 7 35 196 88 400 33 64 128 256), losses := [] }

theorem u1070 : Upper (D 8) (R 8) [6,33,192,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1071 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 35 196 88 400 40 97 161 289), lower := (rows 7 35 196 88 400 40 64 128 256), losses := [] }

theorem u1071 : Upper (D 8) (R 8) [6,33,192,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1071 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1072 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 104 176 33 344 408 280), lower := (rows 7 35 196 104 176 33 64 128 256), losses := [] }

theorem u1072 : Upper (D 8) (R 8) [6,33,192,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1072 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1073 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 7 35 196 104 176 40 337 401 273), lower := (rows 7 35 196 104 176 40 64 128 256), losses := [] }

theorem u1073 : Upper (D 8) (R 8) [6,33,192,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1073 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1074 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 7 35 196 104 176 288 89 153 281), lower := (rows 7 35 196 104 176 288 64 128 256), losses := [] }

theorem u1074 : Upper (D 8) (R 8) [6,33,192,96,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1074 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1075 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 104 280 33 240 176 432), lower := (rows 7 35 196 104 280 33 64 128 256), losses := [] }

theorem u1075 : Upper (D 8) (R 8) [6,33,192,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1076 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 196 104 280 48 225 161 417), lower := (rows 7 35 196 104 280 48 64 128 256), losses := [] }

theorem u1076 : Upper (D 8) (R 8) [6,33,192,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1076 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1077 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 7 35 196 104 280 160 113 177 305), lower := (rows 7 35 196 104 280 160 64 128 256), losses := [] }

theorem u1077 : Upper (D 8) (R 8) [6,33,192,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1078 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 104 304 33 216 152 408), lower := (rows 7 35 196 104 304 33 64 128 256), losses := [] }

theorem u1078 : Upper (D 8) (R 8) [6,33,192,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1079 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 7 35 196 104 304 40 209 145 401), lower := (rows 7 35 196 104 304 40 64 128 256), losses := [] }

theorem u1079 : Upper (D 8) (R 8) [6,33,192,96,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1079 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u1079
end Delivery.IrregularNine14.P08
