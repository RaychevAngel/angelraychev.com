import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1020 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 210, targets := 1 },{ cop := 3, region := 388, targets := 66 }], pairs := [(1,0),(2,1),(2,6),(4,0)], upper := (rows 7 26 261 41 208 96 66 160 416), lower := (rows 7 26 261 41 208 96 66 128 256), losses := [] }

theorem u1020 : Upper (D 7) (R 7) [6,24,257,33,192,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1021 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 389, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 7 26 261 41 208 96 96 130 386), lower := (rows 7 26 261 41 208 96 96 128 256), losses := [] }

theorem u1021 : Upper (D 7) (R 7) [6,24,257,33,192,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1022 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 261 41 208 96 192 162 290), lower := (rows 7 26 261 41 208 96 192 128 256), losses := [] }

theorem u1022 : Upper (D 7) (R 7) [6,24,257,33,192,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1023 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 186, targets := 1 },{ cop := 0, region := 452, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 26 261 104 176 34 65 192 448), lower := (rows 7 26 261 104 176 34 65 128 256), losses := [] }

theorem u1023 : Upper (D 7) (R 7) [6,24,257,96,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1024 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 58, targets := 1 },{ cop := 0, region := 452, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 26 261 104 176 34 192 193 321), lower := (rows 7 26 261 104 176 34 192 128 256), losses := [] }

theorem u1024 : Upper (D 7) (R 7) [6,24,257,96,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1025 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 91, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 26 292 41 81 160 66 192 448), lower := (rows 7 26 292 41 81 160 66 128 256), losses := [] }

theorem u1025 : Upper (D 7) (R 7) [6,24,288,33,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1026 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 0, region := 484, targets := 1 }], pairs := [(1,5),(2,0),(3,1),(4,5)], upper := (rows 7 26 292 41 81 160 192 194 322), lower := (rows 7 26 292 41 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 24 224 224 128 256), good := (rows 5 24 356 121 121 224 224 224 256) }] }

theorem u1026 : Upper (D 7) (R 7) [6,24,288,33,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1027 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 91, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 26 292 42 81 160 65 192 448), lower := (rows 7 26 292 42 81 160 65 128 256), losses := [] }

theorem u1027 : Upper (D 7) (R 7) [6,24,288,34,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1028 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,0),(2,1),(4,1),(4,5)], upper := (rows 7 26 292 42 81 160 192 193 321), lower := (rows 7 26 292 42 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 224 224 128 256), good := (rows 6 26 356 106 122 224 224 224 256) }] }

theorem u1028 : Upper (D 7) (R 7) [6,24,288,34,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1029 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 91, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 26 292 73 112 160 65 130 386), lower := (rows 7 26 292 73 112 160 65 128 256), losses := [] }

theorem u1029 : Upper (D 7) (R 7) [6,24,288,65,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1030 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 91, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 26 292 73 112 160 66 129 385), lower := (rows 7 26 292 73 112 160 66 128 256), losses := [] }

theorem u1030 : Upper (D 7) (R 7) [6,24,288,65,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1031 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 292 73 112 160 192 131 259), lower := (rows 7 26 292 73 112 160 192 128 256), losses := [] }

theorem u1031 : Upper (D 7) (R 7) [6,24,288,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1032 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 388, targets := 67 },{ cop := 4, region := 74, targets := 32 }], pairs := [(1,5),(2,0),(2,1),(2,6)], upper := (rows 7 26 292 73 145 96 66 160 416), lower := (rows 7 26 292 73 145 96 66 128 256), losses := [] }

theorem u1032 : Upper (D 7) (R 7) [6,24,288,65,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1033 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 146, targets := 96 }], pairs := [(1,5),(1,6),(4,5),(4,6)], upper := (rows 7 26 292 73 145 96 96 130 386), lower := (rows 7 26 292 73 145 96 96 128 256), losses := [] }

theorem u1033 : Upper (D 7) (R 7) [6,24,288,65,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1034 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 74, targets := 32 },{ cop := 0, region := 484, targets := 1 },{ cop := 4, region := 72, targets := 2 }], pairs := [(1,5),(2,0),(3,1),(3,5)], upper := (rows 7 26 292 73 145 96 192 162 290), lower := (rows 7 26 292 73 145 96 192 128 256), losses := [] }

theorem u1034 : Upper (D 7) (R 7) [6,24,288,65,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1035 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(1,0),(2,0),(2,1),(4,0)], upper := (rows 7 26 292 73 146 96 65 160 416), lower := (rows 7 26 292 73 146 96 65 128 256), losses := [] }

theorem u1035 : Upper (D 7) (R 7) [6,24,288,65,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1036 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 146, targets := 96 }], pairs := [(1,5),(1,6),(4,5),(4,6)], upper := (rows 7 26 292 73 146 96 96 129 385), lower := (rows 7 26 292 73 146 96 96 128 256), losses := [] }

theorem u1036 : Upper (D 7) (R 7) [6,24,288,65,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1037 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 3, region := 292, targets := 128 }], pairs := [(0,7),(2,1),(2,7),(3,1)], upper := (rows 7 26 292 73 146 96 192 161 289), lower := (rows 7 26 292 73 146 96 192 128 256), losses := [{ target := 7, region := (rows 19 2 14 8 16 104 64 0 266), good := (rows 263 319 292 365 279 96 96 0 256) }] }

theorem u1037 : Upper (D 7) (R 7) [6,24,288,65,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1038 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(1,0),(2,0),(2,1),(4,0)], upper := (rows 7 26 292 73 146 160 65 224 352), lower := (rows 7 26 292 73 146 160 65 128 256), losses := [] }

theorem u1038 : Upper (D 7) (R 7) [6,24,288,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1039 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 3, region := 146, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,5)], upper := (rows 7 26 292 73 146 160 96 193 321), lower := (rows 7 26 292 73 146 160 96 128 256), losses := [] }

theorem u1039 : Upper (D 7) (R 7) [6,24,288,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1040 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 7 26 292 73 176 34 65 192 448), lower := (rows 7 26 292 73 176 34 65 128 256), losses := [] }

theorem u1040 : Upper (D 7) (R 7) [6,24,288,65,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1041 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 200, targets := 34 }], pairs := [(0,7),(2,7),(3,1),(3,5)], upper := (rows 7 26 292 73 176 34 192 193 321), lower := (rows 7 26 292 73 176 34 192 128 256), losses := [{ target := 7, region := (rows 35 2 14 8 16 35 64 0 264), good := (rows 39 319 293 365 49 39 64 0 256) }] }

theorem u1041 : Upper (D 7) (R 7) [6,24,288,65,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1042 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 7 26 292 73 176 96 65 130 386), lower := (rows 7 26 292 73 176 96 65 128 256), losses := [] }

theorem u1042 : Upper (D 7) (R 7) [6,24,288,65,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1043 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 436, targets := 2 },{ cop := 0, region := 72, targets := 32 },{ cop := 0, region := 72, targets := 128 }], pairs := [(2,1),(3,5),(3,7),(4,1)], upper := (rows 7 26 292 73 176 96 66 129 385), lower := (rows 7 26 292 73 176 96 66 128 256), losses := [] }

theorem u1043 : Upper (D 7) (R 7) [6,24,288,65,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1044 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 48, targets := 3 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,0),(3,5),(4,0),(4,1)], upper := (rows 7 26 292 73 176 96 192 131 259), lower := (rows 7 26 292 73 176 96 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 208 250 208 128 256), good := (rows 38 122 292 122 240 112 240 240 256) }] }

theorem u1044 : Upper (D 7) (R 7) [6,24,288,65,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1045 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 388, targets := 67 },{ cop := 0, region := 72, targets := 32 }], pairs := [(2,0),(2,1),(2,6),(3,5)], upper := (rows 7 26 292 73 208 33 66 160 416), lower := (rows 7 26 292 73 208 33 66 128 256), losses := [] }

theorem u1045 : Upper (D 7) (R 7) [6,24,288,65,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1046 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 146, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 7 26 292 73 208 33 96 130 386), lower := (rows 7 26 292 73 208 33 96 128 256), losses := [] }

theorem u1046 : Upper (D 7) (R 7) [6,24,288,65,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1047 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 292 73 208 33 192 162 290), lower := (rows 7 26 292 73 208 33 192 128 256), losses := [] }

theorem u1047 : Upper (D 7) (R 7) [6,24,288,65,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1048 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 6, region := 8, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 7 26 292 73 208 34 65 160 416), lower := (rows 7 26 292 73 208 34 65 128 256), losses := [] }

theorem u1048 : Upper (D 7) (R 7) [6,24,288,65,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1049 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 3, region := 146, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(4,5)], upper := (rows 7 26 292 73 208 34 96 129 385), lower := (rows 7 26 292 73 208 34 96 128 256), losses := [] }

theorem u1049 : Upper (D 7) (R 7) [6,24,288,65,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1050 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 292 73 208 34 192 161 289), lower := (rows 7 26 292 73 208 34 192 128 256), losses := [] }

theorem u1050 : Upper (D 7) (R 7) [6,24,288,65,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1051 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 7 26 292 73 208 160 65 162 290), lower := (rows 7 26 292 73 208 160 65 128 256), losses := [] }

theorem u1051 : Upper (D 7) (R 7) [6,24,288,65,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1052 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 420, targets := 66 },{ cop := 0, region := 72, targets := 160 }], pairs := [(2,1),(2,6),(3,5),(3,7)], upper := (rows 7 26 292 73 208 160 66 161 289), lower := (rows 7 26 292 73 208 160 66 128 256), losses := [] }

theorem u1052 : Upper (D 7) (R 7) [6,24,288,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1053 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 3, region := 146, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(4,5)], upper := (rows 7 26 292 73 208 160 96 131 259), lower := (rows 7 26 292 73 208 160 96 128 256), losses := [] }

theorem u1053 : Upper (D 7) (R 7) [6,24,288,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1054 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 32 },{ cop := 0, region := 72, targets := 128 }], pairs := [(2,1),(3,5),(3,7),(4,1)], upper := (rows 7 26 292 74 176 96 65 129 385), lower := (rows 7 26 292 74 176 96 65 128 256), losses := [] }

theorem u1054 : Upper (D 7) (R 7) [6,24,288,66,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1055 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 58, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 26 292 74 176 96 192 129 257), lower := (rows 7 26 292 74 176 96 192 128 256), losses := [] }

theorem u1055 : Upper (D 7) (R 7) [6,24,288,66,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1056 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 13 88 176 288 66 192 448), lower := (rows 7 35 13 88 176 288 66 128 256), losses := [] }

theorem u1056 : Upper (D 7) (R 7) [6,33,9,80,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1056 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1057 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 13 88 176 288 192 194 322), lower := (rows 7 35 13 88 176 288 192 128 256), losses := [] }

theorem u1057 : Upper (D 7) (R 7) [6,33,9,80,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1057 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1058 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 232, targets := 2 }], pairs := [(0,7),(3,0),(3,1),(4,0)], upper := (rows 7 35 13 88 274 160 96 192 448), lower := (rows 7 35 13 88 274 160 96 128 256), losses := [{ target := 7, region := (rows 17 2 28 24 16 32 98 0 256), good := (rows 71 99 13 93 351 96 96 0 256) }] }

theorem u1058 : Upper (D 7) (R 7) [6,33,9,80,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1059 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 232, targets := 2 }], pairs := [(0,6),(3,0),(3,1),(4,0)], upper := (rows 7 35 13 88 274 160 192 224 352), lower := (rows 7 35 13 88 274 160 192 128 256), losses := [{ target := 6, region := (rows 13 10 12 8 16 224 0 128 256), good := (rows 7 35 15 63 274 160 160 160 256) }] }

theorem u1059 : Upper (D 7) (R 7) [6,33,9,80,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1060 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 13 88 304 160 66 192 448), lower := (rows 7 35 13 88 304 160 66 128 256), losses := [] }

theorem u1060 : Upper (D 7) (R 7) [6,33,9,80,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1061 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(3,1),(3,5),(4,0)], upper := (rows 7 35 13 88 304 160 192 194 322), lower := (rows 7 35 13 88 304 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 224 224 128 256), good := (rows 5 97 13 120 376 224 224 224 256) },{ target := 5, region := (rows 1 2 4 24 16 0 231 131 259), good := (rows 455 451 461 88 344 192 192 192 256) }] }

theorem u1061 : Upper (D 7) (R 7) [6,33,9,80,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1062 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 13 200 112 288 66 144 400), lower := (rows 7 35 13 200 112 288 66 128 256), losses := [] }

theorem u1062 : Upper (D 7) (R 7) [6,33,9,192,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1062 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1063 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 295, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 13 200 112 288 80 130 386), lower := (rows 7 35 13 200 112 288 80 128 256), losses := [] }

theorem u1063 : Upper (D 7) (R 7) [6,33,9,192,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1063 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1064 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 13 200 112 288 192 146 274), lower := (rows 7 35 13 200 112 288 192 128 256), losses := [] }

theorem u1064 : Upper (D 7) (R 7) [6,33,9,192,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1064 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1065 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 13 200 336 48 66 160 416), lower := (rows 7 35 13 200 336 48 66 128 256), losses := [] }

theorem u1065 : Upper (D 7) (R 7) [6,33,9,192,320,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1065 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1066 : PairBound 9 := { available := 130, camps := [{ cop := 8, region := 112, targets := 131 }], pairs := [(4,0),(4,1),(4,7)], upper := (rows 7 35 13 200 336 48 96 130 386), lower := (rows 7 35 13 200 336 48 96 128 256), losses := [] }

theorem u1066 : Upper (D 7) (R 7) [6,33,9,192,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1066 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1067 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 13 200 336 48 192 162 290), lower := (rows 7 35 13 200 336 48 192 128 256), losses := [] }

theorem u1067 : Upper (D 7) (R 7) [6,33,9,192,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1067 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1068 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 7 35 13 280 82 160 96 192 448), lower := (rows 7 35 13 280 82 160 96 128 256), losses := [] }

theorem u1068 : Upper (D 7) (R 7) [6,33,9,272,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1069 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 424, targets := 2 }], pairs := [(3,0),(3,1),(4,0),(4,5)], upper := (rows 7 35 13 280 82 160 192 224 352), lower := (rows 7 35 13 280 82 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 18 0 224 128 256), good := (rows 23 83 13 280 82 192 192 192 256) }] }

theorem u1069 : Upper (D 7) (R 7) [6,33,9,272,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1070 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 35 13 280 112 160 66 192 448), lower := (rows 7 35 13 280 112 160 66 128 256), losses := [] }

theorem u1070 : Upper (D 7) (R 7) [6,33,9,272,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1071 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 13 280 112 160 192 194 322), lower := (rows 7 35 13 280 112 160 192 128 256), losses := [] }

theorem u1071 : Upper (D 7) (R 7) [6,33,9,272,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1072 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 13 328 82 160 80 160 416), lower := (rows 7 35 13 328 82 160 80 128 256), losses := [] }

theorem u1072 : Upper (D 7) (R 7) [6,33,9,320,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1072 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1073 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 7 35 13 328 82 160 96 144 400), lower := (rows 7 35 13 328 82 160 96 128 256), losses := [] }

theorem u1073 : Upper (D 7) (R 7) [6,33,9,320,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1074 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 424, targets := 2 }], pairs := [(3,0),(3,1),(4,0),(4,5)], upper := (rows 7 35 13 328 82 160 192 176 304), lower := (rows 7 35 13 328 82 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 18 0 224 128 256), good := (rows 23 83 13 328 82 192 192 192 256) }] }

theorem u1074 : Upper (D 7) (R 7) [6,33,9,320,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1075 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 35 13 328 112 160 66 144 400), lower := (rows 7 35 13 328 112 160 66 128 256), losses := [] }

theorem u1075 : Upper (D 7) (R 7) [6,33,9,320,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1076 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 13 328 112 160 80 130 386), lower := (rows 7 35 13 328 112 160 80 128 256), losses := [] }

theorem u1076 : Upper (D 7) (R 7) [6,33,9,320,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1076 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1077 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 13 328 112 160 192 146 274), lower := (rows 7 35 13 328 112 160 192 128 256), losses := [] }

theorem u1077 : Upper (D 7) (R 7) [6,33,9,320,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1078 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 13 328 146 160 80 224 352), lower := (rows 7 35 13 328 146 160 80 128 256), losses := [] }

theorem u1078 : Upper (D 7) (R 7) [6,33,9,320,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1078 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1079 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(0,7),(3,0),(3,1),(4,0)], upper := (rows 7 35 13 328 146 160 96 208 336), lower := (rows 7 35 13 328 146 160 96 128 256), losses := [{ target := 7, region := (rows 17 2 20 24 16 32 98 0 272), good := (rows 71 99 13 328 351 96 96 0 256) }] }

theorem u1079 : Upper (D 7) (R 7) [6,33,9,320,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1079
end Delivery.IrregularNine14.P07
