import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0000

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1020 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 28 168 336 36 65 384 384), lower := (rows 35 67 28 168 336 36 65 128 256), losses := [] }

theorem u1020 : Upper (D 9) (R 9) [34,65,24,160,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1020 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1021 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 3, region := 67, targets := 256 }], pairs := [(0,8),(1,5),(1,8),(4,5)], upper := (rows 35 67 28 168 336 36 192 385 257), lower := (rows 35 67 28 168 336 36 192 128 256), losses := [] }

theorem u1021 : Upper (D 9) (R 9) [34,65,24,160,320,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1021 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1022 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 28 168 336 36 320 129 385), lower := (rows 35 67 28 168 336 36 320 128 256), losses := [] }

theorem u1022 : Upper (D 9) (R 9) [34,65,24,160,320,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1022 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1023 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 67, targets := 384 },{ cop := 4, region := 172, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 28 168 336 288 65 132 388), lower := (rows 35 67 28 168 336 288 65 128 256), losses := [] }

theorem u1023 : Upper (D 9) (R 9) [34,65,24,160,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1023 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1024 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(3,6)], upper := (rows 35 67 28 168 336 288 68 129 385), lower := (rows 35 67 28 168 336 288 68 128 256), losses := [] }

theorem u1024 : Upper (D 9) (R 9) [34,65,24,160,320,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1024 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1025 : Route 9 := (fun mask => (mask,id))

def c1025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1025 : Upper (D 9) (R 9) [34,65,24,160,320,256,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,160,320,256,128] 13 (by decide) (choices 1) [1,4] r1025 c1025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u45
  · exact u46

def b1026 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 308, targets := 65 }], pairs := [(2,0),(2,6),(4,0),(4,6)], upper := (rows 35 67 28 200 400 36 65 416 288), lower := (rows 35 67 28 200 400 36 65 128 256), losses := [] }

theorem u1026 : Upper (D 9) (R 9) [34,65,24,192,384,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1026 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1027 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 28 200 400 36 96 385 257), lower := (rows 35 67 28 200 400 36 96 128 256), losses := [] }

theorem u1027 : Upper (D 9) (R 9) [34,65,24,192,384,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1027 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1028 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 76, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,0)], upper := (rows 35 67 28 200 400 36 320 161 289), lower := (rows 35 67 28 200 400 36 320 128 256), losses := [] }

theorem u1028 : Upper (D 9) (R 9) [34,65,24,192,384,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1028 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1029 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 308, targets := 65 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(4,0),(4,6)], upper := (rows 35 67 28 200 400 288 65 164 292), lower := (rows 35 67 28 200 400 288 65 128 256), losses := [] }

theorem u1029 : Upper (D 9) (R 9) [34,65,24,192,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1029 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1030 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 76, targets := 288 }], pairs := [(2,5),(2,8),(3,5),(3,8)], upper := (rows 35 67 28 200 400 288 68 161 289), lower := (rows 35 67 28 200 400 288 68 128 256), losses := [] }

theorem u1030 : Upper (D 9) (R 9) [34,65,24,192,384,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1030 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1031 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 28 200 400 288 96 133 261), lower := (rows 35 67 28 200 400 288 96 128 256), losses := [] }

theorem u1031 : Upper (D 9) (R 9) [34,65,24,192,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1031 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1032 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 88 145 288 68 384 384), lower := (rows 35 67 44 88 145 288 68 128 256), losses := [] }

theorem u1032 : Upper (D 9) (R 9) [34,65,40,80,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1032 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1033 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 74, targets := 288 },{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,5),(1,8),(3,5),(3,8)], upper := (rows 35 67 44 88 145 288 192 388 260), lower := (rows 35 67 44 88 145 288 192 128 256), losses := [] }

theorem u1033 : Upper (D 9) (R 9) [34,65,40,80,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1033 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1034 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 364, targets := 1 },{ cop := 5, region := 67, targets := 128 },{ cop := 3, region := 420, targets := 64 }], pairs := [(0,7),(1,7),(2,0),(2,6),(3,0)], upper := (rows 35 67 44 88 145 288 320 132 388), lower := (rows 35 67 44 88 145 288 320 128 256), losses := [] }

theorem u1034 : Upper (D 9) (R 9) [34,65,40,80,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1034 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1035 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 3, region := 420, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 44 88 148 288 65 384 384), lower := (rows 35 67 44 88 148 288 65 128 256), losses := [] }

theorem u1035 : Upper (D 9) (R 9) [34,65,40,80,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1035 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1036 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 33 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,5)], upper := (rows 35 67 44 88 148 288 192 385 257), lower := (rows 35 67 44 88 148 288 192 128 256), losses := [] }

theorem u1036 : Upper (D 9) (R 9) [34,65,40,80,132,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1036 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1037 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 67, targets := 128 },{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(1,5),(1,7),(2,0)], upper := (rows 35 67 44 88 148 288 320 129 385), lower := (rows 35 67 44 88 148 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 352 352 128 256), good := (rows 98 98 108 124 148 352 352 128 352) }] }

theorem u1037 : Upper (D 9) (R 9) [34,65,40,80,132,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1037 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1038 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 83, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 137 84 288 80 384 384), lower := (rows 35 67 44 137 84 288 80 128 256), losses := [] }

theorem u1038 : Upper (D 9) (R 9) [34,65,40,129,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1038 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1039 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 3, region := 66, targets := 288 },{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7),(1,5),(1,8),(2,0),(4,0)], upper := (rows 35 67 44 137 84 288 192 400 272), lower := (rows 35 67 44 137 84 288 192 128 256), losses := [] }

theorem u1039 : Upper (D 9) (R 9) [34,65,40,129,68,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1039 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1040 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 5, region := 67, targets := 128 },{ cop := 2, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(2,0),(4,0),(4,5)], upper := (rows 35 67 44 137 84 288 320 144 400), lower := (rows 35 67 44 137 84 288 320 128 256), losses := [] }

theorem u1040 : Upper (D 9) (R 9) [34,65,40,129,68,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1040 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1041 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 137 208 288 68 400 272), lower := (rows 35 67 44 137 208 288 68 128 256), losses := [] }

theorem u1041 : Upper (D 9) (R 9) [34,65,40,129,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1041 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1042 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 82, targets := 288 }], pairs := [(1,5),(1,8),(4,5),(4,8)], upper := (rows 35 67 44 137 208 288 80 388 260), lower := (rows 35 67 44 137 208 288 80 128 256), losses := [] }

theorem u1042 : Upper (D 9) (R 9) [34,65,40,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1042 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1043 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 5, region := 67, targets := 128 },{ cop := 2, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(2,0),(4,0),(4,5)], upper := (rows 35 67 44 137 208 288 320 148 276), lower := (rows 35 67 44 137 208 288 320 128 256), losses := [] }

theorem u1043 : Upper (D 9) (R 9) [34,65,40,129,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1043 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1044 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(4,0)], upper := (rows 35 67 44 137 276 288 80 192 448), lower := (rows 35 67 44 137 276 288 80 128 256), losses := [] }

theorem u1044 : Upper (D 9) (R 9) [34,65,40,129,260,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1044 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1045 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 3, region := 66, targets := 288 },{ cop := 2, region := 464, targets := 32 }], pairs := [(1,5),(1,8),(2,0),(4,0),(4,5)], upper := (rows 35 67 44 137 276 288 192 208 336), lower := (rows 35 67 44 137 276 288 192 128 256), losses := [] }

theorem u1045 : Upper (D 9) (R 9) [34,65,40,129,260,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1045 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1046 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 137 400 288 68 208 336), lower := (rows 35 67 44 137 400 288 68 128 256), losses := [] }

theorem u1046 : Upper (D 9) (R 9) [34,65,40,129,384,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1046 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1047 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(4,0)], upper := (rows 35 67 44 137 400 288 80 196 324), lower := (rows 35 67 44 137 400 288 80 128 256), losses := [] }

theorem u1047 : Upper (D 9) (R 9) [34,65,40,129,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1047 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1048 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 4, region := 300, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 44 140 208 288 65 400 272), lower := (rows 35 67 44 140 208 288 65 128 256), losses := [] }

theorem u1048 : Upper (D 9) (R 9) [34,65,40,132,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1048 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1049 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 3, region := 80, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 35 67 44 140 208 288 80 385 257), lower := (rows 35 67 44 140 208 288 80 128 256), losses := [] }

theorem u1049 : Upper (D 9) (R 9) [34,65,40,132,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1049 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1050 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 291, targets := 128 },{ cop := 1, region := 144, targets := 256 }], pairs := [(0,7),(1,5),(1,7),(4,5),(4,8)], upper := (rows 35 67 44 140 208 288 320 145 273), lower := (rows 35 67 44 140 208 288 320 128 256), losses := [] }

theorem u1050 : Upper (D 9) (R 9) [34,65,40,132,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1050 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1051 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 4, region := 172, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 44 140 336 288 65 144 400), lower := (rows 35 67 44 140 336 288 65 128 256), losses := [] }

theorem u1051 : Upper (D 9) (R 9) [34,65,40,132,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1051 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1052 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 5, region := 83, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,6)], upper := (rows 35 67 44 140 336 288 80 129 385), lower := (rows 35 67 44 140 336 288 80 128 256), losses := [] }

theorem u1052 : Upper (D 9) (R 9) [34,65,40,132,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1052 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1053 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 307, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(4,5),(4,7)], upper := (rows 35 67 44 140 336 288 192 145 273), lower := (rows 35 67 44 140 336 288 192 128 256), losses := [] }

theorem u1053 : Upper (D 9) (R 9) [34,65,40,132,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1053 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1054 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 83, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 67 44 152 84 288 65 384 384), lower := (rows 35 67 44 152 84 288 65 128 256), losses := [] }

theorem u1054 : Upper (D 9) (R 9) [34,65,40,144,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1054 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1055 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 291, targets := 128 },{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,7),(1,5),(1,7),(4,0)], upper := (rows 35 67 44 152 84 288 192 385 257), lower := (rows 35 67 44 152 84 288 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 288 200 128 256), good := (rows 34 66 124 216 84 288 192 192 288) }] }

theorem u1055 : Upper (D 9) (R 9) [34,65,40,144,68,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1055 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1056 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 67, targets := 128 },{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(1,5),(1,7),(4,0)], upper := (rows 35 67 44 152 84 288 320 129 385), lower := (rows 35 67 44 152 84 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 352 352 128 256), good := (rows 98 98 124 152 116 352 352 128 352) }] }

theorem u1056 : Upper (D 9) (R 9) [34,65,40,144,68,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1056 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1057 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 200 145 288 68 400 272), lower := (rows 35 67 44 200 145 288 68 128 256), losses := [] }

theorem u1057 : Upper (D 9) (R 9) [34,65,40,192,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1057 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1058 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 74, targets := 288 }], pairs := [(1,5),(1,8),(3,5),(3,8)], upper := (rows 35 67 44 200 145 288 80 388 260), lower := (rows 35 67 44 200 145 288 80 128 256), losses := [] }

theorem u1058 : Upper (D 9) (R 9) [34,65,40,192,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1058 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1059 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 364, targets := 1 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,0),(3,0)], upper := (rows 35 67 44 200 145 288 320 148 276), lower := (rows 35 67 44 200 145 288 320 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 352 128 256), good := (rows 67 67 76 200 147 320 320 128 320) }] }

theorem u1059 : Upper (D 9) (R 9) [34,65,40,192,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1059 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1060 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 3, region := 308, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 44 200 148 288 65 400 272), lower := (rows 35 67 44 200 148 288 65 128 256), losses := [] }

theorem u1060 : Upper (D 9) (R 9) [34,65,40,192,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1060 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1061 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 67 44 200 148 288 80 385 257), lower := (rows 35 67 44 200 148 288 80 128 256), losses := [] }

theorem u1061 : Upper (D 9) (R 9) [34,65,40,192,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1061 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1062 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,0),(4,0)], upper := (rows 35 67 44 200 148 288 320 145 273), lower := (rows 35 67 44 200 148 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 352 352 128 256), good := (rows 98 98 124 252 148 352 352 128 352) },{ target := 5, region := (rows 1 3 4 8 16 0 352 128 256), good := (rows 67 67 76 200 148 320 320 128 320) }] }

theorem u1062 : Upper (D 9) (R 9) [34,65,40,192,132,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1062 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1063 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7)], upper := (rows 35 67 44 200 273 48 68 384 384), lower := (rows 35 67 44 200 273 48 68 128 256), losses := [] }

theorem u1063 : Upper (D 9) (R 9) [34,65,40,192,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1063 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1064 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 67 44 200 273 48 192 388 260), lower := (rows 35 67 44 200 273 48 192 128 256), losses := [] }

theorem u1064 : Upper (D 9) (R 9) [34,65,40,192,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1064 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1065 : PairBound 9 := { available := 132, camps := [{ cop := 6, region := 51, targets := 128 },{ cop := 0, region := 460, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 44 200 273 48 320 132 388), lower := (rows 35 67 44 200 273 48 320 128 256), losses := [] }

theorem u1065 : Upper (D 9) (R 9) [34,65,40,192,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1065 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1066 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 200 273 288 68 144 400), lower := (rows 35 67 44 200 273 288 68 128 256), losses := [] }

theorem u1066 : Upper (D 9) (R 9) [34,65,40,192,257,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1066 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1067 : PairBound 9 := { available := 132, camps := [{ cop := 5, region := 83, targets := 128 },{ cop := 1, region := 428, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 44 200 273 288 80 132 388), lower := (rows 35 67 44 200 273 288 80 128 256), losses := [] }

theorem u1067 : Upper (D 9) (R 9) [34,65,40,192,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1067 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1068 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 67 44 200 273 288 192 148 276), lower := (rows 35 67 44 200 273 288 192 128 256), losses := [] }

theorem u1068 : Upper (D 9) (R 9) [34,65,40,192,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1068 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1069 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 200 276 48 65 384 384), lower := (rows 35 67 44 200 276 48 65 128 256), losses := [] }

theorem u1069 : Upper (D 9) (R 9) [34,65,40,192,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1069 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1070 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 67 44 200 276 48 192 385 257), lower := (rows 35 67 44 200 276 48 192 128 256), losses := [] }

theorem u1070 : Upper (D 9) (R 9) [34,65,40,192,260,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1070 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1071 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(3,5)], upper := (rows 35 67 44 200 276 48 320 129 385), lower := (rows 35 67 44 200 276 48 320 128 256), losses := [] }

theorem u1071 : Upper (D 9) (R 9) [34,65,40,192,260,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1071 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1072 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 3, region := 308, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 44 200 276 288 65 144 400), lower := (rows 35 67 44 200 276 288 65 128 256), losses := [] }

theorem u1072 : Upper (D 9) (R 9) [34,65,40,192,260,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1072 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1073 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 99, targets := 128 },{ cop := 1, region := 136, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(3,5)], upper := (rows 35 67 44 200 276 288 80 129 385), lower := (rows 35 67 44 200 276 288 80 128 256), losses := [] }

theorem u1073 : Upper (D 9) (R 9) [34,65,40,192,260,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1073 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1074 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 67 44 200 276 288 192 145 273), lower := (rows 35 67 44 200 276 288 192 128 256), losses := [] }

theorem u1074 : Upper (D 9) (R 9) [34,65,40,192,260,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1074 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1075 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 308, targets := 65 }], pairs := [(2,0),(2,6),(4,0),(4,6)], upper := (rows 35 67 44 200 400 48 65 388 260), lower := (rows 35 67 44 200 400 48 65 128 256), losses := [] }

theorem u1075 : Upper (D 9) (R 9) [34,65,40,192,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1075 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1076 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 67 44 200 400 48 68 385 257), lower := (rows 35 67 44 200 400 48 68 128 256), losses := [] }

theorem u1076 : Upper (D 9) (R 9) [34,65,40,192,384,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1076 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1077 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 4, region := 108, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,0)], upper := (rows 35 67 44 200 400 48 320 133 261), lower := (rows 35 67 44 200 400 48 320 128 256), losses := [] }

theorem u1077 : Upper (D 9) (R 9) [34,65,40,192,384,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1077 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1078 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 3, region := 308, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 44 200 400 288 65 148 276), lower := (rows 35 67 44 200 400 288 65 128 256), losses := [] }

theorem u1078 : Upper (D 9) (R 9) [34,65,40,192,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1078 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1079 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 44 200 400 288 68 145 273), lower := (rows 35 67 44 200 400 288 68 128 256), losses := [] }

theorem u1079 : Upper (D 9) (R 9) [34,65,40,192,384,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1079 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1079
end Delivery.IrregularNine14.P09
