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

def b960 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 67 13 200 276 288 192 176 304), lower := (rows 35 67 13 200 276 288 192 128 256), losses := [] }

theorem u960 : Upper (D 9) (R 9) [34,65,9,192,260,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b960 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b961 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 67 13 200 400 48 68 416 288), lower := (rows 35 67 13 200 400 48 68 128 256), losses := [] }

theorem u961 : Upper (D 9) (R 9) [34,65,9,192,384,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b961 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b962 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 13 200 400 48 96 388 260), lower := (rows 35 67 13 200 400 48 96 128 256), losses := [] }

theorem u962 : Upper (D 9) (R 9) [34,65,9,192,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b962 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b963 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 200 400 48 320 164 292), lower := (rows 35 67 13 200 400 48 320 128 256), losses := [] }

theorem u963 : Upper (D 9) (R 9) [34,65,9,192,384,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b963 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b964 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0)], upper := (rows 35 67 13 200 400 288 68 176 304), lower := (rows 35 67 13 200 400 288 68 128 256), losses := [] }

theorem u964 : Upper (D 9) (R 9) [34,65,9,192,384,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b964 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b965 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 2, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 67 13 200 400 288 80 164 292), lower := (rows 35 67 13 200 400 288 80 128 256), losses := [] }

theorem u965 : Upper (D 9) (R 9) [34,65,9,192,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b965 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b966 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 13 200 400 288 96 148 276), lower := (rows 35 67 13 200 400 288 96 128 256), losses := [] }

theorem u966 : Upper (D 9) (R 9) [34,65,9,192,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b966 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b967 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 82, targets := 416 }], pairs := [(1,5),(1,7),(1,8),(4,5)], upper := (rows 35 67 13 392 84 160 80 416 288), lower := (rows 35 67 13 392 84 160 80 128 256), losses := [] }

theorem u967 : Upper (D 9) (R 9) [34,65,9,384,68,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b967 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b968 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 119, targets := 256 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8),(4,8)], upper := (rows 35 67 13 392 84 160 96 400 272), lower := (rows 35 67 13 392 84 160 96 128 256), losses := [] }

theorem u968 : Upper (D 9) (R 9) [34,65,9,384,68,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b968 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b969 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 163, targets := 256 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,8),(1,8),(3,0),(3,6),(4,0)], upper := (rows 35 67 13 392 84 160 320 176 304), lower := (rows 35 67 13 392 84 160 320 128 256), losses := [] }

theorem u969 : Upper (D 9) (R 9) [34,65,9,384,68,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b969 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b970 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 504, targets := 1 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 392 148 288 80 224 352), lower := (rows 35 67 13 392 148 288 80 128 256), losses := [] }

theorem u970 : Upper (D 9) (R 9) [34,65,9,384,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b970 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b971 : PairBound 9 := { available := 80, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 13 392 148 288 96 208 336), lower := (rows 35 67 13 392 148 288 96 128 256), losses := [] }

theorem u971 : Upper (D 9) (R 9) [34,65,9,384,132,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b971 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b972 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0)], upper := (rows 35 67 13 392 176 288 68 208 336), lower := (rows 35 67 13 392 176 288 68 128 256), losses := [] }

theorem u972 : Upper (D 9) (R 9) [34,65,9,384,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b972 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b973 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 392 176 288 80 196 324), lower := (rows 35 67 13 392 176 288 80 128 256), losses := [] }

theorem u973 : Upper (D 9) (R 9) [34,65,9,384,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b973 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b974 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 67 13 392 208 36 80 416 288), lower := (rows 35 67 13 392 208 36 80 128 256), losses := [] }

theorem u974 : Upper (D 9) (R 9) [34,65,9,384,192,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b974 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b975 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 13 392 208 36 96 400 272), lower := (rows 35 67 13 392 208 36 96 128 256), losses := [] }

theorem u975 : Upper (D 9) (R 9) [34,65,9,384,192,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b975 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b976 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 67 13 392 208 36 320 176 304), lower := (rows 35 67 13 392 208 36 320 128 256), losses := [] }

theorem u976 : Upper (D 9) (R 9) [34,65,9,384,192,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b976 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b977 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0)], upper := (rows 35 67 13 392 208 288 68 176 304), lower := (rows 35 67 13 392 208 288 68 128 256), losses := [] }

theorem u977 : Upper (D 9) (R 9) [34,65,9,384,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b977 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b978 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 7, region := 80, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 35 67 13 392 208 288 80 164 292), lower := (rows 35 67 13 392 208 288 80 128 256), losses := [] }

theorem u978 : Upper (D 9) (R 9) [34,65,9,384,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b978 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b979 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 13 392 208 288 96 148 276), lower := (rows 35 67 13 392 208 288 96 128 256), losses := [] }

theorem u979 : Upper (D 9) (R 9) [34,65,9,384,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b979 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b980 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 364, targets := 1 },{ cop := 6, region := 291, targets := 128 }], pairs := [(0,7),(1,5),(2,0),(3,0),(4,5)], upper := (rows 35 67 28 44 145 288 192 448 320), lower := (rows 35 67 28 44 145 288 192 128 256), losses := [] }

theorem u980 : Upper (D 9) (R 9) [34,65,24,36,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b980 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b981 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 364, targets := 1 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(1,5),(2,0),(3,0),(4,5)], upper := (rows 35 67 28 44 145 288 320 192 448), lower := (rows 35 67 28 44 145 288 320 128 256), losses := [] }

theorem u981 : Upper (D 9) (R 9) [34,65,24,36,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b981 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b982 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 67, targets := 384 },{ cop := 4, region := 300, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 28 44 208 288 65 384 384), lower := (rows 35 67 28 44 208 288 65 128 256), losses := [] }

theorem u982 : Upper (D 9) (R 9) [34,65,24,36,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b982 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b983 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 35 67 28 44 208 288 192 385 257), lower := (rows 35 67 28 44 208 288 192 128 256), losses := [] }

theorem u983 : Upper (D 9) (R 9) [34,65,24,36,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b983 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b984 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 5, region := 67, targets := 128 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(1,5),(1,7),(4,5)], upper := (rows 35 67 28 44 208 288 320 129 385), lower := (rows 35 67 28 44 208 288 320 128 256), losses := [] }

theorem u984 : Upper (D 9) (R 9) [34,65,24,36,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b984 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b985 : PairBound 9 := { available := 384, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 28 76 145 288 96 384 384), lower := (rows 35 67 28 76 145 288 96 128 256), losses := [] }

theorem u985 : Upper (D 9) (R 9) [34,65,24,68,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b985 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b986 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 78, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8),(3,5)], upper := (rows 35 67 28 76 145 288 192 416 288), lower := (rows 35 67 28 76 145 288 192 128 256), losses := [] }

theorem u986 : Upper (D 9) (R 9) [34,65,24,68,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b986 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b987 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 364, targets := 1 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,6),(0,7),(2,0),(3,0),(4,6)], upper := (rows 35 67 28 76 145 288 320 160 416), lower := (rows 35 67 28 76 145 288 320 128 256), losses := [] }

theorem u987 : Upper (D 9) (R 9) [34,65,24,68,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b987 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b988 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 79, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 28 76 176 288 65 384 384), lower := (rows 35 67 28 76 176 288 65 128 256), losses := [] }

theorem u988 : Upper (D 9) (R 9) [34,65,24,68,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b988 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b989 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 76, targets := 33 },{ cop := 4, region := 67, targets := 256 }], pairs := [(0,8),(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 67 28 76 176 288 192 385 257), lower := (rows 35 67 28 76 176 288 192 128 256), losses := [] }

theorem u989 : Upper (D 9) (R 9) [34,65,24,68,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b989 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b990 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 5, region := 67, targets := 128 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,6),(0,7),(1,5),(1,7),(4,6)], upper := (rows 35 67 28 76 176 288 320 129 385), lower := (rows 35 67 28 76 176 288 320 128 256), losses := [] }

theorem u990 : Upper (D 9) (R 9) [34,65,24,68,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b990 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b991 : PairBound 9 := { available := 260, camps := [{ cop := 5, region := 75, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 35 67 28 104 400 160 65 388 260), lower := (rows 35 67 28 104 400 160 65 128 256), losses := [] }

theorem u991 : Upper (D 9) (R 9) [34,65,24,96,384,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b991 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b992 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 28 104 400 160 68 385 257), lower := (rows 35 67 28 104 400 160 68 128 256), losses := [] }

theorem u992 : Upper (D 9) (R 9) [34,65,24,96,384,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b992 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b993 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 3, targets := 384 },{ cop := 4, region := 108, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 28 104 400 160 320 133 261), lower := (rows 35 67 28 104 400 160 320 128 256), losses := [] }

theorem u993 : Upper (D 9) (R 9) [34,65,24,96,384,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b993 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b994 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 28 137 176 288 68 448 320), lower := (rows 35 67 28 137 176 288 68 128 256), losses := [] }

theorem u994 : Upper (D 9) (R 9) [34,65,24,129,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b994 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b995 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(1,5),(1,7),(2,0),(4,0)], upper := (rows 35 67 28 137 176 288 320 196 324), lower := (rows 35 67 28 137 176 288 320 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 356 132 260), good := (rows 67 67 476 139 208 320 320 128 320) }] }

theorem u995 : Upper (D 9) (R 9) [34,65,24,129,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b995 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b996 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 86, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 67 28 137 208 288 68 416 288), lower := (rows 35 67 28 137 208 288 68 128 256), losses := [] }

theorem u996 : Upper (D 9) (R 9) [34,65,24,129,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b996 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b997 : PairBound 9 := { available := 260, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 28 137 208 288 96 388 260), lower := (rows 35 67 28 137 208 288 96 128 256), losses := [] }

theorem u997 : Upper (D 9) (R 9) [34,65,24,129,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b997 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b998 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(1,5),(1,7),(2,0),(4,0)], upper := (rows 35 67 28 137 208 288 320 164 292), lower := (rows 35 67 28 137 208 288 320 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 352 128 256), good := (rows 67 67 28 139 208 320 320 128 320) }] }

theorem u998 : Upper (D 9) (R 9) [34,65,24,129,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b998 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b999 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,7),(2,0),(3,5),(4,0)], upper := (rows 35 67 28 137 304 160 68 448 320), lower := (rows 35 67 28 137 304 160 68 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 17 32 76 0 334), good := (rows 307 339 350 351 304 32 324 0 256) }] }

theorem u999 : Upper (D 9) (R 9) [34,65,24,129,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b999 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1000 : Route 9 := (fun mask => (mask,id))

def c1000 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1000 : Upper (D 9) (R 9) [34,65,24,129,288,128,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,288,128,256] 13 (by decide) (choices 1) [4,64] r1000 c1000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u43
  · exact u44

def b1001 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 28 137 336 36 96 384 384), lower := (rows 35 67 28 137 336 36 96 128 256), losses := [] }

theorem u1001 : Upper (D 9) (R 9) [34,65,24,129,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1001 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1002 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 3, region := 66, targets := 288 }], pairs := [(1,5),(1,8),(2,0),(4,0)], upper := (rows 35 67 28 137 336 36 192 416 288), lower := (rows 35 67 28 137 336 36 192 128 256), losses := [] }

theorem u1002 : Upper (D 9) (R 9) [34,65,24,129,320,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1002 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1003 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 28 137 336 36 320 160 416), lower := (rows 35 67 28 137 336 36 320 128 256), losses := [] }

theorem u1003 : Upper (D 9) (R 9) [34,65,24,129,320,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1003 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1004 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,6),(2,0),(3,6),(4,0)], upper := (rows 35 67 28 137 336 160 68 416 288), lower := (rows 35 67 28 137 336 160 68 128 256), losses := [] }

theorem u1004 : Upper (D 9) (R 9) [34,65,24,129,320,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1004 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1005 : PairBound 9 := { available := 260, camps := [{ cop := 6, region := 3, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 28 137 336 160 96 388 260), lower := (rows 35 67 28 137 336 160 96 128 256), losses := [] }

theorem u1005 : Upper (D 9) (R 9) [34,65,24,129,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1005 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1006 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 67 28 137 336 160 320 164 292), lower := (rows 35 67 28 137 336 160 320 128 256), losses := [] }

theorem u1006 : Upper (D 9) (R 9) [34,65,24,129,320,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1006 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1007 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,6),(2,0),(3,6),(4,0)], upper := (rows 35 67 28 137 336 288 68 160 416), lower := (rows 35 67 28 137 336 288 68 128 256), losses := [] }

theorem u1007 : Upper (D 9) (R 9) [34,65,24,129,320,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1007 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1008 : PairBound 9 := { available := 132, camps := [{ cop := 6, region := 3, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 28 137 336 288 96 132 388), lower := (rows 35 67 28 137 336 288 96 128 256), losses := [] }

theorem u1008 : Upper (D 9) (R 9) [34,65,24,129,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1008 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1009 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 3, region := 66, targets := 288 },{ cop := 4, region := 35, targets := 128 }], pairs := [(0,7),(1,5),(1,8),(2,0),(4,0)], upper := (rows 35 67 28 137 336 288 192 164 292), lower := (rows 35 67 28 137 336 288 192 128 256), losses := [] }

theorem u1009 : Upper (D 9) (R 9) [34,65,24,129,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1009 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1010 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0)], upper := (rows 35 67 28 137 400 288 68 224 352), lower := (rows 35 67 28 137 400 288 68 128 256), losses := [] }

theorem u1010 : Upper (D 9) (R 9) [34,65,24,129,384,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1010 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1011 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 28 137 400 288 96 196 324), lower := (rows 35 67 28 137 400 288 96 128 256), losses := [] }

theorem u1011 : Upper (D 9) (R 9) [34,65,24,129,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1011 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1012 : PairBound 9 := { available := 320, camps := [{ cop := 1, region := 444, targets := 1 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 28 140 304 160 65 448 320), lower := (rows 35 67 28 140 304 160 65 128 256), losses := [] }

theorem u1012 : Upper (D 9) (R 9) [34,65,24,132,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1012 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1013 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 6, region := 163, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 67 28 140 304 160 320 193 321), lower := (rows 35 67 28 140 304 160 320 128 256), losses := [] }

theorem u1013 : Upper (D 9) (R 9) [34,65,24,132,288,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1013 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1014 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 172, targets := 65 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,0),(2,6),(3,0),(3,6)], upper := (rows 35 67 28 140 336 160 65 416 288), lower := (rows 35 67 28 140 336 160 65 128 256), losses := [] }

theorem u1014 : Upper (D 9) (R 9) [34,65,24,132,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1014 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1015 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(2,5),(3,5),(4,5)], upper := (rows 35 67 28 140 336 160 96 385 257), lower := (rows 35 67 28 140 336 160 96 128 256), losses := [] }

theorem u1015 : Upper (D 9) (R 9) [34,65,24,132,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1015 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1016 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 28 140 336 160 320 161 289), lower := (rows 35 67 28 140 336 160 320 128 256), losses := [] }

theorem u1016 : Upper (D 9) (R 9) [34,65,24,132,320,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1016 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1017 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 87, targets := 256 },{ cop := 4, region := 300, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(4,8)], upper := (rows 35 67 28 168 208 288 65 388 260), lower := (rows 35 67 28 168 208 288 65 128 256), losses := [] }

theorem u1017 : Upper (D 9) (R 9) [34,65,24,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1017 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1018 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 35 67 28 168 208 288 68 385 257), lower := (rows 35 67 28 168 208 288 68 128 256), losses := [] }

theorem u1018 : Upper (D 9) (R 9) [34,65,24,160,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1018 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1019 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 28 168 208 288 320 133 261), lower := (rows 35 67 28 168 208 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 24 352 352 128 256), good := (rows 98 98 28 252 252 352 352 128 352) }] }

theorem u1019 : Upper (D 9) (R 9) [34,65,24,160,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1019 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1019
end Delivery.IrregularNine14.P09
