import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0012

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9960 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(3,1)], upper := (rows 37 322 7 88 146 160 96 137 265), lower := (rows 37 322 7 88 146 160 96 128 256), losses := [] }

theorem u9960 : Upper (D 7) (R 7) [36,320,3,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9961 : PairBound 9 := { available := 24, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 322 7 104 145 160 66 152 280), lower := (rows 37 322 7 104 145 160 66 128 256), losses := [] }

theorem u9961 : Upper (D 7) (R 7) [36,320,3,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9962 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 181, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 322 7 104 145 160 72 146 274), lower := (rows 37 322 7 104 145 160 72 128 256), losses := [] }

theorem u9962 : Upper (D 7) (R 7) [36,320,3,96,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9962 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9963 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 7 104 145 160 80 138 266), lower := (rows 37 322 7 104 145 160 80 128 256), losses := [] }

theorem u9963 : Upper (D 7) (R 7) [36,320,3,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9963 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9964 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 37 322 7 104 146 160 65 152 280), lower := (rows 37 322 7 104 146 160 65 128 256), losses := [] }

theorem u9964 : Upper (D 7) (R 7) [36,320,3,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9965 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 181, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 322 7 104 146 160 72 145 273), lower := (rows 37 322 7 104 146 160 72 128 256), losses := [] }

theorem u9965 : Upper (D 7) (R 7) [36,320,3,96,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9965 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9966 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 7 104 146 160 80 137 265), lower := (rows 37 322 7 104 146 160 80 128 256), losses := [] }

theorem u9966 : Upper (D 7) (R 7) [36,320,3,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9966 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9967 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 322 7 104 152 48 65 130 386), lower := (rows 37 322 7 104 152 48 65 128 256), losses := [] }

theorem u9967 : Upper (D 7) (R 7) [36,320,3,96,136,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9967 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9968 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 7 104 152 48 66 129 385), lower := (rows 37 322 7 104 152 48 66 128 256), losses := [] }

theorem u9968 : Upper (D 7) (R 7) [36,320,3,96,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9968 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9969 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 37 322 7 104 152 48 192 131 259), lower := (rows 37 322 7 104 152 48 192 128 256), losses := [] }

theorem u9969 : Upper (D 7) (R 7) [36,320,3,96,136,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9969 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9970 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 37 322 7 104 152 160 65 146 274), lower := (rows 37 322 7 104 152 160 65 128 256), losses := [] }

theorem u9970 : Upper (D 7) (R 7) [36,320,3,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9971 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 322 7 104 152 160 66 145 273), lower := (rows 37 322 7 104 152 160 66 128 256), losses := [{ target := 0, region := (rows 0 258 4 9 16 176 326 128 256), good := (rows 108 322 78 104 184 160 66 160 322) }] }

theorem u9971 : Upper (D 7) (R 7) [36,320,3,96,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9972 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 37 322 7 104 152 160 80 131 259), lower := (rows 37 322 7 104 152 160 80 128 256), losses := [] }

theorem u9972 : Upper (D 7) (R 7) [36,320,3,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9972 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9973 : PairBound 9 := { available := 48, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 7 137 208 40 66 176 304), lower := (rows 37 322 7 137 208 40 66 128 256), losses := [] }

theorem u9973 : Upper (D 7) (R 7) [36,320,3,129,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9973 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9974 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 173, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 322 7 137 208 40 80 162 290), lower := (rows 37 322 7 137 208 40 80 128 256), losses := [] }

theorem u9974 : Upper (D 7) (R 7) [36,320,3,129,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9974 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9975 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 322 7 137 208 40 96 146 274), lower := (rows 37 322 7 137 208 40 96 128 256), losses := [] }

theorem u9975 : Upper (D 7) (R 7) [36,320,3,129,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9975 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9976 : PairBound 9 := { available := 40, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 7 137 208 48 66 168 296), lower := (rows 37 322 7 137 208 48 66 128 256), losses := [] }

theorem u9976 : Upper (D 7) (R 7) [36,320,3,129,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9976 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9977 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 322 7 137 208 48 72 162 290), lower := (rows 37 322 7 137 208 48 72 128 256), losses := [] }

theorem u9977 : Upper (D 7) (R 7) [36,320,3,129,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9977 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9978 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 136, targets := 96 },{ cop := 3, region := 370, targets := 1 }], pairs := [(1,0),(3,5),(3,6)], upper := (rows 37 322 7 137 208 48 96 138 266), lower := (rows 37 322 7 137 208 48 96 128 256), losses := [] }

theorem u9978 : Upper (D 7) (R 7) [36,320,3,129,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9978 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9979 : PairBound 9 := { available := 40, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 322 7 138 208 48 65 168 296), lower := (rows 37 322 7 138 208 48 65 128 256), losses := [] }

theorem u9979 : Upper (D 7) (R 7) [36,320,3,130,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9979 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9980 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 322 7 138 208 48 72 161 289), lower := (rows 37 322 7 138 208 48 72 128 256), losses := [] }

theorem u9980 : Upper (D 7) (R 7) [36,320,3,130,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9980 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9981 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 136, targets := 96 },{ cop := 3, region := 112, targets := 1 }], pairs := [(3,5),(3,6),(4,0)], upper := (rows 37 322 7 138 208 48 96 137 265), lower := (rows 37 322 7 138 208 48 96 128 256), losses := [] }

theorem u9981 : Upper (D 7) (R 7) [36,320,3,130,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9981 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9982 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 37 322 13 26 112 160 65 130 386), lower := (rows 37 322 13 26 112 160 65 128 256), losses := [] }

theorem u9982 : Upper (D 7) (R 7) [36,320,9,18,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9983 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 13 26 112 160 66 129 385), lower := (rows 37 322 13 26 112 160 66 128 256), losses := [] }

theorem u9983 : Upper (D 7) (R 7) [36,320,9,18,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9984 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 322 13 26 112 160 192 131 259), lower := (rows 37 322 13 26 112 160 192 128 256), losses := [] }

theorem u9984 : Upper (D 7) (R 7) [36,320,9,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9985 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 13 88 50 160 65 130 386), lower := (rows 37 322 13 88 50 160 65 128 256), losses := [] }

theorem u9985 : Upper (D 7) (R 7) [36,320,9,80,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9986 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 13 88 50 160 66 129 385), lower := (rows 37 322 13 88 50 160 66 128 256), losses := [] }

theorem u9986 : Upper (D 7) (R 7) [36,320,9,80,34,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9987 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(1,5),(3,0),(4,0)], upper := (rows 37 322 13 88 50 160 192 131 259), lower := (rows 37 322 13 88 50 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 26 18 224 224 128 256), good := (rows 100 378 12 120 122 224 224 224 256) },{ target := 1, region := (rows 25 0 28 24 16 224 224 128 256), good := (rows 101 352 13 125 125 224 224 224 256) }] }

theorem u9987 : Upper (D 7) (R 7) [36,320,9,80,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9988 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,6)], upper := (rows 37 322 13 88 145 34 66 160 416), lower := (rows 37 322 13 88 145 34 66 128 256), losses := [] }

theorem u9988 : Upper (D 7) (R 7) [36,320,9,80,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9989 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 3, region := 386, targets := 32 },{ cop := 8, region := 98, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 322 13 88 145 34 96 130 386), lower := (rows 37 322 13 88 145 34 96 128 256), losses := [] }

theorem u9989 : Upper (D 7) (R 7) [36,320,9,80,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9990 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 322 13 88 145 34 192 162 290), lower := (rows 37 322 13 88 145 34 192 128 256), losses := [] }

theorem u9990 : Upper (D 7) (R 7) [36,320,9,80,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9991 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 13 88 176 34 65 130 386), lower := (rows 37 322 13 88 176 34 65 128 256), losses := [] }

theorem u9991 : Upper (D 7) (R 7) [36,320,9,80,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9992 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 8, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,6)], upper := (rows 37 322 13 88 176 34 66 129 385), lower := (rows 37 322 13 88 176 34 66 128 256), losses := [] }

theorem u9992 : Upper (D 7) (R 7) [36,320,9,80,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9993 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 77, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 322 13 88 176 34 192 131 259), lower := (rows 37 322 13 88 176 34 192 128 256), losses := [] }

theorem u9993 : Upper (D 7) (R 7) [36,320,9,80,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9994 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 117, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 322 13 138 81 48 66 160 416), lower := (rows 37 322 13 138 81 48 66 128 256), losses := [] }

theorem u9994 : Upper (D 7) (R 7) [36,320,9,130,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9994 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9995 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 117, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 322 13 138 81 48 96 130 386), lower := (rows 37 322 13 138 81 48 96 128 256), losses := [] }

theorem u9995 : Upper (D 7) (R 7) [36,320,9,130,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9995 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9996 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 117, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 322 13 138 81 48 192 162 290), lower := (rows 37 322 13 138 81 48 192 128 256), losses := [] }

theorem u9996 : Upper (D 7) (R 7) [36,320,9,130,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9996 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9997 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 117, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 322 13 138 208 48 65 162 290), lower := (rows 37 322 13 138 208 48 65 128 256), losses := [] }

theorem u9997 : Upper (D 7) (R 7) [36,320,9,130,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9997 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9998 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 13 138 208 48 66 161 289), lower := (rows 37 322 13 138 208 48 66 128 256), losses := [] }

theorem u9998 : Upper (D 7) (R 7) [36,320,9,130,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9998 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9999 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 117, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 322 13 138 208 48 96 131 259), lower := (rows 37 322 13 138 208 48 96 128 256), losses := [] }

theorem u9999 : Upper (D 7) (R 7) [36,320,9,130,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9999 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10000 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 8, region := 66, targets := 32 },{ cop := 8, region := 66, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 322 13 152 19 96 66 160 416), lower := (rows 37 322 13 152 19 96 66 128 256), losses := [] }

theorem u10000 : Upper (D 7) (R 7) [36,320,9,144,3,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10001 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 13 152 19 96 96 130 386), lower := (rows 37 322 13 152 19 96 96 128 256), losses := [] }

theorem u10001 : Upper (D 7) (R 7) [36,320,9,144,3,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10002 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 101, targets := 2 },{ cop := 4, region := 490, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 322 13 152 19 96 192 162 290), lower := (rows 37 322 13 152 19 96 192 128 256), losses := [] }

theorem u10002 : Upper (D 7) (R 7) [36,320,9,144,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10003 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 8, region := 66, targets := 32 },{ cop := 8, region := 66, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 322 13 152 81 34 66 160 416), lower := (rows 37 322 13 152 81 34 66 128 256), losses := [] }

theorem u10003 : Upper (D 7) (R 7) [36,320,9,144,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10004 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 322 13 152 81 34 96 130 386), lower := (rows 37 322 13 152 81 34 96 128 256), losses := [] }

theorem u10004 : Upper (D 7) (R 7) [36,320,9,144,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10005 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 290, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,1)], upper := (rows 37 322 13 152 81 34 192 162 290), lower := (rows 37 322 13 152 81 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 32 200 128 256), good := (rows 53 320 93 216 81 32 192 192 256) }] }

theorem u10005 : Upper (D 7) (R 7) [36,320,9,144,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10006 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 37 322 13 152 112 34 65 130 386), lower := (rows 37 322 13 152 112 34 65 128 256), losses := [] }

theorem u10006 : Upper (D 7) (R 7) [36,320,9,144,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10007 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 141, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 13 152 112 34 66 129 385), lower := (rows 37 322 13 152 112 34 66 128 256), losses := [] }

theorem u10007 : Upper (D 7) (R 7) [36,320,9,144,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10008 : Route 9 := (fun mask => (mask,id))

def c10008 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10008 : Upper (D 7) (R 7) [36,320,9,144,96,2,128] 13 := by
  apply FastRouting.sound _ _ [36,320,9,144,96,2,128] 13 (by decide) (choices 1) [1,2] r10008 c10008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u777
  · exact u778

def b10009 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 37 322 13 200 19 34 80 160 416), lower := (rows 37 322 13 200 19 34 80 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 80 161 289), good := (rows 421 320 397 200 477 416 92 128 256) }] }

theorem u10009 : Upper (D 7) (R 7) [36,320,9,192,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10009 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10010 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 8, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(2,1),(3,0)], upper := (rows 37 322 13 200 19 34 96 144 400), lower := (rows 37 322 13 200 19 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 97 144 272), good := (rows 101 320 77 200 477 96 96 128 256) }] }

theorem u10010 : Upper (D 7) (R 7) [36,320,9,192,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10011 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 322 13 200 19 34 192 176 304), lower := (rows 37 322 13 200 19 34 192 128 256), losses := [] }

theorem u10011 : Upper (D 7) (R 7) [36,320,9,192,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10012 : PairBound 9 := { available := 160, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 13 200 19 48 66 160 416), lower := (rows 37 322 13 200 19 48 66 128 256), losses := [] }

theorem u10012 : Upper (D 7) (R 7) [36,320,9,192,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10012 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10013 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 322 13 200 19 48 96 130 386), lower := (rows 37 322 13 200 19 48 96 128 256), losses := [] }

theorem u10013 : Upper (D 7) (R 7) [36,320,9,192,3,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10013 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10014 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 13 200 19 48 192 162 290), lower := (rows 37 322 13 200 19 48 192 128 256), losses := [] }

theorem u10014 : Upper (D 7) (R 7) [36,320,9,192,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10014 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10015 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,6)], upper := (rows 37 322 13 200 145 34 66 176 304), lower := (rows 37 322 13 200 145 34 66 128 256), losses := [] }

theorem u10015 : Upper (D 7) (R 7) [36,320,9,192,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10016 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 37 322 13 200 145 34 80 162 290), lower := (rows 37 322 13 200 145 34 80 128 256), losses := [] }

theorem u10016 : Upper (D 7) (R 7) [36,320,9,192,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10016 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10017 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(2,1),(3,0)], upper := (rows 37 322 13 200 145 34 96 146 274), lower := (rows 37 322 13 200 145 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 97 128 256), good := (rows 101 320 77 200 221 96 96 128 256) }] }

theorem u10017 : Upper (D 7) (R 7) [36,320,9,192,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10018 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 176, targets := 64 }], pairs := [(1,0),(3,0),(4,0),(4,6)], upper := (rows 37 322 13 200 146 34 65 176 304), lower := (rows 37 322 13 200 146 34 65 128 256), losses := [] }

theorem u10018 : Upper (D 7) (R 7) [36,320,9,192,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10019 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 13 200 146 34 80 161 289), lower := (rows 37 322 13 200 146 34 80 128 256), losses := [] }

theorem u10019 : Upper (D 7) (R 7) [36,320,9,192,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10019 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10019
end Delivery.IrregularNine14.P07
