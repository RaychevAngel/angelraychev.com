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

def b10080 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 8, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 37 322 28 137 208 34 96 131 259), lower := (rows 37 322 28 137 208 34 96 128 256), losses := [{ target := 0, region := (rows 0 258 12 8 24 290 355 128 256), good := (rows 100 354 28 220 208 98 96 128 354) }] }

theorem u10080 : Upper (D 7) (R 7) [36,320,24,129,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10081 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 322 69 11 50 160 72 144 400), lower := (rows 37 322 69 11 50 160 72 128 256), losses := [] }

theorem u10081 : Upper (D 7) (R 7) [36,320,65,3,34,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10081 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10082 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 69 11 50 160 80 136 392), lower := (rows 37 322 69 11 50 160 80 128 256), losses := [] }

theorem u10082 : Upper (D 7) (R 7) [36,320,65,3,34,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10082 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10083 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 322 69 11 50 160 192 152 280), lower := (rows 37 322 69 11 50 160 192 128 256), losses := [] }

theorem u10083 : Upper (D 7) (R 7) [36,320,65,3,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10084 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 322 69 11 146 160 72 176 304), lower := (rows 37 322 69 11 146 160 72 128 256), losses := [] }

theorem u10084 : Upper (D 7) (R 7) [36,320,65,3,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10084 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10085 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 37 322 69 11 146 160 80 168 296), lower := (rows 37 322 69 11 146 160 80 128 256), losses := [] }

theorem u10085 : Upper (D 7) (R 7) [36,320,65,3,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10085 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10086 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 69 11 146 160 96 152 280), lower := (rows 37 322 69 11 146 160 96 128 256), losses := [] }

theorem u10086 : Upper (D 7) (R 7) [36,320,65,3,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10087 : PairBound 9 := { available := 48, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 3, region := 176, targets := 2 }], pairs := [(1,0),(1,5),(1,7),(4,1)], upper := (rows 37 322 69 11 152 160 66 176 304), lower := (rows 37 322 69 11 152 160 66 128 256), losses := [] }

theorem u10087 : Upper (D 7) (R 7) [36,320,65,3,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10088 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 37 322 69 11 152 160 80 162 290), lower := (rows 37 322 69 11 152 160 80 128 256), losses := [] }

theorem u10088 : Upper (D 7) (R 7) [36,320,65,3,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10088 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10089 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 69 11 152 160 96 146 274), lower := (rows 37 322 69 11 152 160 96 128 256), losses := [] }

theorem u10089 : Upper (D 7) (R 7) [36,320,65,3,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10090 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 165, targets := 2 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 322 69 25 26 160 66 160 416), lower := (rows 37 322 69 25 26 160 66 128 256), losses := [] }

theorem u10090 : Upper (D 7) (R 7) [36,320,65,17,10,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10091 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 69 25 26 160 96 130 386), lower := (rows 37 322 69 25 26 160 96 128 256), losses := [] }

theorem u10091 : Upper (D 7) (R 7) [36,320,65,17,10,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10092 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 322 69 25 26 160 192 162 290), lower := (rows 37 322 69 25 26 160 192 128 256), losses := [] }

theorem u10092 : Upper (D 7) (R 7) [36,320,65,17,10,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10093 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 69 25 146 40 66 160 416), lower := (rows 37 322 69 25 146 40 66 128 256), losses := [] }

theorem u10093 : Upper (D 7) (R 7) [36,320,65,17,130,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10093 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10094 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 109, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 322 69 25 146 40 96 130 386), lower := (rows 37 322 69 25 146 40 96 128 256), losses := [] }

theorem u10094 : Upper (D 7) (R 7) [36,320,65,17,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10094 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10095 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 322 69 25 146 40 192 162 290), lower := (rows 37 322 69 25 146 40 192 128 256), losses := [] }

theorem u10095 : Upper (D 7) (R 7) [36,320,65,17,130,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10095 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10096 : PairBound 9 := { available := 40, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 37 322 69 25 146 160 66 168 296), lower := (rows 37 322 69 25 146 160 66 128 256), losses := [] }

theorem u10096 : Upper (D 7) (R 7) [36,320,65,17,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10097 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 37 322 69 25 146 160 72 162 290), lower := (rows 37 322 69 25 146 160 72 128 256), losses := [] }

theorem u10097 : Upper (D 7) (R 7) [36,320,65,17,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10097 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10098 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 69 25 146 160 96 138 266), lower := (rows 37 322 69 25 146 160 96 128 256), losses := [] }

theorem u10098 : Upper (D 7) (R 7) [36,320,65,17,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10099 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 184, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 322 69 26 56 160 65 130 386), lower := (rows 37 322 69 26 56 160 65 128 256), losses := [] }

theorem u10099 : Upper (D 7) (R 7) [36,320,65,18,40,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10100 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 1, region := 165, targets := 2 }], pairs := [(0,1),(1,0),(1,5),(1,7)], upper := (rows 37 322 69 26 56 160 66 129 385), lower := (rows 37 322 69 26 56 160 66 128 256), losses := [] }

theorem u10100 : Upper (D 7) (R 7) [36,320,65,18,40,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10101 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,5),(2,1),(2,5)], upper := (rows 37 322 69 26 56 160 192 131 259), lower := (rows 37 322 69 26 56 160 192 128 256), losses := [] }

theorem u10101 : Upper (D 7) (R 7) [36,320,65,18,40,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10102 : PairBound 9 := { available := 160, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 69 26 145 40 66 160 416), lower := (rows 37 322 69 26 145 40 66 128 256), losses := [] }

theorem u10102 : Upper (D 7) (R 7) [36,320,65,18,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10102 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10103 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 322 69 26 145 40 96 130 386), lower := (rows 37 322 69 26 145 40 96 128 256), losses := [] }

theorem u10103 : Upper (D 7) (R 7) [36,320,65,18,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10103 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10104 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 68, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 37 322 69 26 145 40 192 162 290), lower := (rows 37 322 69 26 145 40 192 128 256), losses := [] }

theorem u10104 : Upper (D 7) (R 7) [36,320,65,18,129,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10104 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10105 : PairBound 9 := { available := 40, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 322 69 26 145 160 66 168 296), lower := (rows 37 322 69 26 145 160 66 128 256), losses := [] }

theorem u10105 : Upper (D 7) (R 7) [36,320,65,18,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10106 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 362, targets := 1 }], pairs := [(0,1),(1,0),(3,0)], upper := (rows 37 322 69 26 145 160 72 162 290), lower := (rows 37 322 69 26 145 160 72 128 256), losses := [{ target := 1, region := (rows 9 0 76 8 16 176 72 128 256), good := (rows 37 324 69 125 177 160 77 160 256) }] }

theorem u10106 : Upper (D 7) (R 7) [36,320,65,18,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10106 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10107 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 69 26 145 160 96 138 266), lower := (rows 37 322 69 26 145 160 96 128 256), losses := [] }

theorem u10107 : Upper (D 7) (R 7) [36,320,65,18,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10108 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 184, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 322 69 26 152 160 65 162 290), lower := (rows 37 322 69 26 152 160 65 128 256), losses := [] }

theorem u10108 : Upper (D 7) (R 7) [36,320,65,18,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10109 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 1, region := 165, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 322 69 26 152 160 66 161 289), lower := (rows 37 322 69 26 152 160 66 128 256), losses := [] }

theorem u10109 : Upper (D 7) (R 7) [36,320,65,18,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10110 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 5, region := 69, targets := 128 }], pairs := [(0,7),(1,5),(3,5),(4,5)], upper := (rows 37 322 69 26 152 160 96 131 259), lower := (rows 37 322 69 26 152 160 96 128 256), losses := [] }

theorem u10110 : Upper (D 7) (R 7) [36,320,65,18,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10111 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 184, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 322 69 26 176 34 65 136 392), lower := (rows 37 322 69 26 176 34 65 128 256), losses := [] }

theorem u10111 : Upper (D 7) (R 7) [36,320,65,18,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10112 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(4,1),(4,6)], upper := (rows 37 322 69 26 176 34 72 129 385), lower := (rows 37 322 69 26 176 34 72 128 256), losses := [] }

theorem u10112 : Upper (D 7) (R 7) [36,320,65,18,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10112 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10113 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 69, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 322 69 26 176 34 192 137 265), lower := (rows 37 322 69 26 176 34 192 128 256), losses := [] }

theorem u10113 : Upper (D 7) (R 7) [36,320,65,18,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10114 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 184, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 322 69 26 176 40 65 130 386), lower := (rows 37 322 69 26 176 40 65 128 256), losses := [] }

theorem u10114 : Upper (D 7) (R 7) [36,320,65,18,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10114 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10115 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 69 26 176 40 66 129 385), lower := (rows 37 322 69 26 176 40 66 128 256), losses := [] }

theorem u10115 : Upper (D 7) (R 7) [36,320,65,18,160,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10115 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10116 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 4, region := 69, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 37 322 69 26 176 40 192 131 259), lower := (rows 37 322 69 26 176 40 192 128 256), losses := [] }

theorem u10116 : Upper (D 7) (R 7) [36,320,65,18,160,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10116 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10117 : PairBound 9 := { available := 24, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(1,7)], upper := (rows 37 322 69 42 145 160 66 152 280), lower := (rows 37 322 69 42 145 160 66 128 256), losses := [] }

theorem u10117 : Upper (D 7) (R 7) [36,320,65,34,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10118 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 322 69 42 145 160 72 146 274), lower := (rows 37 322 69 42 145 160 72 128 256), losses := [] }

theorem u10118 : Upper (D 7) (R 7) [36,320,65,34,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10118 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10119 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 85, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 322 69 42 145 160 80 138 266), lower := (rows 37 322 69 42 145 160 80 128 256), losses := [] }

theorem u10119 : Upper (D 7) (R 7) [36,320,65,34,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10119 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10120 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 184, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 322 69 42 146 160 65 152 280), lower := (rows 37 322 69 42 146 160 65 128 256), losses := [] }

theorem u10120 : Upper (D 7) (R 7) [36,320,65,34,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10121 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 322 69 42 146 160 72 145 273), lower := (rows 37 322 69 42 146 160 72 128 256), losses := [] }

theorem u10121 : Upper (D 7) (R 7) [36,320,65,34,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10121 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10122 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 101, targets := 2 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,1),(2,1),(3,0)], upper := (rows 37 322 69 42 146 160 80 137 265), lower := (rows 37 322 69 42 146 160 80 128 256), losses := [] }

theorem u10122 : Upper (D 7) (R 7) [36,320,65,34,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10122 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10123 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 184, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 322 69 42 152 48 65 130 386), lower := (rows 37 322 69 42 152 48 65 128 256), losses := [] }

theorem u10123 : Upper (D 7) (R 7) [36,320,65,34,136,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10123 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10124 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 69 42 152 48 66 129 385), lower := (rows 37 322 69 42 152 48 66 128 256), losses := [] }

theorem u10124 : Upper (D 7) (R 7) [36,320,65,34,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10124 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10125 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 4, region := 101, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 37 322 69 42 152 48 192 131 259), lower := (rows 37 322 69 42 152 48 192 128 256), losses := [] }

theorem u10125 : Upper (D 7) (R 7) [36,320,65,34,136,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10125 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10126 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 184, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 322 69 42 152 160 65 146 274), lower := (rows 37 322 69 42 152 160 65 128 256), losses := [] }

theorem u10126 : Upper (D 7) (R 7) [36,320,65,34,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10127 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 66, targets := 161 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(1,7)], upper := (rows 37 322 69 42 152 160 66 145 273), lower := (rows 37 322 69 42 152 160 66 128 256), losses := [] }

theorem u10127 : Upper (D 7) (R 7) [36,320,65,34,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10128 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 101, targets := 2 },{ cop := 2, region := 258, targets := 32 }], pairs := [(0,1),(1,5),(2,1)], upper := (rows 37 322 69 42 152 160 80 131 259), lower := (rows 37 322 69 42 152 160 80 128 256), losses := [] }

theorem u10128 : Upper (D 7) (R 7) [36,320,65,34,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10128 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10129 : PairBound 9 := { available := 48, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 69 137 146 40 66 176 304), lower := (rows 37 322 69 137 146 40 66 128 256), losses := [] }

theorem u10129 : Upper (D 7) (R 7) [36,320,65,129,130,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10129 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10130 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 37 322 69 137 146 40 80 162 290), lower := (rows 37 322 69 137 146 40 80 128 256), losses := [] }

theorem u10130 : Upper (D 7) (R 7) [36,320,65,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10130 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10131 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 322 69 137 146 40 96 146 274), lower := (rows 37 322 69 137 146 40 96 128 256), losses := [] }

theorem u10131 : Upper (D 7) (R 7) [36,320,65,129,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10131 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10132 : PairBound 9 := { available := 40, camps := [{ cop := 8, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 322 69 137 146 48 66 168 296), lower := (rows 37 322 69 137 146 48 66 128 256), losses := [] }

theorem u10132 : Upper (D 7) (R 7) [36,320,65,129,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10132 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10133 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 68, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 37 322 69 137 146 48 72 162 290), lower := (rows 37 322 69 137 146 48 72 128 256), losses := [] }

theorem u10133 : Upper (D 7) (R 7) [36,320,65,129,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10133 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10134 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 322 69 137 146 48 96 138 266), lower := (rows 37 322 69 137 146 48 96 128 256), losses := [] }

theorem u10134 : Upper (D 7) (R 7) [36,320,65,129,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10134 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10135 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 1, region := 176, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(4,0)], upper := (rows 37 322 76 11 50 160 65 144 400), lower := (rows 37 322 76 11 50 160 65 128 256), losses := [] }

theorem u10135 : Upper (D 7) (R 7) [36,320,72,3,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10136 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 322 76 11 50 160 80 129 385), lower := (rows 37 322 76 11 50 160 80 128 256), losses := [] }

theorem u10136 : Upper (D 7) (R 7) [36,320,72,3,34,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10136 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10137 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(0,1),(0,6),(4,0),(4,6)], upper := (rows 37 322 76 11 50 160 192 145 273), lower := (rows 37 322 76 11 50 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 100 370 108 26 114 224 224 224 256) },{ target := 1, region := (rows 5 0 4 8 16 224 224 128 256), good := (rows 101 352 109 9 112 224 224 224 256) },{ target := 6, region := (rows 5 2 4 8 26 237 0 140 268), good := (rows 421 306 445 443 50 160 160 160 256) }] }

theorem u10137 : Upper (D 7) (R 7) [36,320,72,3,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10138 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 322 76 11 145 160 66 176 304), lower := (rows 37 322 76 11 145 160 66 128 256), losses := [] }

theorem u10138 : Upper (D 7) (R 7) [36,320,72,3,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10139 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 418, targets := 1 },{ cop := 3, region := 176, targets := 64 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 37 322 76 11 145 160 80 162 290), lower := (rows 37 322 76 11 145 160 80 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 28 190 0 138 266), good := (rows 53 418 445 443 177 160 48 160 256) }] }

theorem u10139 : Upper (D 7) (R 7) [36,320,72,3,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10139 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10139
end Delivery.IrregularNine14.P07
