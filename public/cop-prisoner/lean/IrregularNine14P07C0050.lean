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

def b3000 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 290 69 137 176 96 72 146 274), lower := (rows 7 290 69 137 176 96 72 128 256), losses := [] }

theorem u3000 : Upper (D 7) (R 7) [6,288,65,129,160,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3000 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3001 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 136, targets := 96 },{ cop := 3, region := 370, targets := 1 }], pairs := [(1,0),(3,5),(3,6)], upper := (rows 7 290 69 137 176 96 80 138 266), lower := (rows 7 290 69 137 176 96 80 128 256), losses := [] }

theorem u3001 : Upper (D 7) (R 7) [6,288,65,129,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3001 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3002 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 69 137 208 40 66 176 304), lower := (rows 7 290 69 137 208 40 66 128 256), losses := [] }

theorem u3002 : Upper (D 7) (R 7) [6,288,65,129,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3002 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3003 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 290 69 137 208 40 80 162 290), lower := (rows 7 290 69 137 208 40 80 128 256), losses := [] }

theorem u3003 : Upper (D 7) (R 7) [6,288,65,129,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3003 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3004 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 7 290 69 137 208 40 96 146 274), lower := (rows 7 290 69 137 208 40 96 128 256), losses := [] }

theorem u3004 : Upper (D 7) (R 7) [6,288,65,129,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3004 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3005 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 69 137 208 48 66 168 296), lower := (rows 7 290 69 137 208 48 66 128 256), losses := [] }

theorem u3005 : Upper (D 7) (R 7) [6,288,65,129,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3005 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3006 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 290 69 137 208 48 72 162 290), lower := (rows 7 290 69 137 208 48 72 128 256), losses := [] }

theorem u3006 : Upper (D 7) (R 7) [6,288,65,129,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3006 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3007 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 136, targets := 96 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(3,5),(3,6)], upper := (rows 7 290 69 137 208 48 96 138 266), lower := (rows 7 290 69 137 208 48 96 128 256), losses := [] }

theorem u3007 : Upper (D 7) (R 7) [6,288,65,129,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3007 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3008 : PairBound 9 := { available := 80, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 290 69 138 176 33 72 208 336), lower := (rows 7 290 69 138 176 33 72 128 256), losses := [] }

theorem u3008 : Upper (D 7) (R 7) [6,288,65,130,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3008 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3009 : PairBound 9 := { available := 72, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 290 69 138 176 33 80 200 328), lower := (rows 7 290 69 138 176 33 80 128 256), losses := [] }

theorem u3009 : Upper (D 7) (R 7) [6,288,65,130,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3009 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3010 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 290 69 138 176 96 65 152 280), lower := (rows 7 290 69 138 176 96 65 128 256), losses := [] }

theorem u3010 : Upper (D 7) (R 7) [6,288,65,130,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3011 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 112, targets := 3 },{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(4,0),(4,1)], upper := (rows 7 290 69 138 176 96 72 145 273), lower := (rows 7 290 69 138 176 96 72 128 256), losses := [] }

theorem u3011 : Upper (D 7) (R 7) [6,288,65,130,160,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3011 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3012 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 96 },{ cop := 3, region := 112, targets := 1 }], pairs := [(3,5),(3,6),(4,0)], upper := (rows 7 290 69 138 176 96 80 137 265), lower := (rows 7 290 69 138 176 96 80 128 256), losses := [] }

theorem u3012 : Upper (D 7) (R 7) [6,288,65,130,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3012 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3013 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 85, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 290 69 138 208 33 72 176 304), lower := (rows 7 290 69 138 208 33 72 128 256), losses := [] }

theorem u3013 : Upper (D 7) (R 7) [6,288,65,130,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3013 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3014 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 290 69 138 208 33 80 168 296), lower := (rows 7 290 69 138 208 33 80 128 256), losses := [] }

theorem u3014 : Upper (D 7) (R 7) [6,288,65,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3014 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3015 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 290 69 138 208 33 96 152 280), lower := (rows 7 290 69 138 208 33 96 128 256), losses := [] }

theorem u3015 : Upper (D 7) (R 7) [6,288,65,130,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3016 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 69 138 208 40 65 176 304), lower := (rows 7 290 69 138 208 40 65 128 256), losses := [] }

theorem u3016 : Upper (D 7) (R 7) [6,288,65,130,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3016 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3017 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 290 69 138 208 40 80 161 289), lower := (rows 7 290 69 138 208 40 80 128 256), losses := [] }

theorem u3017 : Upper (D 7) (R 7) [6,288,65,130,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3017 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3018 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 144, targets := 2 }], pairs := [(0,7),(2,7),(4,1)], upper := (rows 7 290 69 138 208 40 96 145 273), lower := (rows 7 290 69 138 208 40 96 128 256), losses := [] }

theorem u3018 : Upper (D 7) (R 7) [6,288,65,130,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3018 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3019 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 290 69 138 208 48 65 168 296), lower := (rows 7 290 69 138 208 48 65 128 256), losses := [] }

theorem u3019 : Upper (D 7) (R 7) [6,288,65,130,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3019 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3020 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 290 69 138 208 48 72 161 289), lower := (rows 7 290 69 138 208 48 72 128 256), losses := [] }

theorem u3020 : Upper (D 7) (R 7) [6,288,65,130,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3020 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3021 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 96 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(3,5),(3,6)], upper := (rows 7 290 69 138 208 48 96 137 265), lower := (rows 7 290 69 138 208 48 96 128 256), losses := [] }

theorem u3021 : Upper (D 7) (R 7) [6,288,65,130,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3021 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3022 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 290 69 168 208 33 66 152 280), lower := (rows 7 290 69 168 208 33 66 128 256), losses := [] }

theorem u3022 : Upper (D 7) (R 7) [6,288,65,160,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3023 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 69 168 208 33 72 146 274), lower := (rows 7 290 69 168 208 33 72 128 256), losses := [] }

theorem u3023 : Upper (D 7) (R 7) [6,288,65,160,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3023 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3024 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 290 69 168 208 33 80 138 266), lower := (rows 7 290 69 168 208 33 80 128 256), losses := [] }

theorem u3024 : Upper (D 7) (R 7) [6,288,65,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3024 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3025 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 290 69 168 208 34 65 152 280), lower := (rows 7 290 69 168 208 34 65 128 256), losses := [] }

theorem u3025 : Upper (D 7) (R 7) [6,288,65,160,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3026 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 290 69 168 208 34 72 145 273), lower := (rows 7 290 69 168 208 34 72 128 256), losses := [] }

theorem u3026 : Upper (D 7) (R 7) [6,288,65,160,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3026 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3027 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 290 69 168 208 34 80 137 265), lower := (rows 7 290 69 168 208 34 80 128 256), losses := [] }

theorem u3027 : Upper (D 7) (R 7) [6,288,65,160,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3027 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3028 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 76 25 112 160 65 130 386), lower := (rows 7 290 76 25 112 160 65 128 256), losses := [] }

theorem u3028 : Upper (D 7) (R 7) [6,288,72,17,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3029 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 76 25 112 160 66 129 385), lower := (rows 7 290 76 25 112 160 66 128 256), losses := [] }

theorem u3029 : Upper (D 7) (R 7) [6,288,72,17,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3030 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 76 25 112 160 192 131 259), lower := (rows 7 290 76 25 112 160 192 128 256), losses := [] }

theorem u3030 : Upper (D 7) (R 7) [6,288,72,17,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3031 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 5, region := 450, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 7 290 76 25 146 33 96 192 448), lower := (rows 7 290 76 25 146 33 96 128 256), losses := [] }

theorem u3031 : Upper (D 7) (R 7) [6,288,72,17,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3032 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 77, targets := 32 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(3,5)], upper := (rows 7 290 76 25 146 33 192 224 352), lower := (rows 7 290 76 25 146 33 192 128 256), losses := [] }

theorem u3032 : Upper (D 7) (R 7) [6,288,72,17,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3033 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 290 76 25 146 96 65 160 416), lower := (rows 7 290 76 25 146 96 65 128 256), losses := [] }

theorem u3033 : Upper (D 7) (R 7) [6,288,72,17,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3034 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 152, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 290 76 25 146 96 96 129 385), lower := (rows 7 290 76 25 146 96 96 128 256), losses := [] }

theorem u3034 : Upper (D 7) (R 7) [6,288,72,17,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3035 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 77, targets := 32 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(3,5)], upper := (rows 7 290 76 25 146 96 192 161 289), lower := (rows 7 290 76 25 146 96 192 128 256), losses := [] }

theorem u3035 : Upper (D 7) (R 7) [6,288,72,17,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3036 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 77, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 76 25 146 160 65 224 352), lower := (rows 7 290 76 25 146 160 65 128 256), losses := [] }

theorem u3036 : Upper (D 7) (R 7) [6,288,72,17,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3037 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 228, targets := 2 }], pairs := [(0,7),(2,0),(2,1),(2,7)], upper := (rows 7 290 76 25 146 160 96 193 321), lower := (rows 7 290 76 25 146 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 250 128 256), good := (rows 70 354 76 124 242 224 96 224 256) },{ target := 7, region := (rows 17 2 20 24 16 32 98 0 273), good := (rows 327 354 76 285 351 96 96 0 256) }] }

theorem u3037 : Upper (D 7) (R 7) [6,288,72,17,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3038 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 402, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 290 76 25 176 96 65 130 386), lower := (rows 7 290 76 25 176 96 65 128 256), losses := [] }

theorem u3038 : Upper (D 7) (R 7) [6,288,72,17,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3039 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 98, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(3,1)], upper := (rows 7 290 76 25 176 96 66 129 385), lower := (rows 7 290 76 25 176 96 66 128 256), losses := [{ target := 0, region := (rows 0 258 12 8 16 367 323 128 256), good := (rows 102 354 108 124 176 96 98 128 354) },{ target := 1, region := (rows 1 0 4 9 21 100 64 137 265), good := (rows 445 288 508 409 176 96 96 128 256) }] }

theorem u3039 : Upper (D 7) (R 7) [6,288,72,17,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3040 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 6, region := 48, targets := 3 }], pairs := [(0,7),(1,7),(4,0),(4,1)], upper := (rows 7 290 76 25 176 96 192 131 259), lower := (rows 7 290 76 25 176 96 192 128 256), losses := [] }

theorem u3040 : Upper (D 7) (R 7) [6,288,72,17,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3041 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 68, targets := 162 },{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(2,7)], upper := (rows 7 290 76 25 208 160 65 162 290), lower := (rows 7 290 76 25 208 160 65 128 256), losses := [] }

theorem u3041 : Upper (D 7) (R 7) [6,288,72,17,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3042 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(3,1)], upper := (rows 7 290 76 25 208 160 66 161 289), lower := (rows 7 290 76 25 208 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 67 128 256), good := (rows 70 354 76 124 240 160 66 160 256) },{ target := 1, region := (rows 1 0 4 9 20 189 64 137 265), good := (rows 445 288 508 441 240 160 64 160 256) }] }

theorem u3042 : Upper (D 7) (R 7) [6,288,72,17,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3043 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 5, region := 80, targets := 3 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 7 290 76 25 208 160 96 131 259), lower := (rows 7 290 76 25 208 160 96 128 256), losses := [] }

theorem u3043 : Upper (D 7) (R 7) [6,288,72,17,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3044 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 69, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 76 26 145 96 65 160 416), lower := (rows 7 290 76 26 145 96 65 128 256), losses := [] }

theorem u3044 : Upper (D 7) (R 7) [6,288,72,18,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3045 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 152, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 290 76 26 145 96 96 129 385), lower := (rows 7 290 76 26 145 96 96 128 256), losses := [] }

theorem u3045 : Upper (D 7) (R 7) [6,288,72,18,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3046 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,7),(1,7),(2,0),(4,1)], upper := (rows 7 290 76 26 145 96 192 161 289), lower := (rows 7 290 76 26 145 96 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 252 208 128 256), good := (rows 38 290 108 126 240 96 224 224 256) }] }

theorem u3046 : Upper (D 7) (R 7) [6,288,72,18,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3047 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 76 26 145 160 65 224 352), lower := (rows 7 290 76 26 145 160 65 128 256), losses := [] }

theorem u3047 : Upper (D 7) (R 7) [6,288,72,18,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3048 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 240, targets := 2 }], pairs := [(0,7),(2,0),(2,1),(4,1)], upper := (rows 7 290 76 26 145 160 96 193 321), lower := (rows 7 290 76 26 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 250 128 256), good := (rows 70 354 76 126 240 224 96 224 256) },{ target := 1, region := (rows 1 0 12 8 17 185 255 145 273), good := (rows 501 352 108 508 497 224 96 224 256) },{ target := 7, region := (rows 9 2 12 8 16 32 98 0 269), good := (rows 327 354 333 351 273 96 96 0 256) }] }

theorem u3048 : Upper (D 7) (R 7) [6,288,72,18,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3049 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 69, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 76 26 176 33 65 192 448), lower := (rows 7 290 76 26 176 33 65 128 256), losses := [] }

theorem u3049 : Upper (D 7) (R 7) [6,288,72,18,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3050 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,5)], upper := (rows 7 290 76 26 176 33 192 193 321), lower := (rows 7 290 76 26 176 33 192 128 256), losses := [] }

theorem u3050 : Upper (D 7) (R 7) [6,288,72,18,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3051 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 69, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 76 26 176 96 65 129 385), lower := (rows 7 290 76 26 176 96 65 128 256), losses := [] }

theorem u3051 : Upper (D 7) (R 7) [6,288,72,18,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3052 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,5)], upper := (rows 7 290 76 26 176 96 192 129 257), lower := (rows 7 290 76 26 176 96 192 128 256), losses := [] }

theorem u3052 : Upper (D 7) (R 7) [6,288,72,18,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3053 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(0,6),(1,6),(2,5)], upper := (rows 7 290 76 26 208 33 65 160 416), lower := (rows 7 290 76 26 208 33 65 128 256), losses := [] }

theorem u3053 : Upper (D 7) (R 7) [6,288,72,18,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3054 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(2,7)], upper := (rows 7 290 76 26 208 33 96 129 385), lower := (rows 7 290 76 26 208 33 96 128 256), losses := [] }

theorem u3054 : Upper (D 7) (R 7) [6,288,72,18,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3055 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 76 26 208 33 192 161 289), lower := (rows 7 290 76 26 208 33 192 128 256), losses := [] }

theorem u3055 : Upper (D 7) (R 7) [6,288,72,18,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3056 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 76 26 208 160 65 161 289), lower := (rows 7 290 76 26 208 160 65 128 256), losses := [] }

theorem u3056 : Upper (D 7) (R 7) [6,288,72,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3057 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 5, region := 80, targets := 3 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 7 290 76 26 208 160 96 129 257), lower := (rows 7 290 76 26 208 160 96 128 256), losses := [] }

theorem u3057 : Upper (D 7) (R 7) [6,288,72,18,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3058 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 290 76 41 82 160 65 144 400), lower := (rows 7 290 76 41 82 160 65 128 256), losses := [] }

theorem u3058 : Upper (D 7) (R 7) [6,288,72,33,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3059 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 76 41 82 160 80 129 385), lower := (rows 7 290 76 41 82 160 80 128 256), losses := [] }

theorem u3059 : Upper (D 7) (R 7) [6,288,72,33,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3059 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u3059
end Delivery.IrregularNine14.P07
