import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0003

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3120 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 117, targets := 128 },{ cop := 4, region := 386, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 290 76 138 112 33 65 144 400), lower := (rows 7 290 76 138 112 33 65 128 256), losses := [] }

theorem u3120 : Upper (D 7) (R 7) [6,288,72,130,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3121 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 290 76 138 112 33 80 129 385), lower := (rows 7 290 76 138 112 33 80 128 256), losses := [] }

theorem u3121 : Upper (D 7) (R 7) [6,288,72,130,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3121 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3122 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 290 76 138 112 33 192 145 273), lower := (rows 7 290 76 138 112 33 192 128 256), losses := [] }

theorem u3122 : Upper (D 7) (R 7) [6,288,72,130,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3123 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 76 138 112 160 65 145 273), lower := (rows 7 290 76 138 112 160 65 128 256), losses := [] }

theorem u3123 : Upper (D 7) (R 7) [6,288,72,130,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3124 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 290 76 138 112 160 80 129 257), lower := (rows 7 290 76 138 112 160 80 128 256), losses := [] }

theorem u3124 : Upper (D 7) (R 7) [6,288,72,130,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3124 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3125 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 85, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 290 76 138 145 33 80 224 352), lower := (rows 7 290 76 138 145 33 80 128 256), losses := [] }

theorem u3125 : Upper (D 7) (R 7) [6,288,72,130,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3125 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3126 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 0, region := 240, targets := 2 },{ cop := 4, region := 354, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,1)], upper := (rows 7 290 76 138 145 33 96 208 336), lower := (rows 7 290 76 138 145 33 96 128 256), losses := [] }

theorem u3126 : Upper (D 7) (R 7) [6,288,72,130,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3127 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 85, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 290 76 138 145 48 65 224 352), lower := (rows 7 290 76 138 145 48 65 128 256), losses := [] }

theorem u3127 : Upper (D 7) (R 7) [6,288,72,130,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3127 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3128 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,7),(2,0),(4,1)], upper := (rows 7 290 76 138 145 48 96 193 321), lower := (rows 7 290 76 138 145 48 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 48 114 128 256), good := (rows 70 354 76 206 240 112 96 128 256) }] }

theorem u3128 : Upper (D 7) (R 7) [6,288,72,130,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3128 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3129 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 85, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(4,5)], upper := (rows 7 290 76 138 145 96 65 176 304), lower := (rows 7 290 76 138 145 96 65 128 256), losses := [] }

theorem u3129 : Upper (D 7) (R 7) [6,288,72,130,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3130 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 85, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 290 76 138 145 96 80 161 289), lower := (rows 7 290 76 138 145 96 80 128 256), losses := [] }

theorem u3130 : Upper (D 7) (R 7) [6,288,72,130,129,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3130 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3131 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 290 76 138 145 96 96 145 273), lower := (rows 7 290 76 138 145 96 96 128 256), losses := [] }

theorem u3131 : Upper (D 7) (R 7) [6,288,72,130,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3132 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 69, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 76 138 176 33 65 208 336), lower := (rows 7 290 76 138 176 33 65 128 256), losses := [] }

theorem u3132 : Upper (D 7) (R 7) [6,288,72,130,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3133 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,7),(1,7),(4,1)], upper := (rows 7 290 76 138 176 33 80 193 321), lower := (rows 7 290 76 138 176 33 80 128 256), losses := [] }

theorem u3133 : Upper (D 7) (R 7) [6,288,72,130,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3133 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3134 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 69, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 290 76 138 176 96 65 145 273), lower := (rows 7 290 76 138 176 96 65 128 256), losses := [] }

theorem u3134 : Upper (D 7) (R 7) [6,288,72,130,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3135 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 290 76 138 176 96 80 129 257), lower := (rows 7 290 76 138 176 96 80 128 256), losses := [] }

theorem u3135 : Upper (D 7) (R 7) [6,288,72,130,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3135 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3136 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 85, targets := 32 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(4,5)], upper := (rows 7 290 76 138 208 33 65 176 304), lower := (rows 7 290 76 138 208 33 65 128 256), losses := [] }

theorem u3136 : Upper (D 7) (R 7) [6,288,72,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3137 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 290 76 138 208 33 80 161 289), lower := (rows 7 290 76 138 208 33 80 128 256), losses := [] }

theorem u3137 : Upper (D 7) (R 7) [6,288,72,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3137 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3138 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,7),(2,0),(2,7),(4,1)], upper := (rows 7 290 76 138 208 33 96 145 273), lower := (rows 7 290 76 138 208 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 32 98 128 256), good := (rows 70 354 92 222 208 96 96 128 256) }] }

theorem u3138 : Upper (D 7) (R 7) [6,288,72,130,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3139 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 85, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 290 76 138 208 48 65 161 289), lower := (rows 7 290 76 138 208 48 65 128 256), losses := [] }

theorem u3139 : Upper (D 7) (R 7) [6,288,72,130,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3139 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3140 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 290 76 138 208 48 96 129 257), lower := (rows 7 290 76 138 208 48 96 128 256), losses := [] }

theorem u3140 : Upper (D 7) (R 7) [6,288,72,130,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3140 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3141 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 7 290 76 152 81 160 65 162 290), lower := (rows 7 290 76 152 81 160 65 128 256), losses := [] }

theorem u3141 : Upper (D 7) (R 7) [6,288,72,144,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3142 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 160 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(4,5),(4,7)], upper := (rows 7 290 76 152 81 160 66 161 289), lower := (rows 7 290 76 152 81 160 66 128 256), losses := [] }

theorem u3142 : Upper (D 7) (R 7) [6,288,72,144,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3143 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 100, targets := 3 }], pairs := [(0,6),(1,6),(2,0),(2,1)], upper := (rows 7 290 76 152 81 160 96 131 259), lower := (rows 7 290 76 152 81 160 96 128 256), losses := [] }

theorem u3143 : Upper (D 7) (R 7) [6,288,72,144,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3144 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 80, targets := 32 },{ cop := 0, region := 80, targets := 128 }], pairs := [(0,6),(1,6),(4,5),(4,7)], upper := (rows 7 290 76 152 82 33 65 160 416), lower := (rows 7 290 76 152 82 33 65 128 256), losses := [] }

theorem u3144 : Upper (D 7) (R 7) [6,288,72,144,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3145 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 141, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 290 76 152 82 33 96 129 385), lower := (rows 7 290 76 152 82 33 96 128 256), losses := [] }

theorem u3145 : Upper (D 7) (R 7) [6,288,72,144,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3146 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 290 76 152 82 33 192 161 289), lower := (rows 7 290 76 152 82 33 192 128 256), losses := [] }

theorem u3146 : Upper (D 7) (R 7) [6,288,72,144,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3147 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 160 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(4,5),(4,7)], upper := (rows 7 290 76 152 82 160 65 161 289), lower := (rows 7 290 76 152 82 160 65 128 256), losses := [] }

theorem u3147 : Upper (D 7) (R 7) [6,288,72,144,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3148 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 141, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 290 76 152 82 160 96 129 257), lower := (rows 7 290 76 152 82 160 96 128 256), losses := [] }

theorem u3148 : Upper (D 7) (R 7) [6,288,72,144,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3149 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 398, targets := 1 },{ cop := 0, region := 112, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 290 76 152 112 33 65 130 386), lower := (rows 7 290 76 152 112 33 65 128 256), losses := [] }

theorem u3149 : Upper (D 7) (R 7) [6,288,72,144,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3150 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 129 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(4,0),(4,7)], upper := (rows 7 290 76 152 112 33 66 129 385), lower := (rows 7 290 76 152 112 33 66 128 256), losses := [] }

theorem u3150 : Upper (D 7) (R 7) [6,288,72,144,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3151 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 290 76 152 112 33 192 131 259), lower := (rows 7 290 76 152 112 33 192 128 256), losses := [] }

theorem u3151 : Upper (D 7) (R 7) [6,288,72,144,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3152 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 172, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,1),(3,1),(3,6)], upper := (rows 7 290 76 168 81 33 66 144 400), lower := (rows 7 290 76 168 81 33 66 128 256), losses := [] }

theorem u3152 : Upper (D 7) (R 7) [6,288,72,160,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3153 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 394, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 7 290 76 168 81 33 80 130 386), lower := (rows 7 290 76 168 81 33 80 128 256), losses := [] }

theorem u3153 : Upper (D 7) (R 7) [6,288,72,160,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3153 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3154 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 290 76 168 81 33 192 146 274), lower := (rows 7 290 76 168 81 33 192 128 256), losses := [] }

theorem u3154 : Upper (D 7) (R 7) [6,288,72,160,65,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3155 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 80, targets := 32 },{ cop := 0, region := 80, targets := 128 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 7 290 76 168 82 33 65 144 400), lower := (rows 7 290 76 168 82 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 28 24 16 97 97 144 272), good := (rows 101 352 108 236 508 97 97 128 256) }] }

theorem u3155 : Upper (D 7) (R 7) [6,288,72,160,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3156 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 7 290 76 168 82 33 80 129 385), lower := (rows 7 290 76 168 82 33 80 128 256), losses := [] }

theorem u3156 : Upper (D 7) (R 7) [6,288,72,160,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3156 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3157 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 290 76 168 82 33 192 145 273), lower := (rows 7 290 76 168 82 33 192 128 256), losses := [] }

theorem u3157 : Upper (D 7) (R 7) [6,288,72,160,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3158 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 80, targets := 32 },{ cop := 0, region := 80, targets := 128 }], pairs := [(2,1),(4,5),(4,7)], upper := (rows 7 290 76 168 82 48 65 129 385), lower := (rows 7 290 76 168 82 48 65 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 48 65 193 321), good := (rows 453 288 460 168 508 60 449 128 256) }] }

theorem u3158 : Upper (D 7) (R 7) [6,288,72,160,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3158 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3159 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 290 76 168 82 48 192 129 257), lower := (rows 7 290 76 168 82 48 192 128 256), losses := [] }

theorem u3159 : Upper (D 7) (R 7) [6,288,72,160,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3159 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3160 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 108, targets := 2 },{ cop := 0, region := 144, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(2,1),(3,1),(4,5),(4,6)], upper := (rows 7 290 76 168 145 96 65 146 274), lower := (rows 7 290 76 168 145 96 65 128 256), losses := [] }

theorem u3160 : Upper (D 7) (R 7) [6,288,72,160,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3161 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 8, region := 98, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,6)], upper := (rows 7 290 76 168 145 96 66 145 273), lower := (rows 7 290 76 168 145 96 66 128 256), losses := [] }

theorem u3161 : Upper (D 7) (R 7) [6,288,72,160,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3162 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 290 76 168 145 96 80 131 259), lower := (rows 7 290 76 168 145 96 80 128 256), losses := [] }

theorem u3162 : Upper (D 7) (R 7) [6,288,72,160,129,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3162 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3163 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(2,5),(2,7),(4,5)], upper := (rows 7 290 76 168 146 33 65 208 336), lower := (rows 7 290 76 168 146 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 97 97 128 256), good := (rows 101 352 108 236 144 97 97 128 256) },{ target := 5, region := (rows 1 2 12 8 19 0 97 227 355), good := (rows 471 466 460 460 402 465 465 128 256) },{ target := 7, region := (rows 1 2 12 8 16 97 97 0 256), good := (rows 103 354 108 108 18 97 97 0 256) }] }

theorem u3163 : Upper (D 7) (R 7) [6,288,72,160,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3164 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(1,7),(4,5)], upper := (rows 7 290 76 168 146 33 80 193 321), lower := (rows 7 290 76 168 146 33 80 128 256), losses := [] }

theorem u3164 : Upper (D 7) (R 7) [6,288,72,160,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3164 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3165 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,6),(3,6),(4,5),(4,6)], upper := (rows 7 290 76 168 146 96 65 145 273), lower := (rows 7 290 76 168 146 96 65 128 256), losses := [{ target := 6, region := (rows 1 34 4 40 57 32 0 193 321), good := (rows 407 314 412 186 146 442 401 128 256) }] }

theorem u3165 : Upper (D 7) (R 7) [6,288,72,160,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3166 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 290 76 168 146 96 80 129 257), lower := (rows 7 290 76 168 146 96 80 128 256), losses := [] }

theorem u3166 : Upper (D 7) (R 7) [6,288,72,160,130,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3166 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3167 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(3,1),(4,1),(4,5)], upper := (rows 7 290 76 168 208 33 65 146 274), lower := (rows 7 290 76 168 208 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 28 24 24 97 97 128 256), good := (rows 101 352 124 252 252 97 97 128 256) }] }

theorem u3167 : Upper (D 7) (R 7) [6,288,72,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3168 : Route 9 := (fun mask => (mask,id))

def c3168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3168 : Upper (D 7) (R 7) [6,288,72,160,192,1,2] 13 := by
  apply FastRouting.sound _ _ [6,288,72,160,192,1,2] 13 (by decide) (choices 1) [1,16] r3168 c3168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u192
  · exact u193

def b3169 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 84, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 290 76 168 208 33 80 131 259), lower := (rows 7 290 76 168 208 33 80 128 256), losses := [] }

theorem u3169 : Upper (D 7) (R 7) [6,288,72,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3169 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3170 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 100 25 146 33 72 192 448), lower := (rows 7 290 100 25 146 33 72 128 256), losses := [] }

theorem u3170 : Upper (D 7) (R 7) [6,288,96,17,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3170 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3171 : Route 9 := (fun mask => (mask,id))

def c3171 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3171 : Upper (D 7) (R 7) [6,288,96,17,130,1,128] 13 := by
  apply FastRouting.sound _ _ [6,288,96,17,130,1,128] 13 (by decide) (choices 1) [8,64] r3171 c3171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u194
  · exact u195

def b3172 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 290 100 25 146 160 65 200 328), lower := (rows 7 290 100 25 146 160 65 128 256), losses := [] }

theorem u3172 : Upper (D 7) (R 7) [6,288,96,17,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3173 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 259, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 290 100 25 146 160 72 193 321), lower := (rows 7 290 100 25 146 160 72 128 256), losses := [] }

theorem u3173 : Upper (D 7) (R 7) [6,288,96,17,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3173 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3174 : PairBound 9 := { available := 136, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 290 100 25 208 33 66 136 392), lower := (rows 7 290 100 25 208 33 66 128 256), losses := [] }

theorem u3174 : Upper (D 7) (R 7) [6,288,96,17,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3175 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 386, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 290 100 25 208 33 72 130 386), lower := (rows 7 290 100 25 208 33 72 128 256), losses := [] }

theorem u3175 : Upper (D 7) (R 7) [6,288,96,17,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3175 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3176 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 100 25 208 33 192 138 266), lower := (rows 7 290 100 25 208 33 192 128 256), losses := [] }

theorem u3176 : Upper (D 7) (R 7) [6,288,96,17,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3177 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 290 100 26 145 33 72 192 448), lower := (rows 7 290 100 26 145 33 72 128 256), losses := [] }

theorem u3177 : Upper (D 7) (R 7) [6,288,96,18,129,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3177 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3178 : Route 9 := (fun mask => (mask,id))

def c3178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3178 : Upper (D 7) (R 7) [6,288,96,18,129,1,128] 13 := by
  apply FastRouting.sound _ _ [6,288,96,18,129,1,128] 13 (by decide) (choices 1) [8,64] r3178 c3178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u196
  · exact u197

def b3179 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 290 100 26 145 160 65 200 328), lower := (rows 7 290 100 26 145 160 65 128 256), losses := [] }

theorem u3179 : Upper (D 7) (R 7) [6,288,96,18,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u3179
end Delivery.IrregularNine14.P07
