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

def b3180 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 259, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 290 100 26 145 160 72 193 321), lower := (rows 7 290 100 26 145 160 72 128 256), losses := [] }

theorem u3180 : Upper (D 7) (R 7) [6,288,96,18,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3180 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3181 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 410, targets := 1 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 290 100 26 152 33 65 192 448), lower := (rows 7 290 100 26 152 33 65 128 256), losses := [] }

theorem u3181 : Upper (D 7) (R 7) [6,288,96,18,136,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3182 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 295, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 290 100 26 152 33 192 193 321), lower := (rows 7 290 100 26 152 33 192 128 256), losses := [] }

theorem u3182 : Upper (D 7) (R 7) [6,288,96,18,136,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3183 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 410, targets := 1 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 290 100 26 208 33 65 136 392), lower := (rows 7 290 100 26 208 33 65 128 256), losses := [] }

theorem u3183 : Upper (D 7) (R 7) [6,288,96,18,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3184 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 290 100 26 208 33 72 129 385), lower := (rows 7 290 100 26 208 33 72 128 256), losses := [] }

theorem u3184 : Upper (D 7) (R 7) [6,288,96,18,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3184 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3185 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 290 100 26 208 33 192 137 265), lower := (rows 7 290 100 26 208 33 192 128 256), losses := [] }

theorem u3185 : Upper (D 7) (R 7) [6,288,96,18,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3186 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 100 74 145 48 65 136 392), lower := (rows 7 290 100 74 145 48 65 128 256), losses := [] }

theorem u3186 : Upper (D 7) (R 7) [6,288,96,66,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3186 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3187 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 290 100 74 145 48 72 129 385), lower := (rows 7 290 100 74 145 48 72 128 256), losses := [] }

theorem u3187 : Upper (D 7) (R 7) [6,288,96,66,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3187 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3188 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 290 100 74 145 48 192 137 265), lower := (rows 7 290 100 74 145 48 192 128 256), losses := [] }

theorem u3188 : Upper (D 7) (R 7) [6,288,96,66,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3188 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3189 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 72, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(3,7)], upper := (rows 7 290 100 74 145 160 65 152 280), lower := (rows 7 290 100 74 145 160 65 128 256), losses := [] }

theorem u3189 : Upper (D 7) (R 7) [6,288,96,66,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3190 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 7 290 100 74 145 160 72 145 273), lower := (rows 7 290 100 74 145 160 72 128 256), losses := [] }

theorem u3190 : Upper (D 7) (R 7) [6,288,96,66,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3190 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3191 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 290 100 74 145 160 80 137 265), lower := (rows 7 290 100 74 145 160 80 128 256), losses := [] }

theorem u3191 : Upper (D 7) (R 7) [6,288,96,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3191 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3192 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 72, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(3,7)], upper := (rows 7 290 100 74 152 160 65 145 273), lower := (rows 7 290 100 74 152 160 65 128 256), losses := [] }

theorem u3192 : Upper (D 7) (R 7) [6,288,96,66,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3193 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 290 100 74 152 160 80 129 257), lower := (rows 7 290 100 74 152 160 80 128 256), losses := [] }

theorem u3193 : Upper (D 7) (R 7) [6,288,96,66,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3193 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3194 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 410, targets := 1 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 290 100 88 146 33 65 136 392), lower := (rows 7 290 100 88 146 33 65 128 256), losses := [] }

theorem u3194 : Upper (D 7) (R 7) [6,288,96,80,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3195 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 290 100 88 146 33 72 129 385), lower := (rows 7 290 100 88 146 33 72 128 256), losses := [] }

theorem u3195 : Upper (D 7) (R 7) [6,288,96,80,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3195 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3196 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 290 100 88 146 33 192 137 265), lower := (rows 7 290 100 88 146 33 192 128 256), losses := [] }

theorem u3196 : Upper (D 7) (R 7) [6,288,96,80,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3197 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 402, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 290 100 137 146 33 72 208 336), lower := (rows 7 290 100 137 146 33 72 128 256), losses := [] }

theorem u3197 : Upper (D 7) (R 7) [6,288,96,129,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3197 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3198 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 290 100 137 146 33 80 200 328), lower := (rows 7 290 100 137 146 33 80 128 256), losses := [] }

theorem u3198 : Upper (D 7) (R 7) [6,288,96,129,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3198 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3199 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 290 100 137 146 40 65 208 336), lower := (rows 7 290 100 137 146 40 65 128 256), losses := [] }

theorem u3199 : Upper (D 7) (R 7) [6,288,96,129,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3199 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3200 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 290 100 137 146 40 80 193 321), lower := (rows 7 290 100 137 146 40 80 128 256), losses := [] }

theorem u3200 : Upper (D 7) (R 7) [6,288,96,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3200 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3201 : PairBound 9 := { available := 24, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 290 100 137 208 33 66 152 280), lower := (rows 7 290 100 137 208 33 66 128 256), losses := [] }

theorem u3201 : Upper (D 7) (R 7) [6,288,96,129,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3202 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 100 137 208 33 72 146 274), lower := (rows 7 290 100 137 208 33 72 128 256), losses := [] }

theorem u3202 : Upper (D 7) (R 7) [6,288,96,129,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3202 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3203 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 290 100 137 208 33 80 138 266), lower := (rows 7 290 100 137 208 33 80 128 256), losses := [] }

theorem u3203 : Upper (D 7) (R 7) [6,288,96,129,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3203 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3204 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 290 100 137 208 40 65 146 274), lower := (rows 7 290 100 137 208 40 65 128 256), losses := [] }

theorem u3204 : Upper (D 7) (R 7) [6,288,96,129,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3204 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3205 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 290 100 137 208 40 66 145 273), lower := (rows 7 290 100 137 208 40 66 128 256), losses := [] }

theorem u3205 : Upper (D 7) (R 7) [6,288,96,129,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3205 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3206 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 290 100 137 208 40 80 131 259), lower := (rows 7 290 100 137 208 40 80 128 256), losses := [] }

theorem u3206 : Upper (D 7) (R 7) [6,288,96,129,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3206 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3207 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 410, targets := 1 },{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 290 100 138 208 33 65 152 280), lower := (rows 7 290 100 138 208 33 65 128 256), losses := [] }

theorem u3207 : Upper (D 7) (R 7) [6,288,96,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3208 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 290 100 138 208 33 72 145 273), lower := (rows 7 290 100 138 208 33 72 128 256), losses := [] }

theorem u3208 : Upper (D 7) (R 7) [6,288,96,130,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3208 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3209 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 290 100 138 208 33 80 137 265), lower := (rows 7 290 100 138 208 33 80 128 256), losses := [] }

theorem u3209 : Upper (D 7) (R 7) [6,288,96,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3209 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3210 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 88, targets := 128 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 7 290 196 25 82 33 72 160 416), lower := (rows 7 290 196 25 82 33 72 128 256), losses := [] }

theorem u3210 : Upper (D 7) (R 7) [6,288,192,17,66,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3210 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3211 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 141, targets := 32 },{ cop := 0, region := 120, targets := 128 }], pairs := [(0,5),(2,5),(3,5),(3,7)], upper := (rows 7 290 196 25 82 33 96 136 392), lower := (rows 7 290 196 25 82 33 96 128 256), losses := [] }

theorem u3211 : Upper (D 7) (R 7) [6,288,192,17,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3212 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 290 196 25 82 33 192 168 296), lower := (rows 7 290 196 25 82 33 192 128 256), losses := [] }

theorem u3212 : Upper (D 7) (R 7) [6,288,192,17,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3213 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 88, targets := 128 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 7 290 196 25 82 40 65 160 416), lower := (rows 7 290 196 25 82 40 65 128 256), losses := [] }

theorem u3213 : Upper (D 7) (R 7) [6,288,192,17,66,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3213 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3214 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 141, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 196 25 82 40 96 129 385), lower := (rows 7 290 196 25 82 40 96 128 256), losses := [] }

theorem u3214 : Upper (D 7) (R 7) [6,288,192,17,66,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3214 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3215 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 290 196 25 82 40 192 161 289), lower := (rows 7 290 196 25 82 40 192 128 256), losses := [] }

theorem u3215 : Upper (D 7) (R 7) [6,288,192,17,66,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3215 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3216 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 7 290 196 25 82 160 65 168 296), lower := (rows 7 290 196 25 82 160 65 128 256), losses := [] }

theorem u3216 : Upper (D 7) (R 7) [6,288,192,17,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3217 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 7 290 196 25 82 160 72 161 289), lower := (rows 7 290 196 25 82 160 72 128 256), losses := [] }

theorem u3217 : Upper (D 7) (R 7) [6,288,192,17,66,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3217 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3218 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 141, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 290 196 25 82 160 96 137 265), lower := (rows 7 290 196 25 82 160 96 128 256), losses := [] }

theorem u3218 : Upper (D 7) (R 7) [6,288,192,17,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3219 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 88, targets := 162 }], pairs := [(3,1),(3,5),(3,7),(4,1)], upper := (rows 7 290 196 25 88 160 65 162 290), lower := (rows 7 290 196 25 88 160 65 128 256), losses := [] }

theorem u3219 : Upper (D 7) (R 7) [6,288,192,17,72,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3220 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 7 290 196 25 88 160 66 161 289), lower := (rows 7 290 196 25 88 160 66 128 256), losses := [] }

theorem u3220 : Upper (D 7) (R 7) [6,288,192,17,72,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3221 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 5, region := 68, targets := 3 }], pairs := [(0,6),(1,6),(2,0),(2,1)], upper := (rows 7 290 196 25 88 160 96 131 259), lower := (rows 7 290 196 25 88 160 96 128 256), losses := [] }

theorem u3221 : Upper (D 7) (R 7) [6,288,192,17,72,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3222 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 120, targets := 128 },{ cop := 1, region := 80, targets := 1 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6),(3,7),(4,0),(4,7)], upper := (rows 7 290 196 25 112 33 66 136 392), lower := (rows 7 290 196 25 112 33 66 128 256), losses := [] }

theorem u3222 : Upper (D 7) (R 7) [6,288,192,17,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3223 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 120, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 7 290 196 25 112 33 72 130 386), lower := (rows 7 290 196 25 112 33 72 128 256), losses := [] }

theorem u3223 : Upper (D 7) (R 7) [6,288,192,17,96,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3223 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3224 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 290 196 25 112 33 192 138 266), lower := (rows 7 290 196 25 112 33 192 128 256), losses := [] }

theorem u3224 : Upper (D 7) (R 7) [6,288,192,17,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3225 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 88, targets := 128 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 7 290 196 26 81 33 72 160 416), lower := (rows 7 290 196 26 81 33 72 128 256), losses := [] }

theorem u3225 : Upper (D 7) (R 7) [6,288,192,18,65,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3225 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3226 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 120, targets := 128 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,6),(3,7),(4,7)], upper := (rows 7 290 196 26 81 33 96 136 392), lower := (rows 7 290 196 26 81 33 96 128 256), losses := [] }

theorem u3226 : Upper (D 7) (R 7) [6,288,192,18,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3227 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 290 196 26 81 33 192 168 296), lower := (rows 7 290 196 26 81 33 192 128 256), losses := [] }

theorem u3227 : Upper (D 7) (R 7) [6,288,192,18,65,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3228 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 290 196 26 81 40 65 160 416), lower := (rows 7 290 196 26 81 40 65 128 256), losses := [] }

theorem u3228 : Upper (D 7) (R 7) [6,288,192,18,65,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3228 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3229 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 120, targets := 128 },{ cop := 4, region := 132, targets := 2 }], pairs := [(2,1),(3,7),(4,7)], upper := (rows 7 290 196 26 81 40 96 129 385), lower := (rows 7 290 196 26 81 40 96 128 256), losses := [] }

theorem u3229 : Upper (D 7) (R 7) [6,288,192,18,65,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3229 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3230 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 290 196 26 81 40 192 161 289), lower := (rows 7 290 196 26 81 40 192 128 256), losses := [] }

theorem u3230 : Upper (D 7) (R 7) [6,288,192,18,65,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3230 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3231 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 7 290 196 26 81 160 65 168 296), lower := (rows 7 290 196 26 81 160 65 128 256), losses := [] }

theorem u3231 : Upper (D 7) (R 7) [6,288,192,18,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3232 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 7 290 196 26 81 160 72 161 289), lower := (rows 7 290 196 26 81 160 72 128 256), losses := [] }

theorem u3232 : Upper (D 7) (R 7) [6,288,192,18,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3232 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3233 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 5, region := 68, targets := 3 }], pairs := [(1,6),(2,0),(2,1),(3,6)], upper := (rows 7 290 196 26 81 160 96 137 265), lower := (rows 7 290 196 26 81 160 96 128 256), losses := [] }

theorem u3233 : Upper (D 7) (R 7) [6,288,192,18,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3234 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 88, targets := 128 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 7 290 196 26 88 33 65 160 416), lower := (rows 7 290 196 26 88 33 65 128 256), losses := [] }

theorem u3234 : Upper (D 7) (R 7) [6,288,192,18,72,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3235 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 88, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 290 196 26 88 33 96 129 385), lower := (rows 7 290 196 26 88 33 96 128 256), losses := [] }

theorem u3235 : Upper (D 7) (R 7) [6,288,192,18,72,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3236 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 290 196 26 88 33 192 161 289), lower := (rows 7 290 196 26 88 33 192 128 256), losses := [] }

theorem u3236 : Upper (D 7) (R 7) [6,288,192,18,72,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3237 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 7 290 196 26 88 160 65 161 289), lower := (rows 7 290 196 26 88 160 65 128 256), losses := [] }

theorem u3237 : Upper (D 7) (R 7) [6,288,192,18,72,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3238 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 88, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 290 196 26 88 160 96 129 257), lower := (rows 7 290 196 26 88 160 96 128 256), losses := [] }

theorem u3238 : Upper (D 7) (R 7) [6,288,192,18,72,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3239 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 398, targets := 1 },{ cop := 0, region := 120, targets := 128 }], pairs := [(1,0),(2,0),(3,0),(3,7)], upper := (rows 7 290 196 26 112 33 65 136 392), lower := (rows 7 290 196 26 112 33 65 128 256), losses := [] }

theorem u3239 : Upper (D 7) (R 7) [6,288,192,18,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u3239
end Delivery.IrregularNine14.P07
