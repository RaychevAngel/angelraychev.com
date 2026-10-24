import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b240 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 7 76 296 208 160 80 161 289), lower := (rows 35 7 76 296 208 160 80 128 256), losses := [] }

theorem u240 : Upper (D 8) (R 8) [34,5,72,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b240 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b241 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 296 208 160 96 145 273), lower := (rows 35 7 76 296 208 160 96 128 256), losses := [] }

theorem u241 : Upper (D 8) (R 8) [34,5,72,288,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b242 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 444, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 324 104 152 160 65 176 304), lower := (rows 35 7 324 104 152 160 65 128 256), losses := [] }

theorem u242 : Upper (D 8) (R 8) [34,5,320,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b242 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b243 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 7 324 104 152 160 80 161 289), lower := (rows 35 7 324 104 152 160 80 128 256), losses := [] }

theorem u243 : Upper (D 8) (R 8) [34,5,320,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b243 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b244 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 324 104 152 160 96 145 273), lower := (rows 35 7 324 104 152 160 96 128 256), losses := [] }

theorem u244 : Upper (D 8) (R 8) [34,5,320,96,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b245 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 21 104 304 160 65 192 448), lower := (rows 35 14 21 104 304 160 65 128 256), losses := [] }

theorem u245 : Upper (D 8) (R 8) [34,12,17,96,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b246 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 21 104 304 160 192 193 321), lower := (rows 35 14 21 104 304 160 192 128 256), losses := [] }

theorem u246 : Upper (D 8) (R 8) [34,12,17,96,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b247 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 21 296 112 160 65 192 448), lower := (rows 35 14 21 296 112 160 65 128 256), losses := [] }

theorem u247 : Upper (D 8) (R 8) [34,12,17,288,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b248 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 21 296 112 160 192 193 321), lower := (rows 35 14 21 296 112 160 192 128 256), losses := [] }

theorem u248 : Upper (D 8) (R 8) [34,12,17,288,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b249 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 296 112 160 65 144 400), lower := (rows 35 14 69 296 112 160 65 128 256), losses := [] }

theorem u249 : Upper (D 8) (R 8) [34,12,65,288,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b249 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b250 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 14 69 296 112 160 80 129 385), lower := (rows 35 14 69 296 112 160 80 128 256), losses := [] }

theorem u250 : Upper (D 8) (R 8) [34,12,65,288,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b250 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b251 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 296 112 160 192 145 273), lower := (rows 35 14 69 296 112 160 192 128 256), losses := [] }

theorem u251 : Upper (D 8) (R 8) [34,12,65,288,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b251 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b252 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0)], upper := (rows 35 14 69 296 208 160 65 176 304), lower := (rows 35 14 69 296 208 160 65 128 256), losses := [] }

theorem u252 : Upper (D 8) (R 8) [34,12,65,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b253 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 14 69 296 208 160 80 161 289), lower := (rows 35 14 69 296 208 160 80 128 256), losses := [] }

theorem u253 : Upper (D 8) (R 8) [34,12,65,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b253 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b254 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 296 208 160 96 145 273), lower := (rows 35 14 69 296 208 160 96 128 256), losses := [] }

theorem u254 : Upper (D 8) (R 8) [34,12,65,288,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b254 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b255 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 308, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 200 304 160 65 164 292), lower := (rows 35 67 28 200 304 160 65 128 256), losses := [] }

theorem u255 : Upper (D 8) (R 8) [34,65,24,192,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b255 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b256 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 67 28 200 304 160 68 161 289), lower := (rows 35 67 28 200 304 160 68 128 256), losses := [] }

theorem u256 : Upper (D 8) (R 8) [34,65,24,192,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b256 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b257 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 200 304 160 96 133 261), lower := (rows 35 67 28 200 304 160 96 128 256), losses := [] }

theorem u257 : Upper (D 8) (R 8) [34,65,24,192,288,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b258 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 88 304 160 65 132 388), lower := (rows 35 67 44 88 304 160 65 128 256), losses := [] }

theorem u258 : Upper (D 8) (R 8) [34,65,40,80,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b258 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b259 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 44 88 304 160 68 129 385), lower := (rows 35 67 44 88 304 160 68 128 256), losses := [] }

theorem u259 : Upper (D 8) (R 8) [34,65,40,80,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b259 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b260 : PairBound 9 := { available := 5, camps := [], pairs := [(2,0)], upper := (rows 35 67 44 88 304 160 192 133 261), lower := (rows 35 67 44 88 304 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 16 224 224 128 256), good := (rows 98 98 108 124 380 224 224 224 256) }] }

theorem u260 : Upper (D 8) (R 8) [34,65,40,80,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b260 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b261 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 300, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 268 208 160 65 176 304), lower := (rows 35 67 44 268 208 160 65 128 256), losses := [] }

theorem u261 : Upper (D 8) (R 8) [34,65,40,260,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b261 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b262 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 67 44 268 208 160 80 161 289), lower := (rows 35 67 44 268 208 160 80 128 256), losses := [] }

theorem u262 : Upper (D 8) (R 8) [34,65,40,260,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b262 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b263 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 268 208 160 96 145 273), lower := (rows 35 67 44 268 208 160 96 128 256), losses := [] }

theorem u263 : Upper (D 8) (R 8) [34,65,40,260,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b263 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b264 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 328 148 160 65 176 304), lower := (rows 35 67 44 328 148 160 65 128 256), losses := [] }

theorem u264 : Upper (D 8) (R 8) [34,65,40,320,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b265 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 67 44 328 148 160 80 161 289), lower := (rows 35 67 44 328 148 160 80 128 256), losses := [] }

theorem u265 : Upper (D 8) (R 8) [34,65,40,320,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b265 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b266 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 328 148 160 96 145 273), lower := (rows 35 67 44 328 148 160 96 128 256), losses := [] }

theorem u266 : Upper (D 8) (R 8) [34,65,40,320,132,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b267 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 76 152 304 160 65 164 292), lower := (rows 35 67 76 152 304 160 65 128 256), losses := [] }

theorem u267 : Upper (D 8) (R 8) [34,65,72,144,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b268 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 67 76 152 304 160 68 161 289), lower := (rows 35 67 76 152 304 160 68 128 256), losses := [] }

theorem u268 : Upper (D 8) (R 8) [34,65,72,144,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b268 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b269 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 152 304 160 96 133 261), lower := (rows 35 67 76 152 304 160 96 128 256), losses := [] }

theorem u269 : Upper (D 8) (R 8) [34,65,72,144,288,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b269 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b270 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 76 296 148 160 65 176 304), lower := (rows 35 67 76 296 148 160 65 128 256), losses := [] }

theorem u270 : Upper (D 8) (R 8) [34,65,72,288,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b270 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b271 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 67 76 296 148 160 80 161 289), lower := (rows 35 67 76 296 148 160 80 128 256), losses := [] }

theorem u271 : Upper (D 8) (R 8) [34,65,72,288,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b271 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b272 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 296 148 160 96 145 273), lower := (rows 35 67 76 296 148 160 96 128 256), losses := [] }

theorem u272 : Upper (D 8) (R 8) [34,65,72,288,132,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b273 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 296 112 160 65 144 400), lower := (rows 35 70 13 296 112 160 65 128 256), losses := [] }

theorem u273 : Upper (D 8) (R 8) [34,68,9,288,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b273 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b274 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 13 296 112 160 80 129 385), lower := (rows 35 70 13 296 112 160 80 128 256), losses := [] }

theorem u274 : Upper (D 8) (R 8) [34,68,9,288,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b274 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b275 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 296 112 160 192 145 273), lower := (rows 35 70 13 296 112 160 192 128 256), losses := [] }

theorem u275 : Upper (D 8) (R 8) [34,68,9,288,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b276 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 296 208 160 65 176 304), lower := (rows 35 70 13 296 208 160 65 128 256), losses := [] }

theorem u276 : Upper (D 8) (R 8) [34,68,9,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b277 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 13 296 208 160 80 161 289), lower := (rows 35 70 13 296 208 160 80 128 256), losses := [] }

theorem u277 : Upper (D 8) (R 8) [34,68,9,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b277 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b278 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 296 208 160 96 145 273), lower := (rows 35 70 13 296 208 160 96 128 256), losses := [] }

theorem u278 : Upper (D 8) (R 8) [34,68,9,288,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b278 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b279 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 265 112 160 65 144 400), lower := (rows 35 70 44 265 112 160 65 128 256), losses := [] }

theorem u279 : Upper (D 8) (R 8) [34,68,40,257,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b280 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 44 265 112 160 80 129 385), lower := (rows 35 70 44 265 112 160 80 128 256), losses := [] }

theorem u280 : Upper (D 8) (R 8) [34,68,40,257,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b280 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b281 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 265 112 160 192 145 273), lower := (rows 35 70 44 265 112 160 192 128 256), losses := [] }

theorem u281 : Upper (D 8) (R 8) [34,68,40,257,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b281 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b282 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 35 70 44 265 145 160 80 224 352), lower := (rows 35 70 44 265 145 160 80 128 256), losses := [] }

theorem u282 : Upper (D 8) (R 8) [34,68,40,257,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b282 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b283 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 265 145 160 96 208 336), lower := (rows 35 70 44 265 145 160 96 128 256), losses := [] }

theorem u283 : Upper (D 8) (R 8) [34,68,40,257,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b283 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b284 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 265 208 160 65 176 304), lower := (rows 35 70 44 265 208 160 65 128 256), losses := [] }

theorem u284 : Upper (D 8) (R 8) [34,68,40,257,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b285 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 44 265 208 160 80 161 289), lower := (rows 35 70 44 265 208 160 80 128 256), losses := [] }

theorem u285 : Upper (D 8) (R 8) [34,68,40,257,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b285 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b286 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 265 208 160 96 145 273), lower := (rows 35 70 44 265 208 160 96 128 256), losses := [] }

theorem u286 : Upper (D 8) (R 8) [34,68,40,257,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b286 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b287 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 104 152 160 65 176 304), lower := (rows 35 70 261 104 152 160 65 128 256), losses := [] }

theorem u287 : Upper (D 8) (R 8) [34,68,257,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b288 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 261 104 152 160 80 161 289), lower := (rows 35 70 261 104 152 160 80 128 256), losses := [] }

theorem u288 : Upper (D 8) (R 8) [34,68,257,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b288 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b289 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 104 152 160 96 145 273), lower := (rows 35 70 261 104 152 160 96 128 256), losses := [] }

theorem u289 : Upper (D 8) (R 8) [34,68,257,96,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b290 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 292 88 145 160 65 168 296), lower := (rows 35 70 292 88 145 160 65 128 256), losses := [] }

theorem u290 : Upper (D 8) (R 8) [34,68,288,80,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b290 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b291 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 292 88 145 160 72 161 289), lower := (rows 35 70 292 88 145 160 72 128 256), losses := [] }

theorem u291 : Upper (D 8) (R 8) [34,68,288,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b291 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b292 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 292 88 145 160 96 137 265), lower := (rows 35 70 292 88 145 160 96 128 256), losses := [] }

theorem u292 : Upper (D 8) (R 8) [34,68,288,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b292 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b293 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 292 104 145 160 65 152 280), lower := (rows 35 70 292 104 145 160 65 128 256), losses := [] }

theorem u293 : Upper (D 8) (R 8) [34,68,288,96,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b293 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b294 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 70 292 104 145 160 72 145 273), lower := (rows 35 70 292 104 145 160 72 128 256), losses := [] }

theorem u294 : Upper (D 8) (R 8) [34,68,288,96,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b294 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b295 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 70 292 104 145 160 80 137 265), lower := (rows 35 70 292 104 145 160 80 128 256), losses := [] }

theorem u295 : Upper (D 8) (R 8) [34,68,288,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b295 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b296 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 292 104 152 160 65 145 273), lower := (rows 35 70 292 104 152 160 65 128 256), losses := [] }

theorem u296 : Upper (D 8) (R 8) [34,68,288,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b297 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 70 292 104 152 160 80 129 257), lower := (rows 35 70 292 104 152 160 80 128 256), losses := [] }

theorem u297 : Upper (D 8) (R 8) [34,68,288,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b297 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b298 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7)], upper := (rows 35 262 44 73 112 160 65 144 400), lower := (rows 35 262 44 73 112 160 65 128 256), losses := [] }

theorem u298 : Upper (D 8) (R 8) [34,260,40,65,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b299 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 262 44 73 112 160 80 129 385), lower := (rows 35 262 44 73 112 160 80 128 256), losses := [] }

theorem u299 : Upper (D 8) (R 8) [34,260,40,65,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b299 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u299
end Delivery.IrregularNine14.P08
