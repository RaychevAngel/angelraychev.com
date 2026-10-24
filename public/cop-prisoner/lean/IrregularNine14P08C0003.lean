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

def b180 : PairBound 9 := { available := 192, camps := [], pairs := [], upper := (rows 7 98 164 25 304 33 72 192 448), lower := (rows 7 98 164 25 304 33 72 128 256), losses := [] }

theorem u180 : Upper (D 8) (R 8) [6,96,160,17,288,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b180 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b181 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 164 25 304 33 192 200 328), lower := (rows 7 98 164 25 304 33 192 128 256), losses := [] }

theorem u181 : Upper (D 8) (R 8) [6,96,160,17,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b182 : PairBound 9 := { available := 264, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 7 98 164 56 208 33 65 392 264), lower := (rows 7 98 164 56 208 33 65 128 256), losses := [] }

theorem u182 : Upper (D 8) (R 8) [6,96,160,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b183 : PairBound 9 := { available := 257, camps := [], pairs := [], upper := (rows 7 98 164 56 208 33 72 385 257), lower := (rows 7 98 164 56 208 33 72 128 256), losses := [] }

theorem u183 : Upper (D 8) (R 8) [6,96,160,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b183 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b184 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 7 98 164 56 208 33 320 137 265), lower := (rows 7 98 164 56 208 33 320 128 256), losses := [] }

theorem u184 : Upper (D 8) (R 8) [6,96,160,48,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b184 [(6,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b185 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 7 98 164 56 336 33 65 136 392), lower := (rows 7 98 164 56 336 33 65 128 256), losses := [] }

theorem u185 : Upper (D 8) (R 8) [6,96,160,48,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b185 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b186 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 98 164 56 336 33 72 129 385), lower := (rows 7 98 164 56 336 33 72 128 256), losses := [] }

theorem u186 : Upper (D 8) (R 8) [6,96,160,48,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b186 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b187 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 164 56 336 33 192 137 265), lower := (rows 7 98 164 56 336 33 192 128 256), losses := [] }

theorem u187 : Upper (D 8) (R 8) [6,96,160,48,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b188 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 7 98 164 88 304 33 65 136 392), lower := (rows 7 98 164 88 304 33 65 128 256), losses := [] }

theorem u188 : Upper (D 8) (R 8) [6,96,160,80,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b189 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 98 164 88 304 33 72 129 385), lower := (rows 7 98 164 88 304 33 72 128 256), losses := [] }

theorem u189 : Upper (D 8) (R 8) [6,96,160,80,288,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b189 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b190 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 164 88 304 33 192 137 265), lower := (rows 7 98 164 88 304 33 192 128 256), losses := [] }

theorem u190 : Upper (D 8) (R 8) [6,96,160,80,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b191 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 7 98 164 88 400 33 65 168 296), lower := (rows 7 98 164 88 400 33 65 128 256), losses := [] }

theorem u191 : Upper (D 8) (R 8) [6,96,160,80,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b192 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 98 164 88 400 33 72 161 289), lower := (rows 7 98 164 88 400 33 72 128 256), losses := [] }

theorem u192 : Upper (D 8) (R 8) [6,96,160,80,384,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b192 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b193 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 164 88 400 33 96 137 265), lower := (rows 7 98 164 88 400 33 96 128 256), losses := [] }

theorem u193 : Upper (D 8) (R 8) [6,96,160,80,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b193 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b194 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 7 98 164 200 273 33 72 176 304), lower := (rows 7 98 164 200 273 33 72 128 256), losses := [] }

theorem u194 : Upper (D 8) (R 8) [6,96,160,192,257,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b194 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b195 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 7 98 164 200 273 33 80 168 296), lower := (rows 7 98 164 200 273 33 80 128 256), losses := [] }

theorem u195 : Upper (D 8) (R 8) [6,96,160,192,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b195 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b196 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 164 200 273 33 96 152 280), lower := (rows 7 98 164 200 273 33 96 128 256), losses := [] }

theorem u196 : Upper (D 8) (R 8) [6,96,160,192,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b196 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b197 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 7 98 164 200 280 33 65 176 304), lower := (rows 7 98 164 200 280 33 65 128 256), losses := [] }

theorem u197 : Upper (D 8) (R 8) [6,96,160,192,264,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b198 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 98 164 200 280 33 80 161 289), lower := (rows 7 98 164 200 280 33 80 128 256), losses := [] }

theorem u198 : Upper (D 8) (R 8) [6,96,160,192,264,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b198 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b199 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 164 200 280 33 96 145 273), lower := (rows 7 98 164 200 280 33 96 128 256), losses := [] }

theorem u199 : Upper (D 8) (R 8) [6,96,160,192,264,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b199 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b200 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 7 98 164 200 304 33 65 152 280), lower := (rows 7 98 164 200 304 33 65 128 256), losses := [] }

theorem u200 : Upper (D 8) (R 8) [6,96,160,192,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b200 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b201 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 7 98 164 200 304 33 72 145 273), lower := (rows 7 98 164 200 304 33 72 128 256), losses := [] }

theorem u201 : Upper (D 8) (R 8) [6,96,160,192,288,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b201 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b202 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 7 98 164 200 304 33 80 137 265), lower := (rows 7 98 164 200 304 33 80 128 256), losses := [] }

theorem u202 : Upper (D 8) (R 8) [6,96,160,192,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b202 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b203 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 7 98 268 168 208 33 65 176 304), lower := (rows 7 98 268 168 208 33 65 128 256), losses := [] }

theorem u203 : Upper (D 8) (R 8) [6,96,264,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b203 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b204 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 98 268 168 208 33 80 161 289), lower := (rows 7 98 268 168 208 33 80 128 256), losses := [] }

theorem u204 : Upper (D 8) (R 8) [6,96,264,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b204 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b205 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 268 168 208 33 96 145 273), lower := (rows 7 98 268 168 208 33 96 128 256), losses := [] }

theorem u205 : Upper (D 8) (R 8) [6,96,264,160,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b205 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b206 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 292 25 56 160 65 192 448), lower := (rows 7 98 292 25 56 160 65 128 256), losses := [] }

theorem u206 : Upper (D 8) (R 8) [6,96,288,17,40,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b207 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 261, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 292 25 56 160 192 193 321), lower := (rows 7 98 292 25 56 160 192 128 256), losses := [] }

theorem u207 : Upper (D 8) (R 8) [6,96,288,17,40,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b208 : PairBound 9 := { available := 192, camps := [], pairs := [], upper := (rows 7 98 292 25 176 33 72 192 448), lower := (rows 7 98 292 25 176 33 72 128 256), losses := [] }

theorem u208 : Upper (D 8) (R 8) [6,96,288,17,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b208 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b209 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 292 25 176 33 192 200 328), lower := (rows 7 98 292 25 176 33 192 128 256), losses := [] }

theorem u209 : Upper (D 8) (R 8) [6,96,288,17,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b210 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 7 98 292 56 208 33 65 136 392), lower := (rows 7 98 292 56 208 33 65 128 256), losses := [] }

theorem u210 : Upper (D 8) (R 8) [6,96,288,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b211 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 98 292 56 208 33 72 129 385), lower := (rows 7 98 292 56 208 33 72 128 256), losses := [] }

theorem u211 : Upper (D 8) (R 8) [6,96,288,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b211 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b212 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 292 56 208 33 192 137 265), lower := (rows 7 98 292 56 208 33 192 128 256), losses := [] }

theorem u212 : Upper (D 8) (R 8) [6,96,288,48,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b213 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 7 98 292 88 176 33 65 136 392), lower := (rows 7 98 292 88 176 33 65 128 256), losses := [] }

theorem u213 : Upper (D 8) (R 8) [6,96,288,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b214 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 98 292 88 176 33 72 129 385), lower := (rows 7 98 292 88 176 33 72 128 256), losses := [] }

theorem u214 : Upper (D 8) (R 8) [6,96,288,80,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b214 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b215 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 292 88 176 33 192 137 265), lower := (rows 7 98 292 88 176 33 192 128 256), losses := [] }

theorem u215 : Upper (D 8) (R 8) [6,96,288,80,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b216 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 7 98 292 137 208 33 72 176 304), lower := (rows 7 98 292 137 208 33 72 128 256), losses := [] }

theorem u216 : Upper (D 8) (R 8) [6,96,288,129,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b216 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b217 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 7 98 292 137 208 33 80 168 296), lower := (rows 7 98 292 137 208 33 80 128 256), losses := [] }

theorem u217 : Upper (D 8) (R 8) [6,96,288,129,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b217 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b218 : PairBound 9 := { available := 24, camps := [{ cop := 8, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 292 137 208 33 96 152 280), lower := (rows 7 98 292 137 208 33 96 128 256), losses := [] }

theorem u218 : Upper (D 8) (R 8) [6,96,288,129,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b219 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 7 98 292 168 208 33 65 152 280), lower := (rows 7 98 292 168 208 33 65 128 256), losses := [] }

theorem u219 : Upper (D 8) (R 8) [6,96,288,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b219 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b220 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 7 98 292 168 208 33 72 145 273), lower := (rows 7 98 292 168 208 33 72 128 256), losses := [] }

theorem u220 : Upper (D 8) (R 8) [6,96,288,160,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b220 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b221 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 7 98 292 168 208 33 80 137 265), lower := (rows 7 98 292 168 208 33 80 128 256), losses := [] }

theorem u221 : Upper (D 8) (R 8) [6,96,288,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b221 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b222 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 7 98 388 56 208 33 65 168 296), lower := (rows 7 98 388 56 208 33 65 128 256), losses := [] }

theorem u222 : Upper (D 8) (R 8) [6,96,384,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b222 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b223 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 98 388 56 208 33 72 161 289), lower := (rows 7 98 388 56 208 33 72 128 256), losses := [] }

theorem u223 : Upper (D 8) (R 8) [6,96,384,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b223 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b224 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 388 56 208 33 96 137 265), lower := (rows 7 98 388 56 208 33 96 128 256), losses := [] }

theorem u224 : Upper (D 8) (R 8) [6,96,384,48,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b224 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b225 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 7 98 388 88 176 33 65 168 296), lower := (rows 7 98 388 88 176 33 65 128 256), losses := [] }

theorem u225 : Upper (D 8) (R 8) [6,96,384,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b226 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 98 388 88 176 33 72 161 289), lower := (rows 7 98 388 88 176 33 72 128 256), losses := [] }

theorem u226 : Upper (D 8) (R 8) [6,96,384,80,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b226 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b227 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 388 88 176 33 96 137 265), lower := (rows 7 98 388 88 176 33 96 128 256), losses := [] }

theorem u227 : Upper (D 8) (R 8) [6,96,384,80,160,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b228 : PairBound 9 := { available := 40, camps := [], pairs := [(1,5)], upper := (rows 7 194 292 88 176 33 65 168 296), lower := (rows 7 194 292 88 176 33 65 128 256), losses := [{ target := 5, region := (rows 1 18 4 24 16 0 97 128 256), good := (rows 71 194 324 90 218 65 65 128 256) }] }

theorem u228 : Upper (D 8) (R 8) [6,192,288,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b229 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 194 292 88 176 33 72 161 289), lower := (rows 7 194 292 88 176 33 72 128 256), losses := [] }

theorem u229 : Upper (D 8) (R 8) [6,192,288,80,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b229 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b230 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 292 88 176 33 96 137 265), lower := (rows 7 194 292 88 176 33 96 128 256), losses := [] }

theorem u230 : Upper (D 8) (R 8) [6,192,288,80,160,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b231 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 146, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 292 104 176 33 65 152 280), lower := (rows 7 194 292 104 176 33 65 128 256), losses := [] }

theorem u231 : Upper (D 8) (R 8) [6,192,288,96,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b232 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 7 194 292 104 176 33 72 145 273), lower := (rows 7 194 292 104 176 33 72 128 256), losses := [] }

theorem u232 : Upper (D 8) (R 8) [6,192,288,96,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b232 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b233 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 7 194 292 104 176 33 80 137 265), lower := (rows 7 194 292 104 176 33 80 128 256), losses := [] }

theorem u233 : Upper (D 8) (R 8) [6,192,288,96,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b233 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b234 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 28 104 304 160 65 192 448), lower := (rows 35 7 28 104 304 160 65 128 256), losses := [] }

theorem u234 : Upper (D 8) (R 8) [34,5,24,96,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b234 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b235 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 28 104 304 160 192 193 321), lower := (rows 35 7 28 104 304 160 192 128 256), losses := [] }

theorem u235 : Upper (D 8) (R 8) [34,5,24,96,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b236 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 296 112 160 65 144 400), lower := (rows 35 7 76 296 112 160 65 128 256), losses := [] }

theorem u236 : Upper (D 8) (R 8) [34,5,72,288,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b237 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 7 76 296 112 160 80 129 385), lower := (rows 35 7 76 296 112 160 80 128 256), losses := [] }

theorem u237 : Upper (D 8) (R 8) [34,5,72,288,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b237 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b238 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 296 112 160 192 145 273), lower := (rows 35 7 76 296 112 160 192 128 256), losses := [] }

theorem u238 : Upper (D 8) (R 8) [34,5,72,288,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b239 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 296 208 160 65 176 304), lower := (rows 35 7 76 296 208 160 65 128 256), losses := [] }

theorem u239 : Upper (D 8) (R 8) [34,5,72,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b239 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u239
end Delivery.IrregularNine14.P08
