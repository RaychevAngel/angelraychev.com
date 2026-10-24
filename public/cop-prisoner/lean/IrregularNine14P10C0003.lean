import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0000

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b180 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 143, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 44 152 112 288 320 129 385), lower := (rows 35 70 44 152 112 288 320 128 256), losses := [] }

theorem u180 : Upper (D 10) (R 10) [34,68,40,144,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b180 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b181 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 135, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 133 104 280 288 80 160 416), lower := (rows 35 70 133 104 280 288 80 128 256), losses := [] }

theorem u181 : Upper (D 10) (R 10) [34,68,129,96,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b181 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b182 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 72, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 35 70 133 104 280 288 96 144 400), lower := (rows 35 70 133 104 280 288 96 128 256), losses := [] }

theorem u182 : Upper (D 10) (R 10) [34,68,129,96,264,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b182 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b183 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 313, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 35 70 133 104 280 288 192 176 304), lower := (rows 35 70 133 104 280 288 192 128 256), losses := [] }

theorem u183 : Upper (D 10) (R 10) [34,68,129,96,264,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b183 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b184 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 133 168 280 288 80 224 352), lower := (rows 35 70 133 168 280 288 80 128 256), losses := [] }

theorem u184 : Upper (D 10) (R 10) [34,68,129,160,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b184 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b185 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 133 168 280 288 96 208 336), lower := (rows 35 70 133 168 280 288 96 128 256), losses := [] }

theorem u185 : Upper (D 10) (R 10) [34,68,129,160,264,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b185 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b186 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 56 208 288 65 392 264), lower := (rows 35 70 164 56 208 288 65 128 256), losses := [] }

theorem u186 : Upper (D 10) (R 10) [34,68,160,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b186 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b187 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 56 208 288 72 385 257), lower := (rows 35 70 164 56 208 288 72 128 256), losses := [] }

theorem u187 : Upper (D 10) (R 10) [34,68,160,48,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b187 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b188 : PairBound 9 := { available := 9, camps := [], pairs := [(1,5),(4,5)], upper := (rows 35 70 164 56 208 288 320 137 265), lower := (rows 35 70 164 56 208 288 320 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 20 0 352 128 256), good := (rows 67 86 214 88 208 320 320 128 320) }] }

theorem u188 : Upper (D 10) (R 10) [34,68,160,48,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b188 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b189 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 88 273 288 72 160 416), lower := (rows 35 70 164 88 273 288 72 128 256), losses := [] }

theorem u189 : Upper (D 10) (R 10) [34,68,160,80,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b189 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b190 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 164 88 273 288 96 136 392), lower := (rows 35 70 164 88 273 288 96 128 256), losses := [] }

theorem u190 : Upper (D 10) (R 10) [34,68,160,80,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b190 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b191 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 313, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 35 70 164 88 273 288 192 168 296), lower := (rows 35 70 164 88 273 288 192 128 256), losses := [] }

theorem u191 : Upper (D 10) (R 10) [34,68,160,80,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b191 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b192 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 88 400 288 65 168 296), lower := (rows 35 70 164 88 400 288 65 128 256), losses := [] }

theorem u192 : Upper (D 10) (R 10) [34,68,160,80,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b192 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b193 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 88 400 288 72 161 289), lower := (rows 35 70 164 88 400 288 72 128 256), losses := [] }

theorem u193 : Upper (D 10) (R 10) [34,68,160,80,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b193 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b194 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 164 88 400 288 96 137 265), lower := (rows 35 70 164 88 400 288 96 128 256), losses := [] }

theorem u194 : Upper (D 10) (R 10) [34,68,160,80,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b194 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b195 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 75, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 104 145 288 72 400 272), lower := (rows 35 70 164 104 145 288 72 128 256), losses := [] }

theorem u195 : Upper (D 10) (R 10) [34,68,160,96,129,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b195 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b196 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 83, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 104 145 288 80 392 264), lower := (rows 35 70 164 104 145 288 80 128 256), losses := [] }

theorem u196 : Upper (D 10) (R 10) [34,68,160,96,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b196 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b197 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 151, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 164 104 145 288 320 152 280), lower := (rows 35 70 164 104 145 288 320 128 256), losses := [] }

theorem u197 : Upper (D 10) (R 10) [34,68,160,96,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b197 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b198 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 104 152 288 65 400 272), lower := (rows 35 70 164 104 152 288 65 128 256), losses := [] }

theorem u198 : Upper (D 10) (R 10) [34,68,160,96,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b198 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b199 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 104 152 288 80 385 257), lower := (rows 35 70 164 104 152 288 80 128 256), losses := [] }

theorem u199 : Upper (D 10) (R 10) [34,68,160,96,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b199 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b200 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 151, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 164 104 152 288 320 145 273), lower := (rows 35 70 164 104 152 288 320 128 256), losses := [] }

theorem u200 : Upper (D 10) (R 10) [34,68,160,96,136,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b200 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b201 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 273 288 72 144 400), lower := (rows 35 70 164 104 273 288 72 128 256), losses := [] }

theorem u201 : Upper (D 10) (R 10) [34,68,160,96,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b201 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b202 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 135, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 104 273 288 80 136 392), lower := (rows 35 70 164 104 273 288 80 128 256), losses := [] }

theorem u202 : Upper (D 10) (R 10) [34,68,160,96,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b202 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b203 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 313, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 35 70 164 104 273 288 192 152 280), lower := (rows 35 70 164 104 273 288 192 128 256), losses := [] }

theorem u203 : Upper (D 10) (R 10) [34,68,160,96,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b203 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b204 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 280 288 65 144 400), lower := (rows 35 70 164 104 280 288 65 128 256), losses := [] }

theorem u204 : Upper (D 10) (R 10) [34,68,160,96,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b204 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b205 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 135, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 104 280 288 80 129 385), lower := (rows 35 70 164 104 280 288 80 128 256), losses := [] }

theorem u205 : Upper (D 10) (R 10) [34,68,160,96,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b205 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b206 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 313, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 35 70 164 104 280 288 192 145 273), lower := (rows 35 70 164 104 280 288 192 128 256), losses := [] }

theorem u206 : Upper (D 10) (R 10) [34,68,160,96,264,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b206 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b207 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 400 288 65 152 280), lower := (rows 35 70 164 104 400 288 65 128 256), losses := [] }

theorem u207 : Upper (D 10) (R 10) [34,68,160,96,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b207 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b208 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 400 288 72 145 273), lower := (rows 35 70 164 104 400 288 72 128 256), losses := [] }

theorem u208 : Upper (D 10) (R 10) [34,68,160,96,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b208 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b209 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 135, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 104 400 288 80 137 265), lower := (rows 35 70 164 104 400 288 80 128 256), losses := [] }

theorem u209 : Upper (D 10) (R 10) [34,68,160,96,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b209 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b210 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 137 280 288 80 224 352), lower := (rows 35 70 164 137 280 288 80 128 256), losses := [] }

theorem u210 : Upper (D 10) (R 10) [34,68,160,129,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b210 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b211 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 164 137 280 288 96 208 336), lower := (rows 35 70 164 137 280 288 96 128 256), losses := [] }

theorem u211 : Upper (D 10) (R 10) [34,68,160,129,264,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b211 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b212 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 75, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 137 336 288 72 176 304), lower := (rows 35 70 164 137 336 288 72 128 256), losses := [] }

theorem u212 : Upper (D 10) (R 10) [34,68,160,129,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b212 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b213 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 425, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 137 336 288 80 168 296), lower := (rows 35 70 164 137 336 288 80 128 256), losses := [] }

theorem u213 : Upper (D 10) (R 10) [34,68,160,129,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b213 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b214 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 164 137 336 288 96 152 280), lower := (rows 35 70 164 137 336 288 96 128 256), losses := [] }

theorem u214 : Upper (D 10) (R 10) [34,68,160,129,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b214 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b215 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 152 273 288 72 224 352), lower := (rows 35 70 164 152 273 288 72 128 256), losses := [] }

theorem u215 : Upper (D 10) (R 10) [34,68,160,144,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b215 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b216 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 164 152 273 288 96 200 328), lower := (rows 35 70 164 152 273 288 96 128 256), losses := [] }

theorem u216 : Upper (D 10) (R 10) [34,68,160,144,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b216 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b217 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 152 336 288 65 168 296), lower := (rows 35 70 164 152 336 288 65 128 256), losses := [] }

theorem u217 : Upper (D 10) (R 10) [34,68,160,144,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b217 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b218 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 152 336 288 72 161 289), lower := (rows 35 70 164 152 336 288 72 128 256), losses := [] }

theorem u218 : Upper (D 10) (R 10) [34,68,160,144,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b218 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b219 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 164 152 336 288 96 137 265), lower := (rows 35 70 164 152 336 288 96 128 256), losses := [] }

theorem u219 : Upper (D 10) (R 10) [34,68,160,144,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b219 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b220 : PairBound 9 := { available := 288, camps := [], pairs := [], upper := (rows 35 70 164 200 273 48 72 416 288), lower := (rows 35 70 164 200 273 48 72 128 256), losses := [] }

theorem u220 : Upper (D 10) (R 10) [34,68,160,192,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b220 [(5,4),(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b221 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 200 273 48 96 392 264), lower := (rows 35 70 164 200 273 48 96 128 256), losses := [] }

theorem u221 : Upper (D 10) (R 10) [34,68,160,192,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b221 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r222 : Route 9 := (fun mask => (mask,id))

def c222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u222 : Upper (D 10) (R 10) [34,68,160,192,257,16,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,257,16,256] 13 (by decide) (choices 1) [8,32] r222 c222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2
  · exact u3

def b223 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 200 273 288 72 176 304), lower := (rows 35 70 164 200 273 288 72 128 256), losses := [] }

theorem u223 : Upper (D 10) (R 10) [34,68,160,192,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b223 [(6,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b224 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 292, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 200 273 288 80 168 296), lower := (rows 35 70 164 200 273 288 80 128 256), losses := [] }

theorem u224 : Upper (D 10) (R 10) [34,68,160,192,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b224 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b225 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 164 200 273 288 96 152 280), lower := (rows 35 70 164 200 273 288 96 128 256), losses := [] }

theorem u225 : Upper (D 10) (R 10) [34,68,160,192,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b225 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b226 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8)], upper := (rows 35 70 164 200 280 288 65 176 304), lower := (rows 35 70 164 200 280 288 65 128 256), losses := [] }

theorem u226 : Upper (D 10) (R 10) [34,68,160,192,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b226 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b227 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 200 280 288 80 161 289), lower := (rows 35 70 164 200 280 288 80 128 256), losses := [] }

theorem u227 : Upper (D 10) (R 10) [34,68,160,192,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b227 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b228 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 164 200 280 288 96 145 273), lower := (rows 35 70 164 200 280 288 96 128 256), losses := [] }

theorem u228 : Upper (D 10) (R 10) [34,68,160,192,264,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b228 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b229 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 35 70 164 265 336 40 80 160 416), lower := (rows 35 70 164 265 336 40 80 128 256), losses := [] }

theorem u229 : Upper (D 10) (R 10) [34,68,160,257,320,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b229 [(5,3),(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b230 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 265 336 40 96 144 400), lower := (rows 35 70 164 265 336 40 96 128 256), losses := [] }

theorem u230 : Upper (D 10) (R 10) [34,68,160,257,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b230 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b231 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 313, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 265 336 40 192 176 304), lower := (rows 35 70 164 265 336 40 192 128 256), losses := [] }

theorem u231 : Upper (D 10) (R 10) [34,68,160,257,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b231 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b232 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 35 70 164 265 400 40 80 224 352), lower := (rows 35 70 164 265 400 40 80 128 256), losses := [] }

theorem u232 : Upper (D 10) (R 10) [34,68,160,257,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b232 [(5,3),(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b233 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 265 400 40 96 208 336), lower := (rows 35 70 164 265 400 40 96 128 256), losses := [] }

theorem u233 : Upper (D 10) (R 10) [34,68,160,257,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b233 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b234 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 70, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 76 152 273 288 68 160 288), lower := (rows 35 194 76 152 273 288 68 128 256), losses := [] }

theorem u234 : Upper (D 10) (R 10) [34,192,72,144,257,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b234 [(6,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r235 : Route 9 := (fun mask => (mask,id))

def c235 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u235 : Upper (D 10) (R 10) [34,192,72,144,257,256,32] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,257,256,32] 13 (by decide) (choices 1) [4,32] r235 c235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4
  · exact u5

def b236 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 168 273 288 68 176 304), lower := (rows 35 194 76 168 273 288 68 128 256), losses := [] }

theorem u236 : Upper (D 10) (R 10) [34,192,72,160,257,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b236 [(6,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b237 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 35 194 76 168 273 288 80 164 292), lower := (rows 35 194 76 168 273 288 80 128 256), losses := [] }

theorem u237 : Upper (D 10) (R 10) [34,192,72,160,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b237 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b238 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 67, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 76 168 273 288 96 148 276), lower := (rows 35 194 76 168 273 288 96 128 256), losses := [] }

theorem u238 : Upper (D 10) (R 10) [34,192,72,160,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b238 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b239 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 67, targets := 256 }], pairs := [(0,8)], upper := (rows 35 194 76 168 276 288 65 176 304), lower := (rows 35 194 76 168 276 288 65 128 256), losses := [] }

theorem u239 : Upper (D 10) (R 10) [34,192,72,160,260,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b239 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u239
end Delivery.IrregularNine14.P10
