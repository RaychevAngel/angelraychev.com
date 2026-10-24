import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b180 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 132, targets := 96 },{ cop := 2, region := 376, targets := 2 }], pairs := [(2,5),(2,6),(3,1)], upper := (rows 11 38 133 28 273 96 96 130 320), lower := (rows 11 38 133 28 273 96 96 130 256), losses := [] }

theorem u180 : Upper (D 6) (R 6) [10,36,129,20,257,64,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b181 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 281, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 133 28 273 96 96 192 258), lower := (rows 11 38 133 28 273 96 96 192 256), losses := [] }

theorem u181 : Upper (D 6) (R 6) [10,36,129,20,257,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b182 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 143, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 133 28 304 96 65 130 320), lower := (rows 11 38 133 28 304 96 65 130 256), losses := [] }

theorem u182 : Upper (D 6) (R 6) [10,36,129,20,288,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b183 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 133 28 304 96 65 192 258), lower := (rows 11 38 133 28 304 96 65 192 256), losses := [] }

theorem u183 : Upper (D 6) (R 6) [10,36,129,20,288,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b184 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 378, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 38 133 28 336 96 66 129 288), lower := (rows 11 38 133 28 336 96 66 129 256), losses := [] }

theorem u184 : Upper (D 6) (R 6) [10,36,129,20,320,64,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b185 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 345, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 133 28 336 96 66 160 257), lower := (rows 11 38 133 28 336 96 66 160 256), losses := [] }

theorem u185 : Upper (D 6) (R 6) [10,36,129,20,320,64,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b186 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 133 268 82 96 65 144 288), lower := (rows 11 38 133 268 82 96 65 144 256), losses := [] }

theorem u186 : Upper (D 6) (R 6) [10,36,129,260,66,64,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b186 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b187 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 345, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 133 268 82 96 65 160 272), lower := (rows 11 38 133 268 82 96 65 160 256), losses := [] }

theorem u187 : Upper (D 6) (R 6) [10,36,129,260,66,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b188 : PairBound 9 := { available := 32, camps := [{ cop := 7, region := 358, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 38 134 25 84 96 320 129 288), lower := (rows 11 38 134 25 84 96 320 129 256), losses := [] }

theorem u188 : Upper (D 6) (R 6) [10,36,130,17,68,64,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b188 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b189 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 6, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 38 134 25 84 96 320 160 257), lower := (rows 11 38 134 25 84 96 320 160 256), losses := [] }

theorem u189 : Upper (D 6) (R 6) [10,36,130,17,68,64,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b189 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b190 : PairBound 9 := { available := 64, camps := [{ cop := 7, region := 374, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 25 276 96 96 129 320), lower := (rows 11 38 134 25 276 96 96 129 256), losses := [] }

theorem u190 : Upper (D 6) (R 6) [10,36,130,17,260,64,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b191 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 281, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 134 25 276 96 96 192 257), lower := (rows 11 38 134 25 276 96 96 192 256), losses := [] }

theorem u191 : Upper (D 6) (R 6) [10,36,130,17,260,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b192 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 134 56 276 96 65 129 320), lower := (rows 11 38 134 56 276 96 65 129 256), losses := [] }

theorem u192 : Upper (D 6) (R 6) [10,36,130,48,260,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b193 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 134 56 276 96 65 192 257), lower := (rows 11 38 134 56 276 96 65 192 256), losses := [] }

theorem u193 : Upper (D 6) (R 6) [10,36,130,48,260,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b194 : PairBound 9 := { available := 32, camps := [{ cop := 7, region := 374, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 38 134 73 276 96 80 129 288), lower := (rows 11 38 134 73 276 96 80 129 256), losses := [] }

theorem u194 : Upper (D 6) (R 6) [10,36,130,65,260,64,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b194 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b195 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 38 134 73 276 96 80 160 257), lower := (rows 11 38 134 73 276 96 80 160 256), losses := [] }

theorem u195 : Upper (D 6) (R 6) [10,36,130,65,260,64,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b195 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b196 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 88 276 33 65 160 320), lower := (rows 11 38 134 88 276 33 65 160 256), losses := [] }

theorem u196 : Upper (D 6) (R 6) [10,36,130,80,260,1,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b197 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 272, targets := 65 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,0),(4,6)], upper := (rows 11 38 134 88 276 33 65 192 288), lower := (rows 11 38 134 88 276 33 65 192 256), losses := [] }

theorem u197 : Upper (D 6) (R 6) [10,36,130,80,260,1,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b198 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 134 88 276 33 96 129 320), lower := (rows 11 38 134 88 276 33 96 129 256), losses := [] }

theorem u198 : Upper (D 6) (R 6) [10,36,130,80,260,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b199 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 38 134 88 276 33 96 192 257), lower := (rows 11 38 134 88 276 33 96 192 256), losses := [{ target := 1, region := (rows 1 0 4 15 18 33 99 239 289), good := (rows 505 508 220 216 412 489 480 192 256) }] }

theorem u199 : Upper (D 6) (R 6) [10,36,130,80,260,1,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b200 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 272, targets := 65 },{ cop := 0, region := 132, targets := 32 }], pairs := [(2,5),(4,0),(4,6)], upper := (rows 11 38 134 88 276 96 65 129 288), lower := (rows 11 38 134 88 276 96 65 129 256), losses := [] }

theorem u200 : Upper (D 6) (R 6) [10,36,130,80,260,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b201 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 88 276 96 65 160 257), lower := (rows 11 38 134 88 276 96 65 160 256), losses := [] }

theorem u201 : Upper (D 6) (R 6) [10,36,130,80,260,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b202 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 264, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 38 134 328 21 96 65 144 288), lower := (rows 11 38 134 328 21 96 65 144 256), losses := [] }

theorem u202 : Upper (D 6) (R 6) [10,36,130,320,5,64,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b202 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b203 : PairBound 9 := { available := 16, camps := [{ cop := 5, region := 134, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 328 21 96 65 160 272), lower := (rows 11 38 134 328 21 96 65 160 256), losses := [] }

theorem u203 : Upper (D 6) (R 6) [10,36,130,320,5,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b204 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 272, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 196 56 336 33 66 129 260), lower := (rows 11 38 196 56 336 33 66 129 256), losses := [] }

theorem u204 : Upper (D 6) (R 6) [10,36,192,48,320,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b205 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 56 336 33 66 132 257), lower := (rows 11 38 196 56 336 33 66 132 256), losses := [] }

theorem u205 : Upper (D 6) (R 6) [10,36,192,48,320,1,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b206 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 1, region := 272, targets := 32 }], pairs := [(3,0),(4,0),(4,5)], upper := (rows 11 38 196 88 276 33 96 129 258), lower := (rows 11 38 196 88 276 33 96 129 256), losses := [] }

theorem u206 : Upper (D 6) (R 6) [10,36,192,80,260,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b207 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 38 196 88 276 33 96 130 257), lower := (rows 11 38 196 88 276 33 96 130 256), losses := [{ target := 1, region := (rows 1 0 132 139 18 33 99 128 289), good := (rows 377 380 204 88 276 361 352 220 256) }] }

theorem u207 : Upper (D 6) (R 6) [10,36,192,80,260,1,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b208 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,0),(4,0)], upper := (rows 11 38 196 88 304 33 66 129 260), lower := (rows 11 38 196 88 304 33 66 129 256), losses := [] }

theorem u208 : Upper (D 6) (R 6) [10,36,192,80,288,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b209 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 88 304 33 66 132 257), lower := (rows 11 38 196 88 304 33 66 132 256), losses := [] }

theorem u209 : Upper (D 6) (R 6) [10,36,192,80,288,1,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b210 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 196 328 21 33 66 144 288), lower := (rows 11 38 196 328 21 33 66 144 256), losses := [] }

theorem u210 : Upper (D 6) (R 6) [10,36,192,320,5,1,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b210 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b211 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 345, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 196 328 21 33 66 160 272), lower := (rows 11 38 196 328 21 33 66 160 256), losses := [] }

theorem u211 : Upper (D 6) (R 6) [10,36,192,320,5,1,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b212 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 360, targets := 6 },{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 38 196 328 21 33 96 130 272), lower := (rows 11 38 196 328 21 33 96 130 256), losses := [] }

theorem u212 : Upper (D 6) (R 6) [10,36,192,320,5,1,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b213 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 38 196 328 21 33 96 144 258), lower := (rows 11 38 196 328 21 33 96 144 256), losses := [] }

theorem u213 : Upper (D 6) (R 6) [10,36,192,320,5,1,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b213 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b214 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 2, region := 272, targets := 1 }], pairs := [(2,1),(4,0),(4,1)], upper := (rows 11 50 69 140 336 33 96 130 260), lower := (rows 11 50 69 140 336 33 96 130 256), losses := [] }

theorem u214 : Upper (D 6) (R 6) [10,48,65,132,320,1,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b215 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 338, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 69 140 336 33 96 132 258), lower := (rows 11 50 69 140 336 33 96 132 256), losses := [] }

theorem u215 : Upper (D 6) (R 6) [10,48,65,132,320,1,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b216 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 100 140 336 33 66 129 260), lower := (rows 11 50 100 140 336 33 66 129 256), losses := [] }

theorem u216 : Upper (D 6) (R 6) [10,48,96,132,320,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b217 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 136, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 50 100 140 336 33 66 132 257), lower := (rows 11 50 100 140 336 33 66 132 256), losses := [] }

theorem u217 : Upper (D 6) (R 6) [10,48,96,132,320,1,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b218 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 235, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 50 100 200 276 33 66 129 260), lower := (rows 11 50 100 200 276 33 66 129 256), losses := [] }

theorem u218 : Upper (D 6) (R 6) [10,48,96,192,260,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b219 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 136, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 50 100 200 276 33 66 132 257), lower := (rows 11 50 100 200 276 33 66 132 256), losses := [] }

theorem u219 : Upper (D 6) (R 6) [10,48,96,192,260,1,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b220 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 134 44 276 96 65 129 320), lower := (rows 11 50 134 44 276 96 65 129 256), losses := [] }

theorem u220 : Upper (D 6) (R 6) [10,48,130,36,260,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b221 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 275, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 134 44 276 96 65 192 257), lower := (rows 11 50 134 44 276 96 65 192 256), losses := [] }

theorem u221 : Upper (D 6) (R 6) [10,48,130,36,260,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b222 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 272, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 134 76 276 33 96 129 320), lower := (rows 11 50 134 76 276 33 96 129 256), losses := [] }

theorem u222 : Upper (D 6) (R 6) [10,48,130,68,260,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b223 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 307, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 134 76 276 33 96 192 257), lower := (rows 11 50 134 76 276 33 96 192 256), losses := [] }

theorem u223 : Upper (D 6) (R 6) [10,48,130,68,260,1,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b224 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 264, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 50 134 328 21 96 68 129 288), lower := (rows 11 50 134 328 21 96 68 129 256), losses := [] }

theorem u224 : Upper (D 6) (R 6) [10,48,130,320,5,64,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b225 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 345, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 50 134 328 21 96 68 160 257), lower := (rows 11 50 134 328 21 96 68 160 256), losses := [] }

theorem u225 : Upper (D 6) (R 6) [10,48,130,320,5,64,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b226 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 274, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 164 76 274 96 65 129 260), lower := (rows 11 50 164 76 274 96 65 129 256), losses := [] }

theorem u226 : Upper (D 6) (R 6) [10,48,160,68,258,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b227 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 140, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 50 164 76 274 96 65 132 257), lower := (rows 11 50 164 76 274 96 65 132 256), losses := [] }

theorem u227 : Upper (D 6) (R 6) [10,48,160,68,258,64,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b228 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 272, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 164 76 276 33 65 130 320), lower := (rows 11 50 164 76 276 33 65 130 256), losses := [] }

theorem u228 : Upper (D 6) (R 6) [10,48,160,68,260,1,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b229 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 274, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 164 76 276 33 65 192 258), lower := (rows 11 50 164 76 276 33 65 192 256), losses := [] }

theorem u229 : Upper (D 6) (R 6) [10,48,160,68,260,1,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b230 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 346, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 50 164 76 276 33 66 129 320), lower := (rows 11 50 164 76 276 33 66 129 256), losses := [] }

theorem u230 : Upper (D 6) (R 6) [10,48,160,68,260,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b231 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 307, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 164 76 276 33 66 192 257), lower := (rows 11 50 164 76 276 33 66 192 256), losses := [] }

theorem u231 : Upper (D 6) (R 6) [10,48,160,68,260,1,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b232 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 274, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 164 76 276 96 65 129 258), lower := (rows 11 50 164 76 276 96 65 129 256), losses := [] }

theorem u232 : Upper (D 6) (R 6) [10,48,160,68,260,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b233 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 132, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 50 164 76 276 96 65 130 257), lower := (rows 11 50 164 76 276 96 65 130 256), losses := [{ target := 0, region := (rows 0 2 71 104 16 104 64 131 256), good := (rows 174 190 172 108 276 108 236 134 256) }] }

theorem u233 : Upper (D 6) (R 6) [10,48,160,68,260,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b234 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 338, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 196 13 336 36 66 129 288), lower := (rows 11 50 196 13 336 36 66 129 256), losses := [] }

theorem u234 : Upper (D 6) (R 6) [10,48,192,5,320,4,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b235 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 246, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 196 13 336 36 66 160 257), lower := (rows 11 50 196 13 336 36 66 160 256), losses := [] }

theorem u235 : Upper (D 6) (R 6) [10,48,192,5,320,4,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b236 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 272, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 196 44 336 33 66 129 260), lower := (rows 11 50 196 44 336 33 66 129 256), losses := [] }

theorem u236 : Upper (D 6) (R 6) [10,48,192,36,320,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b237 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 196 44 336 33 66 132 257), lower := (rows 11 50 196 44 336 33 66 132 256), losses := [] }

theorem u237 : Upper (D 6) (R 6) [10,48,192,36,320,1,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b238 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 264, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 50 196 328 22 33 96 129 260), lower := (rows 11 50 196 328 22 33 96 129 256), losses := [] }

theorem u238 : Upper (D 6) (R 6) [10,48,192,320,6,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b239 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 132, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 50 196 328 22 33 96 132 257), lower := (rows 11 50 196 328 22 33 96 132 256), losses := [] }

theorem u239 : Upper (D 6) (R 6) [10,48,192,320,6,1,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u239
end Delivery.IrregularNine14.P06
