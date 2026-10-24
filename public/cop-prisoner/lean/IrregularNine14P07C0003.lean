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

def b180 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 290 13 200 112 160 66 144 257), lower := (rows 7 290 13 200 112 160 66 144 256), losses := [] }

theorem u180 : Upper (D 7) (R 7) [6,288,9,192,96,128,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b180 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b181 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 181, targets := 64 },{ cop := 4, region := 322, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 7 290 28 74 176 33 192 129 320), lower := (rows 7 290 28 74 176 33 192 129 256), losses := [] }

theorem u181 : Upper (D 7) (R 7) [6,288,24,66,160,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b182 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 291, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 290 28 74 176 33 192 192 257), lower := (rows 7 290 28 74 176 33 192 192 256), losses := [] }

theorem u182 : Upper (D 7) (R 7) [6,288,24,66,160,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b183 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 184, targets := 64 },{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0),(3,6),(4,6)], upper := (rows 7 290 69 41 152 160 80 130 320), lower := (rows 7 290 69 41 152 160 80 130 256), losses := [] }

theorem u183 : Upper (D 7) (R 7) [6,288,65,33,136,128,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b183 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b184 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 252, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 290 69 41 152 160 80 192 258), lower := (rows 7 290 69 41 152 160 80 192 256), losses := [] }

theorem u184 : Upper (D 7) (R 7) [6,288,65,33,136,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b184 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b185 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 184, targets := 64 },{ cop := 5, region := 338, targets := 1 }], pairs := [(1,0),(3,6),(4,6)], upper := (rows 7 290 76 41 146 160 80 129 320), lower := (rows 7 290 76 41 146 160 80 129 256), losses := [] }

theorem u185 : Upper (D 7) (R 7) [6,288,72,33,130,128,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b185 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b186 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 258, targets := 192 },{ cop := 8, region := 242, targets := 1 }], pairs := [(1,0),(1,6),(1,7)], upper := (rows 7 290 76 41 146 160 80 192 257), lower := (rows 7 290 76 41 146 160 80 192 256), losses := [] }

theorem u186 : Upper (D 7) (R 7) [6,288,72,33,130,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b186 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b187 : PairBound 9 := { available := 128, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,6),(1,0),(1,6),(4,5)], upper := (rows 7 290 76 56 208 33 66 129 384), lower := (rows 7 290 76 56 208 33 66 129 256), losses := [{ target := 0, region := (rows 0 10 12 8 144 32 79 128 400), good := (rows 70 354 78 382 464 96 66 464 256) }] }

theorem u187 : Upper (D 7) (R 7) [6,288,72,48,192,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b188 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 374, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 290 76 137 146 48 96 129 320), lower := (rows 7 290 76 137 146 48 96 129 256), losses := [] }

theorem u188 : Upper (D 7) (R 7) [6,288,72,129,130,16,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b188 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b189 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 306, targets := 64 },{ cop := 8, region := 242, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 7 290 76 137 146 48 96 192 257), lower := (rows 7 290 76 137 146 48 96 192 256), losses := [] }

theorem u189 : Upper (D 7) (R 7) [6,288,72,129,130,16,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b189 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b190 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 184, targets := 64 },{ cop := 4, region := 322, targets := 1 }], pairs := [(1,0),(3,6),(4,6)], upper := (rows 7 290 76 138 49 160 80 129 320), lower := (rows 7 290 76 138 49 160 80 129 256), losses := [] }

theorem u190 : Upper (D 7) (R 7) [6,288,72,130,33,128,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b190 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b191 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 4, region := 258, targets := 64 },{ cop := 4, region := 258, targets := 128 }], pairs := [(1,6),(1,7),(4,1)], upper := (rows 7 290 76 138 49 160 80 192 257), lower := (rows 7 290 76 138 49 160 80 192 256), losses := [] }

theorem u191 : Upper (D 7) (R 7) [6,288,72,130,33,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b191 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b192 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 342, targets := 1 },{ cop := 0, region := 168, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 7 290 76 168 208 33 66 129 272), lower := (rows 7 290 76 168 208 33 66 129 256), losses := [] }

theorem u192 : Upper (D 7) (R 7) [6,288,72,160,192,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b193 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 290 76 168 208 33 66 144 257), lower := (rows 7 290 76 168 208 33 66 144 256), losses := [] }

theorem u193 : Upper (D 7) (R 7) [6,288,72,160,192,1,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b193 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b194 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 100 25 146 33 192 136 320), lower := (rows 7 290 100 25 146 33 192 136 256), losses := [] }

theorem u194 : Upper (D 7) (R 7) [6,288,96,17,130,1,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b194 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b195 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 290 100 25 146 33 192 192 264), lower := (rows 7 290 100 25 146 33 192 192 256), losses := [] }

theorem u195 : Upper (D 7) (R 7) [6,288,96,17,130,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b196 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 290 100 26 145 33 192 136 320), lower := (rows 7 290 100 26 145 33 192 136 256), losses := [] }

theorem u196 : Upper (D 7) (R 7) [6,288,96,18,129,1,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b196 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b197 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 298, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 290 100 26 145 33 192 192 264), lower := (rows 7 290 100 26 145 33 192 192 256), losses := [] }

theorem u197 : Upper (D 7) (R 7) [6,288,96,18,129,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b198 : PairBound 9 := { available := 8, camps := [{ cop := 1, region := 213, targets := 32 },{ cop := 2, region := 314, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 290 196 56 82 160 65 129 264), lower := (rows 7 290 196 56 82 160 65 129 256), losses := [] }

theorem u198 : Upper (D 7) (R 7) [6,288,192,48,66,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b199 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 172, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 290 196 56 82 160 65 136 257), lower := (rows 7 290 196 56 82 160 65 136 256), losses := [] }

theorem u199 : Upper (D 7) (R 7) [6,288,192,48,66,128,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b199 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b200 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 196 74 152 48 65 129 288), lower := (rows 7 290 196 74 152 48 65 129 256), losses := [] }

theorem u200 : Upper (D 7) (R 7) [6,288,192,66,136,16,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b200 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b201 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 290 196 74 152 48 65 160 257), lower := (rows 7 290 196 74 152 48 65 160 256), losses := [] }

theorem u201 : Upper (D 7) (R 7) [6,288,192,66,136,16,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b201 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b202 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 290 196 74 176 40 65 129 272), lower := (rows 7 290 196 74 176 40 65 129 256), losses := [] }

theorem u202 : Upper (D 7) (R 7) [6,288,192,66,160,8,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b202 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b203 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 290 196 74 176 40 65 144 257), lower := (rows 7 290 196 74 176 40 65 144 256), losses := [] }

theorem u203 : Upper (D 7) (R 7) [6,288,192,66,160,8,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b203 [(5,3),(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b204 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 334, targets := 1 },{ cop := 0, region := 176, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 290 196 88 176 33 66 129 264), lower := (rows 7 290 196 88 176 33 66 129 256), losses := [] }

theorem u204 : Upper (D 7) (R 7) [6,288,192,80,160,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b205 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 290 196 88 176 33 66 136 257), lower := (rows 7 290 196 88 176 33 66 136 256), losses := [] }

theorem u205 : Upper (D 7) (R 7) [6,288,192,80,160,1,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b205 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b206 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 314, targets := 1 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 290 196 88 176 34 65 129 264), lower := (rows 7 290 196 88 176 34 65 129 256), losses := [] }

theorem u206 : Upper (D 7) (R 7) [6,288,192,80,160,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b207 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 307, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 290 196 88 176 34 65 136 257), lower := (rows 7 290 196 88 176 34 65 136 256), losses := [] }

theorem u207 : Upper (D 7) (R 7) [6,288,192,80,160,2,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b207 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b208 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 162, targets := 64 },{ cop := 1, region := 200, targets := 32 }], pairs := [(1,6),(3,0),(3,5),(4,0)], upper := (rows 13 35 21 74 304 160 192 130 320), lower := (rows 13 35 21 74 304 160 192 130 256), losses := [] }

theorem u208 : Upper (D 7) (R 7) [12,33,17,66,288,128,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b209 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 276, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 21 74 304 160 192 192 258), lower := (rows 13 35 21 74 304 160 192 192 256), losses := [] }

theorem u209 : Upper (D 7) (R 7) [12,33,17,66,288,128,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b210 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 333, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 13 35 69 266 146 160 80 160 320), lower := (rows 13 35 69 266 146 160 80 160 256), losses := [] }

theorem u210 : Upper (D 7) (R 7) [12,33,65,258,130,128,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b210 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b211 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 213, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 13 35 69 266 146 160 80 192 288), lower := (rows 13 35 69 266 146 160 80 192 256), losses := [] }

theorem u211 : Upper (D 7) (R 7) [12,33,65,258,130,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b211 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b212 : PairBound 9 := { available := 128, camps := [{ cop := 3, region := 272, targets := 35 },{ cop := 5, region := 466, targets := 1 }], pairs := [(1,0),(4,0),(4,1),(4,5)], upper := (rows 13 50 7 200 336 33 96 130 384), lower := (rows 13 50 7 200 336 33 96 130 256), losses := [] }

theorem u212 : Upper (D 7) (R 7) [12,48,3,192,320,1,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b213 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 205, targets := 32 },{ cop := 5, region := 338, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 7 200 336 160 66 129 288), lower := (rows 13 50 7 200 336 160 66 129 256), losses := [] }

theorem u213 : Upper (D 7) (R 7) [12,48,3,192,320,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b214 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 2, region := 336, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 50 7 200 336 160 66 160 257), lower := (rows 13 50 7 200 336 160 66 160 256), losses := [] }

theorem u214 : Upper (D 7) (R 7) [12,48,3,192,320,128,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b215 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 274, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 7 200 336 160 96 129 258), lower := (rows 13 50 7 200 336 160 96 129 256), losses := [] }

theorem u215 : Upper (D 7) (R 7) [12,48,3,192,320,128,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b216 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 50 7 200 336 160 96 130 257), lower := (rows 13 50 7 200 336 160 96 130 256), losses := [] }

theorem u216 : Upper (D 7) (R 7) [12,48,3,192,320,128,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b217 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 264, targets := 131 },{ cop := 2, region := 144, targets := 32 }], pairs := [(3,0),(3,1),(3,7),(4,5)], upper := (rows 13 50 7 328 145 96 192 130 288), lower := (rows 13 50 7 328 145 96 192 130 256), losses := [] }

theorem u217 : Upper (D 7) (R 7) [12,48,3,320,129,64,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b218 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 240, targets := 2 },{ cop := 8, region := 232, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,1)], upper := (rows 13 50 7 328 145 96 192 160 258), lower := (rows 13 50 7 328 145 96 192 160 256), losses := [] }

theorem u218 : Upper (D 7) (R 7) [12,48,3,320,129,64,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b219 : PairBound 9 := { available := 128, camps := [{ cop := 4, region := 264, targets := 35 },{ cop := 5, region := 210, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(3,5)], upper := (rows 13 50 7 328 208 33 96 130 384), lower := (rows 13 50 7 328 208 33 96 130 256), losses := [] }

theorem u219 : Upper (D 7) (R 7) [12,48,3,320,192,1,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b220 : PairBound 9 := { available := 2, camps := [{ cop := 7, region := 378, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 50 69 168 208 288 66 129 258), lower := (rows 13 50 69 168 208 288 66 129 256), losses := [] }

theorem u220 : Upper (D 7) (R 7) [12,48,65,160,192,256,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b220 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b221 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 301, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 13 50 69 168 208 288 66 130 257), lower := (rows 13 50 69 168 208 288 66 130 256), losses := [] }

theorem u221 : Upper (D 7) (R 7) [12,48,65,160,192,256,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b221 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b222 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 141, targets := 2 },{ cop := 7, region := 370, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 50 69 168 400 96 66 129 258), lower := (rows 13 50 69 168 400 96 66 129 256), losses := [] }

theorem u222 : Upper (D 7) (R 7) [12,48,65,160,384,64,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b223 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 1, region := 136, targets := 64 }], pairs := [(1,0),(3,0),(3,6),(4,0)], upper := (rows 13 50 69 168 400 96 66 130 257), lower := (rows 13 50 69 168 400 96 66 130 256), losses := [] }

theorem u223 : Upper (D 7) (R 7) [12,48,65,160,384,64,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b224 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 264, targets := 193 },{ cop := 8, region := 237, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 13 50 69 296 146 96 192 129 258), lower := (rows 13 50 69 296 146 96 192 129 256), losses := [] }

theorem u224 : Upper (D 7) (R 7) [12,48,65,288,130,64,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b225 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 269, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 69 296 146 96 192 130 257), lower := (rows 13 50 69 296 146 96 192 130 256), losses := [] }

theorem u225 : Upper (D 7) (R 7) [12,48,65,288,130,64,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b225 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b226 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 144, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 13 50 70 168 145 96 320 129 258), lower := (rows 13 50 70 168 145 96 320 129 256), losses := [] }

theorem u226 : Upper (D 7) (R 7) [12,48,66,160,129,64,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b226 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b227 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 136, targets := 65 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,7),(3,0),(3,6)], upper := (rows 13 50 70 168 145 96 320 130 257), lower := (rows 13 50 70 168 145 96 320 130 256), losses := [] }

theorem u227 : Upper (D 7) (R 7) [12,48,66,160,129,64,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b227 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b228 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 324, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 13 50 70 168 208 33 320 129 258), lower := (rows 13 50 70 168 208 33 320 129 256), losses := [] }

theorem u228 : Upper (D 7) (R 7) [12,48,66,160,192,1,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b228 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b229 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 136, targets := 65 },{ cop := 2, region := 144, targets := 1 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 13 50 70 168 208 33 320 130 257), lower := (rows 13 50 70 168 208 33 320 130 256), losses := [] }

theorem u229 : Upper (D 7) (R 7) [12,48,66,160,192,1,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b229 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b230 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 302, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 13 50 70 168 208 288 65 129 258), lower := (rows 13 50 70 168 208 288 65 129 256), losses := [] }

theorem u230 : Upper (D 7) (R 7) [12,48,66,160,192,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b230 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b231 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 136, targets := 65 },{ cop := 2, region := 144, targets := 1 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 13 50 70 168 208 288 65 130 257), lower := (rows 13 50 70 168 208 288 65 130 256), losses := [] }

theorem u231 : Upper (D 7) (R 7) [12,48,66,160,192,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b231 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b232 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 272, targets := 161 },{ cop := 2, region := 169, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 13 50 70 168 336 33 192 129 258), lower := (rows 13 50 70 168 336 33 192 129 256), losses := [] }

theorem u232 : Upper (D 7) (R 7) [12,48,66,160,320,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b232 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b233 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 2, region := 169, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(3,6)], upper := (rows 13 50 70 168 336 33 192 130 257), lower := (rows 13 50 70 168 336 33 192 130 256), losses := [] }

theorem u233 : Upper (D 7) (R 7) [12,48,66,160,320,1,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b234 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 274, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 70 168 400 96 65 129 258), lower := (rows 13 50 70 168 400 96 65 129 256), losses := [] }

theorem u234 : Upper (D 7) (R 7) [12,48,66,160,384,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b235 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 136, targets := 65 }], pairs := [(0,6),(3,0),(3,6),(4,5)], upper := (rows 13 50 70 168 400 96 65 130 257), lower := (rows 13 50 70 168 400 96 65 130 256), losses := [{ target := 5, region := (rows 1 2 4 8 21 0 65 134 321), good := (rows 477 146 470 136 400 320 337 130 256) },{ target := 6, region := (rows 5 42 4 42 117 32 0 175 325), good := (rows 415 186 415 186 400 442 401 138 256) }] }

theorem u235 : Upper (D 7) (R 7) [12,48,66,160,384,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b236 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 425, targets := 2 }], pairs := [(0,1),(2,5),(3,0),(3,1)], upper := (rows 13 50 70 392 146 96 65 129 288), lower := (rows 13 50 70 392 146 96 65 129 256), losses := [{ target := 0, region := (rows 0 2 4 152 16 100 64 128 359), good := (rows 300 314 358 392 410 352 352 392 256) },{ target := 5, region := (rows 1 2 20 8 20 0 193 193 256), good := (rows 221 22 214 456 214 192 193 193 256) }] }

theorem u236 : Upper (D 7) (R 7) [12,48,66,384,130,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b237 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 70 392 146 96 65 160 257), lower := (rows 13 50 70 392 146 96 65 160 256), losses := [] }

theorem u237 : Upper (D 7) (R 7) [12,48,66,384,130,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b238 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 68, targets := 129 }], pairs := [(2,0),(2,1),(2,7),(3,0)], upper := (rows 13 50 100 392 208 33 66 129 258), lower := (rows 13 50 100 392 208 33 66 129 256), losses := [{ target := 0, region := (rows 0 2 6 24 16 32 66 128 322), good := (rows 12 382 356 392 472 32 326 128 256) },{ target := 1, region := (rows 1 0 20 8 20 161 64 161 256), good := (rows 189 180 244 424 244 161 64 161 256) }] }

theorem u238 : Upper (D 7) (R 7) [12,48,96,384,192,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b239 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 301, targets := 2 },{ cop := 5, region := 210, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 50 100 392 208 33 66 130 257), lower := (rows 13 50 100 392 208 33 66 130 256), losses := [] }

theorem u239 : Upper (D 7) (R 7) [12,48,96,384,192,1,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u239
end Delivery.IrregularNine14.P07
