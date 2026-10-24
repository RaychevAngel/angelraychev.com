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

def b9240 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 37 259 76 152 112 34 192 131 259), lower := (rows 37 259 76 152 112 34 192 128 256), losses := [] }

theorem u9240 : Upper (D 7) (R 7) [36,257,72,144,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9241 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 259 76 168 82 34 65 144 400), lower := (rows 37 259 76 168 82 34 65 128 256), losses := [] }

theorem u9241 : Upper (D 7) (R 7) [36,257,72,160,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9242 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 259 76 168 82 34 80 129 385), lower := (rows 37 259 76 168 82 34 80 128 256), losses := [] }

theorem u9242 : Upper (D 7) (R 7) [36,257,72,160,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9242 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9243 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(4,7)], upper := (rows 37 259 76 168 82 34 192 145 273), lower := (rows 37 259 76 168 82 34 192 128 256), losses := [] }

theorem u9243 : Upper (D 7) (R 7) [36,257,72,160,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9244 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 85, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 37 259 76 168 208 34 65 146 274), lower := (rows 37 259 76 168 208 34 65 128 256), losses := [] }

theorem u9244 : Upper (D 7) (R 7) [36,257,72,160,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9245 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,5)], upper := (rows 37 259 76 168 208 34 66 145 273), lower := (rows 37 259 76 168 208 34 66 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 24 98 98 128 256), good := (rows 100 354 124 252 252 98 98 128 256) }] }

theorem u9245 : Upper (D 7) (R 7) [36,257,72,160,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9246 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 259 76 168 208 34 80 131 259), lower := (rows 37 259 76 168 208 34 80 128 256), losses := [] }

theorem u9246 : Upper (D 7) (R 7) [36,257,72,160,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9246 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9247 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 88, targets := 32 },{ cop := 1, region := 88, targets := 128 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 37 259 196 25 82 34 72 160 416), lower := (rows 37 259 196 25 82 34 72 128 256), losses := [] }

theorem u9247 : Upper (D 7) (R 7) [36,257,192,17,66,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9247 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9248 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 120, targets := 128 },{ cop := 1, region := 112, targets := 1 },{ cop := 3, region := 386, targets := 32 }], pairs := [(1,5),(3,7),(4,0),(4,7)], upper := (rows 37 259 196 25 82 34 96 136 392), lower := (rows 37 259 196 25 82 34 96 128 256), losses := [] }

theorem u9248 : Upper (D 7) (R 7) [36,257,192,17,66,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9249 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 25 82 34 192 168 296), lower := (rows 37 259 196 25 82 34 192 128 256), losses := [] }

theorem u9249 : Upper (D 7) (R 7) [36,257,192,17,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9250 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 173, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 259 196 25 82 40 66 160 416), lower := (rows 37 259 196 25 82 40 66 128 256), losses := [] }

theorem u9250 : Upper (D 7) (R 7) [36,257,192,17,66,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9250 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9251 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 386, targets := 96 },{ cop := 1, region := 120, targets := 128 }], pairs := [(1,5),(1,6),(3,7)], upper := (rows 37 259 196 25 82 40 96 130 386), lower := (rows 37 259 196 25 82 40 96 128 256), losses := [] }

theorem u9251 : Upper (D 7) (R 7) [36,257,192,17,66,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9251 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9252 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 259 196 25 82 40 192 162 290), lower := (rows 37 259 196 25 82 40 192 128 256), losses := [] }

theorem u9252 : Upper (D 7) (R 7) [36,257,192,17,66,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9252 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9253 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 88, targets := 32 },{ cop := 1, region := 88, targets := 128 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 37 259 196 25 88 34 66 160 416), lower := (rows 37 259 196 25 88 34 66 128 256), losses := [] }

theorem u9253 : Upper (D 7) (R 7) [36,257,192,17,72,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9254 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 37 259 196 25 88 34 96 130 386), lower := (rows 37 259 196 25 88 34 96 128 256), losses := [] }

theorem u9254 : Upper (D 7) (R 7) [36,257,192,17,72,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9255 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 25 88 34 192 162 290), lower := (rows 37 259 196 25 88 34 192 128 256), losses := [] }

theorem u9255 : Upper (D 7) (R 7) [36,257,192,17,72,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9256 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 141, targets := 2 },{ cop := 1, region := 120, targets := 128 }], pairs := [(0,1),(2,1),(3,1),(3,7)], upper := (rows 37 259 196 25 112 34 66 136 392), lower := (rows 37 259 196 25 112 34 66 128 256), losses := [] }

theorem u9256 : Upper (D 7) (R 7) [36,257,192,17,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9257 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 37 259 196 25 112 34 72 130 386), lower := (rows 37 259 196 25 112 34 72 128 256), losses := [] }

theorem u9257 : Upper (D 7) (R 7) [36,257,192,17,96,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9257 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9258 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 25 112 34 192 138 266), lower := (rows 37 259 196 25 112 34 192 128 256), losses := [] }

theorem u9258 : Upper (D 7) (R 7) [36,257,192,17,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9259 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 88, targets := 32 },{ cop := 1, region := 88, targets := 128 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 37 259 196 26 81 34 72 160 416), lower := (rows 37 259 196 26 81 34 72 128 256), losses := [] }

theorem u9259 : Upper (D 7) (R 7) [36,257,192,18,65,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9259 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9260 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 259 196 26 81 34 96 136 392), lower := (rows 37 259 196 26 81 34 96 128 256), losses := [] }

theorem u9260 : Upper (D 7) (R 7) [36,257,192,18,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9261 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 26 81 34 192 168 296), lower := (rows 37 259 196 26 81 34 192 128 256), losses := [] }

theorem u9261 : Upper (D 7) (R 7) [36,257,192,18,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9262 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 80, targets := 130 },{ cop := 1, region := 120, targets := 128 }], pairs := [(2,1),(3,7),(4,1),(4,7)], upper := (rows 37 259 196 26 112 34 65 136 392), lower := (rows 37 259 196 26 112 34 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 49 32 67 136 264), good := (rows 117 337 196 476 112 112 81 128 256) }] }

theorem u9262 : Upper (D 7) (R 7) [36,257,192,18,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9263 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 120, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 37 259 196 26 112 34 72 129 385), lower := (rows 37 259 196 26 112 34 72 128 256), losses := [] }

theorem u9263 : Upper (D 7) (R 7) [36,257,192,18,96,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9263 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9264 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 26 112 34 192 137 265), lower := (rows 37 259 196 26 112 34 192 128 256), losses := [] }

theorem u9264 : Upper (D 7) (R 7) [36,257,192,18,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9265 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 120, targets := 128 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,6),(3,7),(4,7)], upper := (rows 37 259 196 56 81 34 66 136 392), lower := (rows 37 259 196 56 81 34 66 128 256), losses := [] }

theorem u9265 : Upper (D 7) (R 7) [36,257,192,48,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9266 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 37 259 196 56 81 34 72 130 386), lower := (rows 37 259 196 56 81 34 72 128 256), losses := [] }

theorem u9266 : Upper (D 7) (R 7) [36,257,192,48,65,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9266 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9267 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 56 81 34 192 138 266), lower := (rows 37 259 196 56 81 34 192 128 256), losses := [] }

theorem u9267 : Upper (D 7) (R 7) [36,257,192,48,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9268 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 37 259 196 73 146 34 72 176 304), lower := (rows 37 259 196 73 146 34 72 128 256), losses := [] }

theorem u9268 : Upper (D 7) (R 7) [36,257,192,65,130,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9268 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9269 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 259 196 73 146 34 80 168 296), lower := (rows 37 259 196 73 146 34 80 128 256), losses := [] }

theorem u9269 : Upper (D 7) (R 7) [36,257,192,65,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9269 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9270 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 259 196 73 146 34 96 152 280), lower := (rows 37 259 196 73 146 34 96 128 256), losses := [] }

theorem u9270 : Upper (D 7) (R 7) [36,257,192,65,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9271 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 1, region := 72, targets := 32 },{ cop := 1, region := 72, targets := 128 }], pairs := [(1,6),(3,5),(3,7),(4,6)], upper := (rows 37 259 196 73 152 34 66 176 304), lower := (rows 37 259 196 73 152 34 66 128 256), losses := [] }

theorem u9271 : Upper (D 7) (R 7) [36,257,192,65,136,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9272 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 259 196 73 152 34 80 162 290), lower := (rows 37 259 196 73 152 34 80 128 256), losses := [] }

theorem u9272 : Upper (D 7) (R 7) [36,257,192,65,136,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9272 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9273 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 259 196 73 152 34 96 146 274), lower := (rows 37 259 196 73 152 34 96 128 256), losses := [] }

theorem u9273 : Upper (D 7) (R 7) [36,257,192,65,136,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9274 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 1, region := 72, targets := 32 },{ cop := 1, region := 72, targets := 128 }], pairs := [(1,6),(3,5),(3,7),(4,6)], upper := (rows 37 259 196 73 176 34 66 152 280), lower := (rows 37 259 196 73 176 34 66 128 256), losses := [] }

theorem u9274 : Upper (D 7) (R 7) [36,257,192,65,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9275 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 37 259 196 73 176 34 72 146 274), lower := (rows 37 259 196 73 176 34 72 128 256), losses := [] }

theorem u9275 : Upper (D 7) (R 7) [36,257,192,65,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9275 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9276 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 259 196 73 176 34 80 138 266), lower := (rows 37 259 196 73 176 34 80 128 256), losses := [] }

theorem u9276 : Upper (D 7) (R 7) [36,257,192,65,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9276 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9277 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 3, region := 180, targets := 1 }], pairs := [(1,6),(2,0),(4,6)], upper := (rows 37 259 196 74 146 40 65 176 304), lower := (rows 37 259 196 74 146 40 65 128 256), losses := [] }

theorem u9277 : Upper (D 7) (R 7) [36,257,192,66,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9277 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9278 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 259 196 74 146 40 80 161 289), lower := (rows 37 259 196 74 146 40 80 128 256), losses := [] }

theorem u9278 : Upper (D 7) (R 7) [36,257,192,66,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9278 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9279 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 37 259 196 74 146 40 96 145 273), lower := (rows 37 259 196 74 146 40 96 128 256), losses := [] }

theorem u9279 : Upper (D 7) (R 7) [36,257,192,66,130,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9279 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9280 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 180, targets := 1 },{ cop := 1, region := 72, targets := 32 },{ cop := 1, region := 72, targets := 128 }], pairs := [(2,0),(3,5),(3,7),(4,0)], upper := (rows 37 259 196 74 152 34 65 176 304), lower := (rows 37 259 196 74 152 34 65 128 256), losses := [] }

theorem u9280 : Upper (D 7) (R 7) [36,257,192,66,136,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9281 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 259 196 74 152 34 80 161 289), lower := (rows 37 259 196 74 152 34 80 128 256), losses := [] }

theorem u9281 : Upper (D 7) (R 7) [36,257,192,66,136,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9281 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9282 : Route 9 := (fun mask => (mask,id))

def c9282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9282 : Upper (D 7) (R 7) [36,257,192,66,136,2,32] 13 := by
  apply FastRouting.sound _ _ [36,257,192,66,136,2,32] 13 (by decide) (choices 1) [1,16] r9282 c9282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u737
  · exact u738

def b9283 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 180, targets := 1 },{ cop := 4, region := 69, targets := 2 }], pairs := [(0,1),(2,0),(2,1),(4,0)], upper := (rows 37 259 196 74 176 34 65 152 280), lower := (rows 37 259 196 74 176 34 65 128 256), losses := [] }

theorem u9283 : Upper (D 7) (R 7) [36,257,192,66,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9284 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 37 259 196 74 176 34 72 145 273), lower := (rows 37 259 196 74 176 34 72 128 256), losses := [] }

theorem u9284 : Upper (D 7) (R 7) [36,257,192,66,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9284 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9285 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 259 196 74 176 34 80 137 265), lower := (rows 37 259 196 74 176 34 80 128 256), losses := [] }

theorem u9285 : Upper (D 7) (R 7) [36,257,192,66,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9285 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9286 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 3, region := 180, targets := 1 }], pairs := [(1,6),(2,0),(4,6)], upper := (rows 37 259 196 74 176 40 65 146 274), lower := (rows 37 259 196 74 176 40 65 128 256), losses := [] }

theorem u9286 : Upper (D 7) (R 7) [36,257,192,66,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9286 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9287 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 181, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 259 196 74 176 40 66 145 273), lower := (rows 37 259 196 74 176 40 66 128 256), losses := [] }

theorem u9287 : Upper (D 7) (R 7) [36,257,192,66,160,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9287 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9288 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 37 259 196 74 176 40 80 131 259), lower := (rows 37 259 196 74 176 40 80 128 256), losses := [] }

theorem u9288 : Upper (D 7) (R 7) [36,257,192,66,160,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9288 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9289 : Route 9 := (fun mask => (mask,id))

def c9289 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9289 : Upper (D 7) (R 7) [36,257,192,80,160,2,1] 13 := by
  apply FastRouting.sound _ _ [36,257,192,80,160,2,1] 13 (by decide) (choices 1) [2,8] r9289 c9289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u739
  · exact u740

def b9290 : PairBound 9 := { available := 9, camps := [], pairs := [(2,0),(2,5),(3,0),(4,0)], upper := (rows 37 259 196 88 176 34 66 137 265), lower := (rows 37 259 196 88 176 34 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 29 20 98 98 128 256), good := (rows 124 362 252 124 252 98 98 128 256) },{ target := 5, region := (rows 1 2 20 24 16 0 98 128 256), good := (rows 69 323 196 92 220 66 66 128 256) }] }

theorem u9290 : Upper (D 7) (R 7) [36,257,192,80,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9291 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 259 196 88 176 34 72 131 259), lower := (rows 37 259 196 88 176 34 72 128 256), losses := [] }

theorem u9291 : Upper (D 7) (R 7) [36,257,192,80,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9291 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9292 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,0),(1,5),(4,0)], upper := (rows 37 266 7 25 82 160 96 192 448), lower := (rows 37 266 7 25 82 160 96 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 16 0 64 208 336), good := (rows 5 270 7 415 466 128 448 128 256) }] }

theorem u9292 : Upper (D 7) (R 7) [36,264,3,17,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9293 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,6),(1,0),(4,0)], upper := (rows 37 266 7 25 82 160 192 224 352), lower := (rows 37 266 7 25 82 160 192 128 256), losses := [{ target := 6, region := (rows 17 2 20 24 16 224 0 128 256), good := (rows 37 266 7 29 63 160 160 160 256) }] }

theorem u9293 : Upper (D 7) (R 7) [36,264,3,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9294 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 266 7 25 208 96 66 160 416), lower := (rows 37 266 7 25 208 96 66 128 256), losses := [] }

theorem u9294 : Upper (D 7) (R 7) [36,264,3,17,192,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9295 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5),(2,6)], upper := (rows 37 266 7 25 208 96 96 130 386), lower := (rows 37 266 7 25 208 96 96 128 256), losses := [] }

theorem u9295 : Upper (D 7) (R 7) [36,264,3,17,192,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9296 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 7 25 208 96 192 162 290), lower := (rows 37 266 7 25 208 96 192 128 256), losses := [] }

theorem u9296 : Upper (D 7) (R 7) [36,264,3,17,192,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9297 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 37 266 7 26 112 160 65 192 448), lower := (rows 37 266 7 26 112 160 65 128 256), losses := [] }

theorem u9297 : Upper (D 7) (R 7) [36,264,3,18,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9298 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 7 26 112 160 192 193 321), lower := (rows 37 266 7 26 112 160 192 128 256), losses := [] }

theorem u9298 : Upper (D 7) (R 7) [36,264,3,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9299 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 37 266 7 56 82 160 65 192 448), lower := (rows 37 266 7 56 82 160 65 128 256), losses := [] }

theorem u9299 : Upper (D 7) (R 7) [36,264,3,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9299
end Delivery.IrregularNine14.P07
