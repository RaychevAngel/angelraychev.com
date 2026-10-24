import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0000

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b240 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 155, targets := 256 },{ cop := 4, region := 356, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8),(4,8)], upper := (rows 7 11 100 168 145 288 320 208 336), lower := (rows 7 11 100 168 145 288 320 128 256), losses := [] }

theorem u240 : Upper (D 9) (R 9) [6,9,96,160,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b240 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b241 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 87, targets := 256 },{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,8)], upper := (rows 7 11 100 168 208 288 65 400 272), lower := (rows 7 11 100 168 208 288 65 128 256), losses := [] }

theorem u241 : Upper (D 9) (R 9) [6,9,96,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b241 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b242 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 7 11 100 168 208 288 80 385 257), lower := (rows 7 11 100 168 208 288 80 128 256), losses := [] }

theorem u242 : Upper (D 9) (R 9) [6,9,96,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b242 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b243 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 155, targets := 256 },{ cop := 5, region := 68, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8),(4,8)], upper := (rows 7 11 100 168 208 288 320 145 273), lower := (rows 7 11 100 168 208 288 320 128 256), losses := [] }

theorem u243 : Upper (D 9) (R 9) [6,9,96,160,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b243 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b244 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 4, region := 228, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8)], upper := (rows 7 11 100 168 273 48 192 448 320), lower := (rows 7 11 100 168 273 48 192 128 256), losses := [] }

theorem u244 : Upper (D 9) (R 9) [6,9,96,160,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b244 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b245 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 139, targets := 256 },{ cop := 4, region := 100, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8)], upper := (rows 7 11 100 168 273 48 320 192 448), lower := (rows 7 11 100 168 273 48 320 128 256), losses := [] }

theorem u245 : Upper (D 9) (R 9) [6,9,96,160,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b245 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b246 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 139, targets := 256 },{ cop := 4, region := 100, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8)], upper := (rows 7 11 100 168 273 288 80 192 448), lower := (rows 7 11 100 168 273 288 80 128 256), losses := [] }

theorem u246 : Upper (D 9) (R 9) [6,9,96,160,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b246 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b247 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 4, region := 236, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,0)], upper := (rows 7 11 100 168 273 288 192 208 336), lower := (rows 7 11 100 168 273 288 192 128 256), losses := [] }

theorem u247 : Upper (D 9) (R 9) [6,9,96,160,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b247 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b248 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 5, region := 468, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 11 100 168 336 33 80 384 384), lower := (rows 7 11 100 168 336 33 80 128 256), losses := [] }

theorem u248 : Upper (D 9) (R 9) [6,9,96,160,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b248 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b249 : PairBound 9 := { available := 272, camps := [{ cop := 6, region := 47, targets := 256 },{ cop := 5, region := 468, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 7 11 100 168 336 33 192 400 272), lower := (rows 7 11 100 168 336 33 192 128 256), losses := [] }

theorem u249 : Upper (D 9) (R 9) [6,9,96,160,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b249 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b250 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 5, region := 468, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 7 11 100 168 336 33 320 144 400), lower := (rows 7 11 100 168 336 33 320 128 256), losses := [] }

theorem u250 : Upper (D 9) (R 9) [6,9,96,160,320,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b250 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b251 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 11 100 168 336 288 65 144 400), lower := (rows 7 11 100 168 336 288 65 128 256), losses := [] }

theorem u251 : Upper (D 9) (R 9) [6,9,96,160,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b251 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b252 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 84, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 7 11 100 168 336 288 80 129 385), lower := (rows 7 11 100 168 336 288 80 128 256), losses := [] }

theorem u252 : Upper (D 9) (R 9) [6,9,96,160,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b252 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b253 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 4, region := 36, targets := 129 }], pairs := [(0,8),(1,8),(2,0),(2,7),(2,8)], upper := (rows 7 11 100 168 336 288 192 145 273), lower := (rows 7 11 100 168 336 288 192 128 256), losses := [] }

theorem u253 : Upper (D 9) (R 9) [6,9,96,160,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b253 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b254 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 11 100 168 400 33 80 448 320), lower := (rows 7 11 100 168 400 33 80 128 256), losses := [] }

theorem u254 : Upper (D 9) (R 9) [6,9,96,160,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b254 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r255 : Route 9 := (fun mask => (mask,id))

def c255 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u255 : Upper (D 9) (R 9) [6,9,96,160,384,1,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,384,1,256] 13 (by decide) (choices 1) [16,64] r255 c255
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4
  · exact u5

def b256 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 11 100 168 400 288 65 208 336), lower := (rows 7 11 100 168 400 288 65 128 256), losses := [] }

theorem u256 : Upper (D 9) (R 9) [6,9,96,160,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b256 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b257 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 139, targets := 256 },{ cop := 4, region := 100, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8)], upper := (rows 7 11 100 168 400 288 80 193 321), lower := (rows 7 11 100 168 400 288 80 128 256), losses := [] }

theorem u257 : Upper (D 9) (R 9) [6,9,96,160,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b257 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b258 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5),(4,5)], upper := (rows 7 11 100 392 145 48 96 448 320), lower := (rows 7 11 100 392 145 48 96 128 256), losses := [] }

theorem u258 : Upper (D 9) (R 9) [6,9,96,384,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b258 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b259 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 364, targets := 1 },{ cop := 4, region := 356, targets := 128 }], pairs := [(2,0),(2,7),(3,0),(4,8)], upper := (rows 7 11 100 392 145 48 320 224 352), lower := (rows 7 11 100 392 145 48 320 128 256), losses := [{ target := 8, region := (rows 1 2 4 8 17 51 64 132 0), good := (rows 183 59 228 136 177 48 64 128 0) }] }

theorem u259 : Upper (D 9) (R 9) [6,9,96,384,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b259 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b260 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(3,6),(4,6)], upper := (rows 7 11 100 392 145 96 320 176 304), lower := (rows 7 11 100 392 145 96 320 128 256), losses := [] }

theorem u260 : Upper (D 9) (R 9) [6,9,96,384,129,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b260 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b261 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 6, region := 444, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7),(3,0)], upper := (rows 7 11 100 392 176 288 65 208 336), lower := (rows 7 11 100 392 176 288 65 128 256), losses := [] }

theorem u261 : Upper (D 9) (R 9) [6,9,96,384,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b261 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b262 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 395, targets := 32 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,5),(1,5),(2,0),(3,5)], upper := (rows 7 11 100 392 176 288 80 193 321), lower := (rows 7 11 100 392 176 288 80 128 256), losses := [] }

theorem u262 : Upper (D 9) (R 9) [6,9,96,384,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b262 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b263 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 3, region := 434, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(2,8),(3,8)], upper := (rows 7 26 37 73 176 288 192 448 320), lower := (rows 7 26 37 73 176 288 192 128 256), losses := [] }

theorem u263 : Upper (D 9) (R 9) [6,24,33,65,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b263 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b264 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,6),(1,0),(2,6),(3,5),(4,0)], upper := (rows 7 26 37 73 176 288 320 192 448), lower := (rows 7 26 37 73 176 288 320 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 352 0 128 256), good := (rows 7 31 37 45 176 288 288 128 288) }] }

theorem u264 : Upper (D 9) (R 9) [6,24,33,65,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b264 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b265 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 72, targets := 384 },{ cop := 3, region := 402, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,7),(3,8)], upper := (rows 7 26 37 73 208 288 96 384 384), lower := (rows 7 26 37 73 208 288 96 128 256), losses := [] }

theorem u265 : Upper (D 9) (R 9) [6,24,33,65,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b265 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b266 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 37 73 208 288 192 416 288), lower := (rows 7 26 37 73 208 288 192 128 256), losses := [] }

theorem u266 : Upper (D 9) (R 9) [6,24,33,65,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b266 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b267 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 3, region := 434, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,5),(4,0)], upper := (rows 7 26 37 73 208 288 320 160 416), lower := (rows 7 26 37 73 208 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 16 0 352 128 256), good := (rows 15 26 77 73 208 320 320 128 320) }] }

theorem u267 : Upper (D 9) (R 9) [6,24,33,65,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b267 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b268 : PairBound 9 := { available := 384, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(3,0),(4,0)], upper := (rows 7 26 37 104 208 288 65 384 384), lower := (rows 7 26 37 104 208 288 65 128 256), losses := [] }

theorem u268 : Upper (D 9) (R 9) [6,24,33,96,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b268 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b269 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 7 26 37 104 208 288 192 385 257), lower := (rows 7 26 37 104 208 288 192 128 256), losses := [] }

theorem u269 : Upper (D 9) (R 9) [6,24,33,96,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b269 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b270 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 151, targets := 256 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(4,8)], upper := (rows 7 26 37 104 208 288 320 129 385), lower := (rows 7 26 37 104 208 288 320 128 256), losses := [] }

theorem u270 : Upper (D 9) (R 9) [6,24,33,96,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b270 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b271 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 0, region := 484, targets := 1 },{ cop := 6, region := 292, targets := 128 }], pairs := [(1,5),(1,7),(2,0),(2,7),(4,5)], upper := (rows 7 26 100 41 145 288 192 448 320), lower := (rows 7 26 100 41 145 288 192 128 256), losses := [{ target := 7, region := (rows 1 18 68 25 16 357 64 0 324), good := (rows 303 26 356 41 59 288 356 0 288) }] }

theorem u271 : Upper (D 9) (R 9) [6,24,96,33,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b271 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b272 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 155, targets := 256 },{ cop := 3, region := 466, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(3,8),(4,8)], upper := (rows 7 26 100 41 145 288 320 192 448), lower := (rows 7 26 100 41 145 288 320 128 256), losses := [] }

theorem u272 : Upper (D 9) (R 9) [6,24,96,33,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b272 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b273 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 3, region := 68, targets := 384 },{ cop := 6, region := 420, targets := 1 }], pairs := [(1,5),(2,0),(2,7),(2,8),(4,5)], upper := (rows 7 26 100 41 208 288 65 384 384), lower := (rows 7 26 100 41 208 288 65 128 256), losses := [] }

theorem u273 : Upper (D 9) (R 9) [6,24,96,33,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b273 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b274 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 7 26 100 41 208 288 192 385 257), lower := (rows 7 26 100 41 208 288 192 128 256), losses := [] }

theorem u274 : Upper (D 9) (R 9) [6,24,96,33,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b274 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b275 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 155, targets := 256 },{ cop := 3, region := 466, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(3,8),(4,8)], upper := (rows 7 26 100 41 208 288 320 129 385), lower := (rows 7 26 100 41 208 288 320 128 256), losses := [] }

theorem u275 : Upper (D 9) (R 9) [6,24,96,33,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b275 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b276 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 3, region := 466, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,8),(3,8)], upper := (rows 7 26 100 41 400 160 65 448 320), lower := (rows 7 26 100 41 400 160 65 128 256), losses := [] }

theorem u276 : Upper (D 9) (R 9) [6,24,96,33,384,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b276 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b277 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 3, region := 324, targets := 128 },{ cop := 4, region := 100, targets := 1 }], pairs := [(0,7),(1,5),(2,0),(2,7),(4,5)], upper := (rows 7 26 100 41 400 160 320 193 321), lower := (rows 7 26 100 41 400 160 320 128 256), losses := [{ target := 7, region := (rows 3 2 12 8 16 32 347 0 267), good := (rows 327 351 100 365 336 32 320 0 320) }] }

theorem u277 : Upper (D 9) (R 9) [6,24,96,33,384,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b277 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b278 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 26 100 137 176 288 65 448 320), lower := (rows 7 26 100 137 176 288 65 128 256), losses := [] }

theorem u278 : Upper (D 9) (R 9) [6,24,96,129,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b278 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b279 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 155, targets := 256 },{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 26 100 137 176 288 320 193 321), lower := (rows 7 26 100 137 176 288 320 128 256), losses := [] }

theorem u279 : Upper (D 9) (R 9) [6,24,96,129,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b279 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b280 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 0, region := 484, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 26 100 137 273 96 192 416 288), lower := (rows 7 26 100 137 273 96 192 128 256), losses := [] }

theorem u280 : Upper (D 9) (R 9) [6,24,96,129,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b280 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b281 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 484, targets := 1 },{ cop := 5, region := 324, targets := 128 },{ cop := 6, region := 164, targets := 256 }], pairs := [(1,7),(2,0),(2,7),(2,8),(4,7)], upper := (rows 7 26 100 137 273 160 320 224 352), lower := (rows 7 26 100 137 273 160 320 128 256), losses := [{ target := 7, region := (rows 1 10 36 8 17 32 373 0 292), good := (rows 343 90 356 91 337 356 320 0 320) }] }

theorem u281 : Upper (D 9) (R 9) [6,24,96,129,257,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b281 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b282 : PairBound 9 := { available := 320, camps := [{ cop := 5, region := 468, targets := 1 },{ cop := 0, region := 456, targets := 32 },{ cop := 2, region := 272, targets := 128 },{ cop := 3, region := 100, targets := 256 }], pairs := [(2,0),(2,8),(3,5),(4,0),(4,7)], upper := (rows 7 26 100 137 304 33 192 448 320), lower := (rows 7 26 100 137 304 33 192 128 256), losses := [] }

theorem u282 : Upper (D 9) (R 9) [6,24,96,129,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b282 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b283 : PairBound 9 := { available := 192, camps := [{ cop := 5, region := 468, targets := 1 },{ cop := 0, region := 456, targets := 32 },{ cop := 4, region := 68, targets := 128 }], pairs := [(1,5),(2,0),(2,7),(3,5),(4,0)], upper := (rows 7 26 100 137 304 33 320 192 448), lower := (rows 7 26 100 137 304 33 320 128 256), losses := [{ target := 5, region := (rows 1 18 4 41 16 0 511 511 511), good := (rows 463 474 460 457 474 457 448 448 448) }] }

theorem u283 : Upper (D 9) (R 9) [6,24,96,129,288,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b283 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b284 : PairBound 9 := { available := 320, camps := [{ cop := 6, region := 436, targets := 1 },{ cop := 0, region := 456, targets := 32 },{ cop := 2, region := 272, targets := 128 },{ cop := 3, region := 100, targets := 256 }], pairs := [(2,0),(2,8),(3,5),(4,0),(4,7)], upper := (rows 7 26 100 137 304 160 65 448 320), lower := (rows 7 26 100 137 304 160 65 128 256), losses := [] }

theorem u284 : Upper (D 9) (R 9) [6,24,96,129,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b284 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r285 : Route 9 := (fun mask => (mask,id))

def c285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u285 : Upper (D 9) (R 9) [6,24,96,129,288,128,256] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288,128,256] 13 (by decide) (choices 1) [1,64] r285 c285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6
  · exact u7

def b286 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 357, targets := 128 },{ cop := 5, region := 468, targets := 1 }], pairs := [(0,7),(1,0),(2,0),(2,7),(4,0)], upper := (rows 7 26 100 137 400 33 320 224 352), lower := (rows 7 26 100 137 400 33 320 128 256), losses := [{ target := 0, region := (rows 0 10 36 8 53 32 373 164 292), good := (rows 470 90 500 218 464 500 320 128 320) }] }

theorem u286 : Upper (D 9) (R 9) [6,24,96,129,384,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b286 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b287 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 26 100 137 400 96 320 161 289), lower := (rows 7 26 100 137 400 96 320 128 256), losses := [] }

theorem u287 : Upper (D 9) (R 9) [6,24,96,129,384,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b287 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b288 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 26 100 168 208 33 320 385 257), lower := (rows 7 26 100 168 208 33 320 128 256), losses := [] }

theorem u288 : Upper (D 9) (R 9) [6,24,96,160,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b288 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b289 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 155, targets := 256 },{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 26 100 168 208 288 320 129 257), lower := (rows 7 26 100 168 208 288 320 128 256), losses := [] }

theorem u289 : Upper (D 9) (R 9) [6,24,96,160,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b289 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b290 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 101, targets := 384 },{ cop := 2, region := 410, targets := 1 }], pairs := [(0,7),(0,8),(1,0),(2,7),(2,8)], upper := (rows 7 26 100 168 336 33 65 384 384), lower := (rows 7 26 100 168 336 33 65 128 256), losses := [] }

theorem u290 : Upper (D 9) (R 9) [6,24,96,160,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b290 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b291 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 68, targets := 257 },{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 424, targets := 64 }], pairs := [(1,5),(2,0),(2,8),(3,6),(4,5)], upper := (rows 7 26 100 168 336 33 192 385 257), lower := (rows 7 26 100 168 336 33 192 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 61 0 237 161 289), good := (rows 471 90 468 474 336 465 192 192 256) }] }

theorem u291 : Upper (D 9) (R 9) [6,24,96,160,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b291 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b292 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 26 100 168 336 33 320 129 385), lower := (rows 7 26 100 168 336 33 320 128 256), losses := [] }

theorem u292 : Upper (D 9) (R 9) [6,24,96,160,320,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b292 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b293 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 2, region := 410, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(2,8),(3,8)], upper := (rows 7 26 100 168 400 33 65 448 320), lower := (rows 7 26 100 168 400 33 65 128 256), losses := [] }

theorem u293 : Upper (D 9) (R 9) [6,24,96,160,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b293 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r294 : Route 9 := (fun mask => (mask,id))

def c294 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u294 : Upper (D 9) (R 9) [6,24,96,160,384,1,256] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,384,1,256] 13 (by decide) (choices 1) [1,64] r294 c294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8
  · exact u9

def b295 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 35 69 56 208 288 72 384 384), lower := (rows 7 35 69 56 208 288 72 128 256), losses := [] }

theorem u295 : Upper (D 9) (R 9) [6,33,65,48,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b295 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b296 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,7)], upper := (rows 7 35 69 56 208 288 192 392 264), lower := (rows 7 35 69 56 208 288 192 128 256), losses := [] }

theorem u296 : Upper (D 9) (R 9) [6,33,65,48,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b296 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b297 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,0)], upper := (rows 7 35 69 56 208 288 320 136 392), lower := (rows 7 35 69 56 208 288 320 128 256), losses := [] }

theorem u297 : Upper (D 9) (R 9) [6,33,65,48,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b297 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b298 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 7 35 69 152 304 160 72 448 320), lower := (rows 7 35 69 152 304 160 72 128 256), losses := [] }

theorem u298 : Upper (D 9) (R 9) [6,33,65,144,288,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b298 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b299 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,0)], upper := (rows 7 35 69 152 304 160 320 200 328), lower := (rows 7 35 69 152 304 160 320 128 256), losses := [] }

theorem u299 : Upper (D 9) (R 9) [6,33,65,144,288,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b299 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u299
end Delivery.IrregularNine14.P09
