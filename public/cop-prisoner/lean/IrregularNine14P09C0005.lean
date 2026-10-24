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

def b300 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 69 168 208 40 320 400 272), lower := (rows 7 35 69 168 208 40 320 128 256), losses := [] }

theorem u300 : Upper (D 9) (R 9) [6,33,65,160,192,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b300 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b301 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 69 168 208 48 320 392 264), lower := (rows 7 35 69 168 208 48 320 128 256), losses := [] }

theorem u301 : Upper (D 9) (R 9) [6,33,65,160,192,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b301 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b302 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,0)], upper := (rows 7 35 69 168 208 288 320 152 280), lower := (rows 7 35 69 168 208 288 320 128 256), losses := [] }

theorem u302 : Upper (D 9) (R 9) [6,33,65,160,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b302 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b303 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 35 69 168 400 288 72 208 336), lower := (rows 7 35 69 168 400 288 72 128 256), losses := [] }

theorem u303 : Upper (D 9) (R 9) [6,33,65,160,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b303 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b304 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 103, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 168 400 288 80 200 328), lower := (rows 7 35 69 168 400 288 80 128 256), losses := [] }

theorem u304 : Upper (D 9) (R 9) [6,33,65,160,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b304 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b305 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 76 25 176 288 192 448 320), lower := (rows 7 35 76 25 176 288 192 128 256), losses := [] }

theorem u305 : Upper (D 9) (R 9) [6,33,72,17,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b305 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b306 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 500, targets := 1 },{ cop := 3, region := 452, targets := 32 }], pairs := [(0,6),(1,6),(2,0),(2,5),(4,0)], upper := (rows 7 35 76 25 176 288 320 192 448), lower := (rows 7 35 76 25 176 288 320 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 352 0 128 256), good := (rows 7 35 47 25 176 288 288 128 288) }] }

theorem u306 : Upper (D 9) (R 9) [6,33,72,17,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b306 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b307 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 500, targets := 1 },{ cop := 2, region := 400, targets := 32 }], pairs := [(0,6),(1,6),(2,0),(4,0),(4,5)], upper := (rows 7 35 76 25 208 288 96 384 384), lower := (rows 7 35 76 25 208 288 96 128 256), losses := [] }

theorem u307 : Upper (D 9) (R 9) [6,33,72,17,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b307 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b308 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 76 25 208 288 192 416 288), lower := (rows 7 35 76 25 208 288 192 128 256), losses := [] }

theorem u308 : Upper (D 9) (R 9) [6,33,72,17,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b308 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b309 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 500, targets := 1 }], pairs := [(0,6),(0,7),(1,6),(2,0),(4,0)], upper := (rows 7 35 76 25 208 288 320 160 416), lower := (rows 7 35 76 25 208 288 320 128 256), losses := [{ target := 7, region := (rows 29 22 20 24 16 352 352 0 256), good := (rows 7 99 111 31 127 352 352 0 352) }] }

theorem u309 : Upper (D 9) (R 9) [6,33,72,17,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b309 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b310 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 4, region := 364, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(2,0),(3,0),(4,5)], upper := (rows 7 35 76 56 145 288 192 448 320), lower := (rows 7 35 76 56 145 288 192 128 256), losses := [] }

theorem u310 : Upper (D 9) (R 9) [6,33,72,48,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b310 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b311 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 364, targets := 1 },{ cop := 0, region := 464, targets := 32 },{ cop := 3, region := 452, targets := 32 }], pairs := [(0,6),(2,0),(2,5),(3,0),(4,5)], upper := (rows 7 35 76 56 145 288 320 192 448), lower := (rows 7 35 76 56 145 288 320 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 352 0 128 256), good := (rows 7 35 47 56 145 288 288 128 288) }] }

theorem u311 : Upper (D 9) (R 9) [6,33,72,48,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b311 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b312 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 35 76 56 208 288 65 384 384), lower := (rows 7 35 76 56 208 288 65 128 256), losses := [] }

theorem u312 : Upper (D 9) (R 9) [6,33,72,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b312 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b313 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 7 35 76 56 208 288 192 385 257), lower := (rows 7 35 76 56 208 288 192 128 256), losses := [] }

theorem u313 : Upper (D 9) (R 9) [6,33,72,48,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b313 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b314 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(1,6),(2,0),(3,0),(4,5)], upper := (rows 7 35 76 56 208 288 320 129 385), lower := (rows 7 35 76 56 208 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 16 352 352 128 256), good := (rows 6 98 108 124 252 352 352 128 352) }] }

theorem u314 : Upper (D 9) (R 9) [6,33,72,48,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b314 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b315 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 1, region := 80, targets := 128 }], pairs := [(0,6),(1,6),(3,6),(4,7)], upper := (rows 7 35 76 137 112 288 80 384 384), lower := (rows 7 35 76 137 112 288 80 128 256), losses := [] }

theorem u315 : Upper (D 9) (R 9) [6,33,72,129,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b315 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b316 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0),(4,7)], upper := (rows 7 35 76 137 112 288 192 400 272), lower := (rows 7 35 76 137 112 288 192 128 256), losses := [] }

theorem u316 : Upper (D 9) (R 9) [6,33,72,129,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b316 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b317 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 143, targets := 256 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 7 35 76 137 112 288 320 144 400), lower := (rows 7 35 76 137 112 288 320 128 256), losses := [] }

theorem u317 : Upper (D 9) (R 9) [6,33,72,129,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b317 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b318 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 76 137 176 288 80 448 320), lower := (rows 7 35 76 137 176 288 80 128 256), losses := [] }

theorem u318 : Upper (D 9) (R 9) [6,33,72,129,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b318 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b319 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(0,6),(0,7),(1,6),(2,0),(4,0)], upper := (rows 7 35 76 137 176 288 320 208 336), lower := (rows 7 35 76 137 176 288 320 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 352 0 128 256), good := (rows 7 35 47 137 176 288 288 128 288) },{ target := 7, region := (rows 5 6 4 8 16 368 368 0 272), good := (rows 7 99 111 9 368 352 352 0 352) }] }

theorem u319 : Upper (D 9) (R 9) [6,33,72,129,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b319 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b320 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 84, targets := 288 }], pairs := [(2,5),(2,8),(4,5),(4,8)], upper := (rows 7 35 76 137 208 288 80 416 288), lower := (rows 7 35 76 137 208 288 80 128 256), losses := [] }

theorem u320 : Upper (D 9) (R 9) [6,33,72,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b320 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r321 : Route 9 := (fun mask => (mask,id))

def c321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 8 | 32 => 5 | 64 => 6 | _ => 0)

theorem u321 : Upper (D 9) (R 9) [6,33,72,129,192,256,32] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,192,256,32] 13 (by decide) (choices 1) [256] r321 c321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u10

def b322 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(0,6),(0,7),(1,6),(2,0),(4,0)], upper := (rows 7 35 76 137 208 288 320 176 304), lower := (rows 7 35 76 137 208 288 320 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 368 0 144 272), good := (rows 7 35 47 137 432 288 288 128 288) },{ target := 7, region := (rows 5 6 4 8 16 368 368 0 272), good := (rows 7 99 111 9 368 352 352 0 352) }] }

theorem u322 : Upper (D 9) (R 9) [6,33,72,129,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b322 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b323 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 392, targets := 96 },{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(4,0)], upper := (rows 7 35 76 137 336 48 96 384 384), lower := (rows 7 35 76 137 336 48 96 128 256), losses := [] }

theorem u323 : Upper (D 9) (R 9) [6,33,72,129,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b323 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b324 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 35 76 137 336 48 192 416 288), lower := (rows 7 35 76 137 336 48 192 128 256), losses := [] }

theorem u324 : Upper (D 9) (R 9) [6,33,72,129,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b324 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b325 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 76 137 336 48 320 160 416), lower := (rows 7 35 76 137 336 48 320 128 256), losses := [] }

theorem u325 : Upper (D 9) (R 9) [6,33,72,129,320,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b325 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b326 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 35 76 137 336 288 80 160 416), lower := (rows 7 35 76 137 336 288 80 128 256), losses := [] }

theorem u326 : Upper (D 9) (R 9) [6,33,72,129,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b326 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b327 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 2, region := 400, targets := 32 },{ cop := 5, region := 80, targets := 128 }], pairs := [(2,0),(3,5),(4,0),(4,5),(4,7)], upper := (rows 7 35 76 137 336 288 96 144 400), lower := (rows 7 35 76 137 336 288 96 128 256), losses := [{ target := 5, region := (rows 1 2 4 11 84 0 64 213 341), good := (rows 415 395 476 393 464 256 464 128 256) }] }

theorem u327 : Upper (D 9) (R 9) [6,33,72,129,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b327 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b328 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0),(4,7)], upper := (rows 7 35 76 137 336 288 192 176 304), lower := (rows 7 35 76 137 336 288 192 128 256), losses := [] }

theorem u328 : Upper (D 9) (R 9) [6,33,72,129,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b328 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b329 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 76 137 400 48 96 448 320), lower := (rows 7 35 76 137 400 48 96 128 256), losses := [] }

theorem u329 : Upper (D 9) (R 9) [6,33,72,129,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b329 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r330 : Route 9 := (fun mask => (mask,id))

def c330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u330 : Upper (D 9) (R 9) [6,33,72,129,384,16,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,384,16,256] 13 (by decide) (choices 1) [32,64] r330 c330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11
  · exact u12

def b331 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0)], upper := (rows 7 35 76 137 400 288 80 224 352), lower := (rows 7 35 76 137 400 288 80 128 256), losses := [] }

theorem u331 : Upper (D 9) (R 9) [6,33,72,129,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b331 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r332 : Route 9 := (fun mask => (mask,id))

def c332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u332 : Upper (D 9) (R 9) [6,33,72,129,384,256,32] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,384,256,32] 13 (by decide) (choices 1) [16,64] r332 c332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13
  · exact u14

def b333 : PairBound 9 := { available := 384, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 1, region := 80, targets := 384 }], pairs := [(2,0),(3,0),(4,0),(4,7),(4,8)], upper := (rows 7 35 76 152 112 288 65 384 384), lower := (rows 7 35 76 152 112 288 65 128 256), losses := [] }

theorem u333 : Upper (D 9) (R 9) [6,33,72,144,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b333 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b334 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 33 }], pairs := [(0,7),(1,7),(2,0),(2,5),(4,7)], upper := (rows 7 35 76 152 112 288 192 385 257), lower := (rows 7 35 76 152 112 288 192 128 256), losses := [] }

theorem u334 : Upper (D 9) (R 9) [6,33,72,144,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b334 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b335 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 143, targets := 256 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 76 152 112 288 320 129 385), lower := (rows 7 35 76 152 112 288 320 128 256), losses := [] }

theorem u335 : Upper (D 9) (R 9) [6,33,72,144,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b335 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b336 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 236, targets := 1 },{ cop := 4, region := 34, targets := 64 },{ cop := 4, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(2,0),(3,0),(3,5)], upper := (rows 7 35 76 152 273 288 96 192 448), lower := (rows 7 35 76 152 273 288 96 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 64 196 324), good := (rows 415 27 460 152 281 256 448 128 256) }] }

theorem u336 : Upper (D 9) (R 9) [6,33,72,144,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b336 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b337 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 288 }], pairs := [(0,7),(1,7),(2,5),(2,8),(4,7)], upper := (rows 7 35 76 152 273 288 192 224 352), lower := (rows 7 35 76 152 273 288 192 128 256), losses := [] }

theorem u337 : Upper (D 9) (R 9) [6,33,72,144,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b337 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b338 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(3,0),(4,0)], upper := (rows 7 35 76 152 336 288 65 160 416), lower := (rows 7 35 76 152 336 288 65 128 256), losses := [] }

theorem u338 : Upper (D 9) (R 9) [6,33,72,144,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b338 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b339 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 5, region := 80, targets := 129 }], pairs := [(0,6),(1,6),(2,0),(4,0),(4,7)], upper := (rows 7 35 76 152 336 288 96 129 385), lower := (rows 7 35 76 152 336 288 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 304 304 378 128 256), good := (rows 70 114 76 252 368 368 112 128 368) }] }

theorem u339 : Upper (D 9) (R 9) [6,33,72,144,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b339 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b340 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 33 }], pairs := [(0,7),(1,7),(2,0),(2,5),(4,7)], upper := (rows 7 35 76 152 336 288 192 161 289), lower := (rows 7 35 76 152 336 288 192 128 256), losses := [] }

theorem u340 : Upper (D 9) (R 9) [6,33,72,144,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b340 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b341 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 7 35 76 168 145 288 80 448 320), lower := (rows 7 35 76 168 145 288 80 128 256), losses := [] }

theorem u341 : Upper (D 9) (R 9) [6,33,72,160,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b341 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b342 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 364, targets := 1 },{ cop := 0, region := 464, targets := 32 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,7),(2,0),(2,5),(3,0),(4,5)], upper := (rows 7 35 76 168 145 288 320 208 336), lower := (rows 7 35 76 168 145 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 19 0 371 147 275), good := (rows 471 467 76 204 465 320 320 128 320) }] }

theorem u342 : Upper (D 9) (R 9) [6,33,72,160,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b342 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b343 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 87, targets := 256 },{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,8)], upper := (rows 7 35 76 168 208 288 65 400 272), lower := (rows 7 35 76 168 208 288 65 128 256), losses := [] }

theorem u343 : Upper (D 9) (R 9) [6,33,72,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b343 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b344 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 7 35 76 168 208 288 80 385 257), lower := (rows 7 35 76 168 208 288 80 128 256), losses := [] }

theorem u344 : Upper (D 9) (R 9) [6,33,72,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b344 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b345 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(2,0),(2,5),(3,0),(4,0),(4,5)], upper := (rows 7 35 76 168 208 288 320 145 273), lower := (rows 7 35 76 168 208 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 24 352 352 128 256), good := (rows 6 98 124 252 252 352 352 128 352) },{ target := 5, region := (rows 1 2 12 8 27 0 355 131 259), good := (rows 471 467 92 220 208 320 320 128 320) }] }

theorem u345 : Upper (D 9) (R 9) [6,33,72,160,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b345 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b346 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 7 35 76 168 336 48 65 384 384), lower := (rows 7 35 76 168 336 48 65 128 256), losses := [] }

theorem u346 : Upper (D 9) (R 9) [6,33,72,160,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b346 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b347 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 71, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,7)], upper := (rows 7 35 76 168 336 48 192 385 257), lower := (rows 7 35 76 168 336 48 192 128 256), losses := [] }

theorem u347 : Upper (D 9) (R 9) [6,33,72,160,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b347 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b348 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 76 168 336 48 320 129 385), lower := (rows 7 35 76 168 336 48 320 128 256), losses := [] }

theorem u348 : Upper (D 9) (R 9) [6,33,72,160,320,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b348 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b349 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 35 76 168 336 288 65 144 400), lower := (rows 7 35 76 168 336 288 65 128 256), losses := [] }

theorem u349 : Upper (D 9) (R 9) [6,33,72,160,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b349 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b350 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 5, region := 80, targets := 1 }], pairs := [(0,6),(1,6),(3,6),(4,0)], upper := (rows 7 35 76 168 336 288 80 129 385), lower := (rows 7 35 76 168 336 288 80 128 256), losses := [] }

theorem u350 : Upper (D 9) (R 9) [6,33,72,160,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b350 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b351 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 71, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 7 35 76 168 336 288 192 145 273), lower := (rows 7 35 76 168 336 288 192 128 256), losses := [] }

theorem u351 : Upper (D 9) (R 9) [6,33,72,160,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b351 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b352 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 35 76 168 400 288 65 208 336), lower := (rows 7 35 76 168 400 288 65 128 256), losses := [] }

theorem u352 : Upper (D 9) (R 9) [6,33,72,160,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b352 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b353 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 4, region := 108, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,0)], upper := (rows 7 35 76 168 400 288 80 193 321), lower := (rows 7 35 76 168 400 288 80 128 256), losses := [] }

theorem u353 : Upper (D 9) (R 9) [6,33,72,160,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b353 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b354 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 7 35 76 392 208 48 65 416 288), lower := (rows 7 35 76 392 208 48 65 128 256), losses := [] }

theorem u354 : Upper (D 9) (R 9) [6,33,72,384,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b354 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b355 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 7 35 76 392 208 48 96 385 257), lower := (rows 7 35 76 392 208 48 96 128 256), losses := [] }

theorem u355 : Upper (D 9) (R 9) [6,33,72,384,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b355 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b356 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 179, targets := 256 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(4,8)], upper := (rows 7 35 76 392 208 48 320 161 289), lower := (rows 7 35 76 392 208 48 320 128 256), losses := [] }

theorem u356 : Upper (D 9) (R 9) [6,33,72,384,192,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b356 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b357 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 88, targets := 384 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(3,7),(3,8),(4,7),(4,8)], upper := (rows 7 35 196 25 88 288 96 384 384), lower := (rows 7 35 196 25 88 288 96 128 256), losses := [] }

theorem u357 : Upper (D 9) (R 9) [6,33,192,17,72,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b357 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b358 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 35 196 25 88 288 192 416 288), lower := (rows 7 35 196 25 88 288 192 128 256), losses := [] }

theorem u358 : Upper (D 9) (R 9) [6,33,192,17,72,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b358 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b359 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 3, region := 500, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,5),(4,0)], upper := (rows 7 35 196 25 88 288 320 160 416), lower := (rows 7 35 196 25 88 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 4 11 18 0 352 128 256), good := (rows 31 91 196 25 88 320 320 128 320) }] }

theorem u359 : Upper (D 9) (R 9) [6,33,192,17,72,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b359 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u359
end Delivery.IrregularNine14.P09
