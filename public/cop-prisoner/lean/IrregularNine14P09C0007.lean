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

def b420 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 290, targets := 1 },{ cop := 3, region := 290, targets := 128 },{ cop := 4, region := 356, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(3,5),(4,5)], upper := (rows 7 42 52 73 145 288 192 448 320), lower := (rows 7 42 52 73 145 288 192 128 256), losses := [] }

theorem u420 : Upper (D 9) (R 9) [6,40,48,65,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b420 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b421 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 418, targets := 1 },{ cop := 3, region := 144, targets := 256 },{ cop := 4, region := 356, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(4,5),(4,8)], upper := (rows 7 42 52 73 145 288 320 192 448), lower := (rows 7 42 52 73 145 288 320 128 256), losses := [] }

theorem u421 : Upper (D 9) (R 9) [6,40,48,65,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b421 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b422 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 75, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 42 52 73 208 288 65 384 384), lower := (rows 7 42 52 73 208 288 65 128 256), losses := [] }

theorem u422 : Upper (D 9) (R 9) [6,40,48,65,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b422 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b423 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 7 42 52 73 208 288 192 385 257), lower := (rows 7 42 52 73 208 288 192 128 256), losses := [] }

theorem u423 : Upper (D 9) (R 9) [6,40,48,65,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b423 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b424 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 418, targets := 64 },{ cop := 3, region := 144, targets := 256 }], pairs := [(1,0),(1,6),(3,5),(4,5),(4,8)], upper := (rows 7 42 52 73 208 288 320 129 385), lower := (rows 7 42 52 73 208 288 320 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 352 352 128 256), good := (rows 6 106 116 106 244 352 352 128 352) }] }

theorem u424 : Upper (D 9) (R 9) [6,40,48,65,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b424 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b425 : PairBound 9 := { available := 384, camps := [{ cop := 6, region := 408, targets := 33 }], pairs := [(1,0),(3,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 52 200 336 33 65 384 384), lower := (rows 7 42 52 200 336 33 65 128 256), losses := [{ target := 0, region := (rows 0 6 6 88 88 32 64 511 511), good := (rows 390 446 446 472 472 416 472 384 384) }] }

theorem u425 : Upper (D 9) (R 9) [6,40,48,192,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b425 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b426 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 7 42 52 200 336 33 192 385 257), lower := (rows 7 42 52 200 336 33 192 128 256), losses := [] }

theorem u426 : Upper (D 9) (R 9) [6,40,48,192,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b426 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b427 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 404, targets := 32 },{ cop := 3, region := 434, targets := 64 },{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(1,6),(2,5),(4,5),(4,6)], upper := (rows 7 42 84 73 145 288 96 384 384), lower := (rows 7 42 84 73 145 288 96 128 256), losses := [] }

theorem u427 : Upper (D 9) (R 9) [6,40,80,65,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b427 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b428 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 76, targets := 288 },{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(2,5),(2,8),(3,5),(3,8)], upper := (rows 7 42 84 73 145 288 192 416 288), lower := (rows 7 42 84 73 145 288 192 128 256), losses := [] }

theorem u428 : Upper (D 9) (R 9) [6,40,80,65,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b428 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b429 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 3, region := 418, targets := 1 },{ cop := 4, region := 356, targets := 1 }], pairs := [(0,7),(1,0),(1,6),(2,0),(4,6)], upper := (rows 7 42 84 73 145 288 320 160 416), lower := (rows 7 42 84 73 145 288 320 128 256), losses := [{ target := 7, region := (rows 5 14 4 12 16 352 352 0 256), good := (rows 15 106 127 107 17 352 352 0 352) }] }

theorem u429 : Upper (D 9) (R 9) [6,40,80,65,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b429 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b430 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 79, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 42 84 73 176 288 65 384 384), lower := (rows 7 42 84 73 176 288 65 128 256), losses := [] }

theorem u430 : Upper (D 9) (R 9) [6,40,80,65,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b430 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b431 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 42 84 73 176 288 192 385 257), lower := (rows 7 42 84 73 176 288 192 128 256), losses := [] }

theorem u431 : Upper (D 9) (R 9) [6,40,80,65,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b431 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b432 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 0, region := 456, targets := 32 }], pairs := [(1,0),(1,6),(2,0),(3,5),(4,6)], upper := (rows 7 42 84 73 176 288 320 129 385), lower := (rows 7 42 84 73 176 288 320 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 352 352 128 256), good := (rows 6 106 116 106 244 352 352 128 352) }] }

theorem u432 : Upper (D 9) (R 9) [6,40,80,65,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b432 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r433 : Route 9 := (fun mask => (mask,id))

def c433 : Nat → Fin 9 := (fun mask => match mask with | 1 => 8 | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | _ => 0)

theorem u433 : Upper (D 9) (R 9) [6,40,80,129,160,64,256] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,160,64,256] 13 (by decide) (choices 1) [256] r433 c433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u19

def b434 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 6, region := 436, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 7 42 84 137 176 288 65 448 320), lower := (rows 7 42 84 137 176 288 65 128 256), losses := [] }

theorem u434 : Upper (D 9) (R 9) [6,40,80,129,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b434 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b435 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,7),(2,0),(2,5),(2,7),(3,5)], upper := (rows 7 42 84 137 176 288 320 193 321), lower := (rows 7 42 84 137 176 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 352 352 128 256), good := (rows 6 106 116 136 244 352 352 128 352) },{ target := 5, region := (rows 1 2 20 9 16 0 363 137 265), good := (rows 463 458 84 457 212 320 320 128 320) },{ target := 7, region := (rows 1 10 20 8 16 363 363 0 265), good := (rows 359 362 116 363 116 352 352 0 352) }] }

theorem u435 : Upper (D 9) (R 9) [6,40,80,129,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b435 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b436 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 408, targets := 96 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,7),(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 84 137 273 96 96 384 384), lower := (rows 7 42 84 137 273 96 96 128 256), losses := [] }

theorem u436 : Upper (D 9) (R 9) [6,40,80,129,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b436 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b437 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 98, targets := 1 },{ cop := 3, region := 98, targets := 256 },{ cop := 4, region := 228, targets := 1 }], pairs := [(1,0),(1,8),(2,0),(3,6),(4,6)], upper := (rows 7 42 84 137 273 96 192 416 288), lower := (rows 7 42 84 137 273 96 192 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 17 32 0 162 290), good := (rows 415 426 20 153 281 416 128 128 256) }] }

theorem u437 : Upper (D 9) (R 9) [6,40,80,129,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b437 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b438 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 171, targets := 256 },{ cop := 3, region := 354, targets := 1 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(2,0),(3,8)], upper := (rows 7 42 84 137 273 96 320 160 416), lower := (rows 7 42 84 137 273 96 320 128 256), losses := [] }

theorem u438 : Upper (D 9) (R 9) [6,40,80,129,257,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b438 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b439 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 354, targets := 1 },{ cop := 4, region := 228, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(2,8),(4,7)], upper := (rows 7 42 84 137 273 288 192 224 352), lower := (rows 7 42 84 137 273 288 192 128 256), losses := [{ target := 7, region := (rows 1 10 4 8 17 373 64 0 324), good := (rows 311 42 372 59 305 288 352 0 288) },{ target := 8, region := (rows 1 2 20 9 16 32 235 162 0), good := (rows 207 234 84 201 93 224 192 192 0) }] }

theorem u439 : Upper (D 9) (R 9) [6,40,80,129,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b439 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b440 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 3, region := 98, targets := 384 },{ cop := 0, region := 392, targets := 32 }], pairs := [(1,7),(1,8),(3,5),(4,0),(4,6)], upper := (rows 7 42 84 137 304 96 65 384 384), lower := (rows 7 42 84 137 304 96 65 128 256), losses := [] }

theorem u440 : Upper (D 9) (R 9) [6,40,80,129,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b440 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b441 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 98, targets := 257 },{ cop := 0, region := 392, targets := 32 },{ cop := 0, region := 392, targets := 64 }], pairs := [(1,0),(1,8),(3,5),(3,6),(4,6)], upper := (rows 7 42 84 137 304 96 192 385 257), lower := (rows 7 42 84 137 304 96 192 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 18 32 0 137 265), good := (rows 415 442 20 393 304 32 128 128 256) }] }

theorem u441 : Upper (D 9) (R 9) [6,40,80,129,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b441 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b442 : PairBound 9 := { available := 129, camps := [{ cop := 6, region := 52, targets := 129 },{ cop := 2, region := 171, targets := 256 }], pairs := [(0,8),(2,0),(2,7),(4,0),(4,7)], upper := (rows 7 42 84 137 304 96 320 129 385), lower := (rows 7 42 84 137 304 96 320 128 256), losses := [] }

theorem u442 : Upper (D 9) (R 9) [6,40,80,129,288,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b442 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b443 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 1, region := 400, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 42 84 137 400 96 65 416 288), lower := (rows 7 42 84 137 400 96 65 128 256), losses := [] }

theorem u443 : Upper (D 9) (R 9) [6,40,80,129,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b443 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b444 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 96 },{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 84 137 400 96 96 385 257), lower := (rows 7 42 84 137 400 96 96 128 256), losses := [] }

theorem u444 : Upper (D 9) (R 9) [6,40,80,129,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b444 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b445 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 171, targets := 256 },{ cop := 4, region := 68, targets := 129 }], pairs := [(0,8),(1,8),(2,0),(2,7),(3,8)], upper := (rows 7 42 84 137 400 96 320 161 289), lower := (rows 7 42 84 137 400 96 320 128 256), losses := [] }

theorem u445 : Upper (D 9) (R 9) [6,40,80,129,384,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b445 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b446 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 436, targets := 1 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(3,8),(4,0)], upper := (rows 7 42 84 137 400 288 65 224 352), lower := (rows 7 42 84 137 400 288 65 128 256), losses := [{ target := 0, region := (rows 0 10 68 8 85 373 64 196 324), good := (rows 438 42 500 186 432 288 500 128 288) },{ target := 8, region := (rows 1 2 4 9 16 32 73 130 0), good := (rows 207 234 84 201 144 32 73 128 0) }] }

theorem u446 : Upper (D 9) (R 9) [6,40,80,129,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b446 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r447 : Route 9 := (fun mask => (mask,id))

def c447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u447 : Upper (D 9) (R 9) [6,40,80,129,384,256,32] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,384,256,32] 13 (by decide) (choices 1) [1,64] r447 c447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20
  · exact u21

def b448 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 55, targets := 256 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,8)], upper := (rows 7 42 84 200 176 33 320 385 257), lower := (rows 7 42 84 200 176 33 320 128 256), losses := [] }

theorem u448 : Upper (D 9) (R 9) [6,40,80,192,160,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b448 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b449 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(2,0),(3,0),(3,5),(4,6)], upper := (rows 7 42 84 200 176 288 320 129 257), lower := (rows 7 42 84 200 176 288 320 128 256), losses := [{ target := 0, region := (rows 0 30 30 24 24 352 352 128 256), good := (rows 6 126 126 254 254 352 352 128 352) }] }

theorem u449 : Upper (D 9) (R 9) [6,40,80,192,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b449 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b450 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 2, region := 392, targets := 33 }], pairs := [(2,5),(3,0),(3,5),(4,0),(4,6)], upper := (rows 7 42 84 200 304 33 65 384 384), lower := (rows 7 42 84 200 304 33 65 128 256), losses := [{ target := 5, region := (rows 1 2 20 127 16 0 97 511 511), good := (rows 463 458 476 456 476 457 457 384 384) }] }

theorem u450 : Upper (D 9) (R 9) [6,40,80,192,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b450 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b451 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 7 42 84 200 304 33 192 385 257), lower := (rows 7 42 84 200 304 33 192 128 256), losses := [] }

theorem u451 : Upper (D 9) (R 9) [6,40,80,192,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b451 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b452 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 171, targets := 256 },{ cop := 4, region := 68, targets := 33 }], pairs := [(0,8),(1,8),(2,0),(2,5),(3,8)], upper := (rows 7 42 84 200 304 33 320 129 385), lower := (rows 7 42 84 200 304 33 320 128 256), losses := [] }

theorem u452 : Upper (D 9) (R 9) [6,40,80,192,288,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b452 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b453 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 1, region := 400, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 42 84 200 400 33 65 416 288), lower := (rows 7 42 84 200 400 33 65 128 256), losses := [] }

theorem u453 : Upper (D 9) (R 9) [6,40,80,192,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b453 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b454 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,5)], upper := (rows 7 42 84 200 400 33 96 385 257), lower := (rows 7 42 84 200 400 33 96 128 256), losses := [] }

theorem u454 : Upper (D 9) (R 9) [6,40,80,192,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b454 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b455 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 76, targets := 33 },{ cop := 2, region := 171, targets := 256 }], pairs := [(0,8),(2,0),(2,5),(3,0),(3,5)], upper := (rows 7 42 84 200 400 33 320 161 289), lower := (rows 7 42 84 200 400 33 320 128 256), losses := [] }

theorem u455 : Upper (D 9) (R 9) [6,40,80,192,384,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b455 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r456 : Route 9 := (fun mask => (mask,id))

def c456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u456 : Upper (D 9) (R 9) [6,40,80,192,384,256,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,384,256,1] 13 (by decide) (choices 1) [1,32] r456 c456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22
  · exact u23

def b457 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 110, targets := 1 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,0),(2,0),(3,0),(4,5),(4,6)], upper := (rows 7 42 84 200 400 288 96 129 257), lower := (rows 7 42 84 200 400 288 96 128 256), losses := [] }

theorem u457 : Upper (D 9) (R 9) [6,40,80,192,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b457 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b458 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 69, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,5)], upper := (rows 7 42 100 25 208 288 65 384 384), lower := (rows 7 42 100 25 208 288 65 128 256), losses := [] }

theorem u458 : Upper (D 9) (R 9) [6,40,96,17,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b458 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b459 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 7 42 100 25 208 288 192 385 257), lower := (rows 7 42 100 25 208 288 192 128 256), losses := [] }

theorem u459 : Upper (D 9) (R 9) [6,40,96,17,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b459 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b460 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 155, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,8)], upper := (rows 7 42 100 25 208 288 320 129 385), lower := (rows 7 42 100 25 208 288 320 128 256), losses := [] }

theorem u460 : Upper (D 9) (R 9) [6,40,96,17,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b460 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b461 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 69, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,5)], upper := (rows 7 42 100 88 145 288 65 384 384), lower := (rows 7 42 100 88 145 288 65 128 256), losses := [] }

theorem u461 : Upper (D 9) (R 9) [6,40,96,80,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b461 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b462 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 88 145 288 192 385 257), lower := (rows 7 42 100 88 145 288 192 128 256), losses := [] }

theorem u462 : Upper (D 9) (R 9) [6,40,96,80,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b462 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b463 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 155, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,8)], upper := (rows 7 42 100 88 145 288 320 129 385), lower := (rows 7 42 100 88 145 288 320 128 256), losses := [] }

theorem u463 : Upper (D 9) (R 9) [6,40,96,80,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b463 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b464 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 69, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,5)], upper := (rows 7 42 100 137 208 288 65 400 272), lower := (rows 7 42 100 137 208 288 65 128 256), losses := [] }

theorem u464 : Upper (D 9) (R 9) [6,40,96,129,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b464 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b465 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 7, region := 80, targets := 1 }], pairs := [(0,6),(1,6),(3,6),(4,0)], upper := (rows 7 42 100 137 208 288 80 385 257), lower := (rows 7 42 100 137 208 288 80 128 256), losses := [] }

theorem u465 : Upper (D 9) (R 9) [6,40,96,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b465 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b466 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 155, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,8)], upper := (rows 7 42 100 137 208 288 320 145 273), lower := (rows 7 42 100 137 208 288 320 128 256), losses := [] }

theorem u466 : Upper (D 9) (R 9) [6,40,96,129,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b466 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b467 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 452, targets := 1 }], pairs := [(1,7),(2,0),(3,5),(4,5)], upper := (rows 7 42 100 137 273 48 192 448 320), lower := (rows 7 42 100 137 273 48 192 128 256), losses := [{ target := 7, region := (rows 1 10 4 8 17 57 64 0 324), good := (rows 311 42 356 59 305 48 320 0 256) }] }

theorem u467 : Upper (D 9) (R 9) [6,40,96,129,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b467 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b468 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 139, targets := 256 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 7 42 100 137 273 48 320 192 448), lower := (rows 7 42 100 137 273 48 320 128 256), losses := [] }

theorem u468 : Upper (D 9) (R 9) [6,40,96,129,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b468 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b469 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 139, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 7 42 100 137 273 288 80 192 448), lower := (rows 7 42 100 137 273 288 80 128 256), losses := [] }

theorem u469 : Upper (D 9) (R 9) [6,40,96,129,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b469 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b470 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 228, targets := 1 },{ cop := 4, region := 200, targets := 256 }], pairs := [(0,8),(2,0),(3,5),(3,8),(4,5)], upper := (rows 7 42 100 137 273 288 192 208 336), lower := (rows 7 42 100 137 273 288 192 128 256), losses := [{ target := 8, region := (rows 3 2 6 24 16 32 216 144 0), good := (rows 7 111 100 201 217 32 192 192 0) }] }

theorem u470 : Upper (D 9) (R 9) [6,40,96,129,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b470 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b471 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 69, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,5)], upper := (rows 7 42 100 137 336 288 65 144 400), lower := (rows 7 42 100 137 336 288 65 128 256), losses := [] }

theorem u471 : Upper (D 9) (R 9) [6,40,96,129,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b471 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b472 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 84, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 7 42 100 137 336 288 80 129 385), lower := (rows 7 42 100 137 336 288 80 128 256), losses := [] }

theorem u472 : Upper (D 9) (R 9) [6,40,96,129,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b472 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b473 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 36, targets := 129 }], pairs := [(0,8),(2,0),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 137 336 288 192 145 273), lower := (rows 7 42 100 137 336 288 192 128 256), losses := [{ target := 8, region := (rows 3 2 6 8 16 32 200 128 0), good := (rows 7 111 100 201 80 32 192 192 0) }] }

theorem u473 : Upper (D 9) (R 9) [6,40,96,129,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b473 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b474 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 69, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,5)], upper := (rows 7 42 100 137 400 288 65 208 336), lower := (rows 7 42 100 137 400 288 65 128 256), losses := [] }

theorem u474 : Upper (D 9) (R 9) [6,40,96,129,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b474 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b475 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 139, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 7 42 100 137 400 288 80 193 321), lower := (rows 7 42 100 137 400 288 80 128 256), losses := [] }

theorem u475 : Upper (D 9) (R 9) [6,40,96,129,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b475 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b476 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 85, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8),(4,7)], upper := (rows 7 42 100 152 81 288 65 384 384), lower := (rows 7 42 100 152 81 288 65 128 256), losses := [] }

theorem u476 : Upper (D 9) (R 9) [6,40,96,144,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b476 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b477 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 426, targets := 64 },{ cop := 4, region := 292, targets := 128 }], pairs := [(1,6),(2,7),(3,5),(3,6),(4,5)], upper := (rows 7 42 100 152 81 288 192 385 257), lower := (rows 7 42 100 152 81 288 192 128 256), losses := [] }

theorem u477 : Upper (D 9) (R 9) [6,40,96,144,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b477 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b478 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 155, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,8)], upper := (rows 7 42 100 152 81 288 320 129 385), lower := (rows 7 42 100 152 81 288 320 128 256), losses := [] }

theorem u478 : Upper (D 9) (R 9) [6,40,96,144,65,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b478 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b479 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 103, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 42 100 152 336 33 65 384 384), lower := (rows 7 42 100 152 336 33 65 128 256), losses := [] }

theorem u479 : Upper (D 9) (R 9) [6,40,96,144,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b479 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u479
end Delivery.IrregularNine14.P09
