import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0000
import IrregularNine14P10C0001

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b420 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 84 392 49 160 352 480 352), lower := (rows 7 42 84 392 49 160 64 128 256), losses := [] }

theorem u420 : Upper (D 10) (R 10) [6,40,80,384,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b420 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b421 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 324, targets := 128 }], pairs := [(2,7)], upper := (rows 7 42 84 392 176 33 352 480 352), lower := (rows 7 42 84 392 176 33 64 128 256), losses := [] }

theorem u421 : Upper (D 10) (R 10) [6,40,80,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b421 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r422 : Route 9 := (fun mask => (mask,id))

def c422 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u422 : Upper (D 10) (R 10) [6,40,80,384,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,160,64] 13 (by decide) (choices 1) [1,32,256] r422 c422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u46
  · exact u47
  · exact u48

def b423 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 213, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 42 84 392 176 288 97 225 353), lower := (rows 7 42 84 392 176 288 64 128 256), losses := [] }

theorem u423 : Upper (D 10) (R 10) [6,40,80,384,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b423 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b424 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 88 176 33 448 384 384), lower := (rows 7 42 100 88 176 33 64 128 256), losses := [] }

theorem u424 : Upper (D 10) (R 10) [6,40,96,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b424 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b425 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 42 100 88 176 160 321 385 257), lower := (rows 7 42 100 88 176 160 64 128 256), losses := [] }

theorem u425 : Upper (D 10) (R 10) [6,40,96,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b425 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r426 : Route 9 := (fun mask => (mask,id))

def c426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u426 : Upper (D 10) (R 10) [6,40,96,80,160,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,80,160,256] 13 (by decide) (choices 1) [1,128,256] r426 c426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u49
  · exact u50
  · exact u51

def b427 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 88 400 33 480 416 416), lower := (rows 7 42 100 88 400 33 64 128 256), losses := [] }

theorem u427 : Upper (D 10) (R 10) [6,40,96,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b427 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b428 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 100 88 400 160 353 417 289), lower := (rows 7 42 100 88 400 160 64 128 256), losses := [] }

theorem u428 : Upper (D 10) (R 10) [6,40,96,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b428 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b429 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 50, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 100 137 176 48 320 448 320), lower := (rows 7 42 100 137 176 48 64 128 256), losses := [] }

theorem u429 : Upper (D 10) (R 10) [6,40,96,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b429 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b430 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 137 176 96 336 400 272), lower := (rows 7 42 100 137 176 96 64 128 256), losses := [] }

theorem u430 : Upper (D 10) (R 10) [6,40,96,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b430 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r431 : Route 9 := (fun mask => (mask,id))

def c431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u431 : Upper (D 10) (R 10) [6,40,96,129,160,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,160,256] 13 (by decide) (choices 1) [16,256] r431 c431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u52
  · exact u53

def b432 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 100 137 208 48 352 416 288), lower := (rows 7 42 100 137 208 48 64 128 256), losses := [] }

theorem u432 : Upper (D 10) (R 10) [6,40,96,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b432 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r433 : Route 9 := (fun mask => (mask,id))

def c433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u433 : Upper (D 10) (R 10) [6,40,96,129,192,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,192,256] 13 (by decide) (choices 1) [16,32,256] r433 c433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u54
  · exact u55
  · exact u56

def b434 : PairBound 9 := { available := 448, camps := [{ cop := 8, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 100 137 304 48 448 448 448), lower := (rows 7 42 100 137 304 48 64 128 256), losses := [] }

theorem u434 : Upper (D 10) (R 10) [6,40,96,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b434 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b435 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 137 304 96 464 400 400), lower := (rows 7 42 100 137 304 96 64 128 256), losses := [] }

theorem u435 : Upper (D 10) (R 10) [6,40,96,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b435 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b436 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 100 137 304 160 336 464 336), lower := (rows 7 42 100 137 304 160 64 128 256), losses := [] }

theorem u436 : Upper (D 10) (R 10) [6,40,96,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b436 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b437 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 100 137 304 288 208 208 464), lower := (rows 7 42 100 137 304 288 64 128 256), losses := [] }

theorem u437 : Upper (D 10) (R 10) [6,40,96,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b437 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b438 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 137 336 48 480 416 416), lower := (rows 7 42 100 137 336 48 64 128 256), losses := [] }

theorem u438 : Upper (D 10) (R 10) [6,40,96,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b438 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b439 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 100 137 336 160 368 432 304), lower := (rows 7 42 100 137 336 160 64 128 256), losses := [] }

theorem u439 : Upper (D 10) (R 10) [6,40,96,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b439 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r440 : Route 9 := (fun mask => (mask,id))

def c440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u440 : Upper (D 10) (R 10) [6,40,96,129,320,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,320,256] 13 (by decide) (choices 1) [16,32,128] r440 c440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u57
  · exact u58
  · exact u59

def b441 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 137 400 48 352 480 352), lower := (rows 7 42 100 137 400 48 64 128 256), losses := [] }

theorem u441 : Upper (D 10) (R 10) [6,40,96,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b441 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b442 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 137 400 96 368 432 304), lower := (rows 7 42 100 137 400 96 64 128 256), losses := [] }

theorem u442 : Upper (D 10) (R 10) [6,40,96,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b442 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r443 : Route 9 := (fun mask => (mask,id))

def c443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u443 : Upper (D 10) (R 10) [6,40,96,129,384,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,384,256] 13 (by decide) (choices 1) [16,32] r443 c443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u60
  · exact u61

def b444 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 152 49 96 448 384 384), lower := (rows 7 42 100 152 49 96 64 128 256), losses := [] }

theorem u444 : Upper (D 10) (R 10) [6,40,96,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b444 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b445 : PairBound 9 := { available := 320, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 100 152 49 160 320 448 320), lower := (rows 7 42 100 152 49 160 64 128 256), losses := [] }

theorem u445 : Upper (D 10) (R 10) [6,40,96,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b445 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r446 : Route 9 := (fun mask => (mask,id))

def c446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u446 : Upper (D 10) (R 10) [6,40,96,144,33,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,33,256] 13 (by decide) (choices 1) [128,256] r446 c446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u62
  · exact u63

def b447 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 152 273 96 480 416 416), lower := (rows 7 42 100 152 273 96 64 128 256), losses := [] }

theorem u447 : Upper (D 10) (R 10) [6,40,96,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b447 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b448 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 100 152 273 160 352 480 352), lower := (rows 7 42 100 152 273 160 64 128 256), losses := [] }

theorem u448 : Upper (D 10) (R 10) [6,40,96,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b448 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b449 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 197, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 42 100 152 273 288 224 224 480), lower := (rows 7 42 100 152 273 288 64 128 256), losses := [] }

theorem u449 : Upper (D 10) (R 10) [6,40,96,144,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b449 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b450 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 100 152 304 33 448 448 448), lower := (rows 7 42 100 152 304 33 64 128 256), losses := [] }

theorem u450 : Upper (D 10) (R 10) [6,40,96,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b450 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b451 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 152 304 96 449 385 385), lower := (rows 7 42 100 152 304 96 64 128 256), losses := [] }

theorem u451 : Upper (D 10) (R 10) [6,40,96,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b451 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b452 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 100 152 304 160 321 449 321), lower := (rows 7 42 100 152 304 160 64 128 256), losses := [] }

theorem u452 : Upper (D 10) (R 10) [6,40,96,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b452 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b453 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 100 152 304 288 193 193 449), lower := (rows 7 42 100 152 304 288 64 128 256), losses := [] }

theorem u453 : Upper (D 10) (R 10) [6,40,96,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b453 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r454 : Route 9 := (fun mask => (mask,id))

def c454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u454 : Upper (D 10) (R 10) [6,40,96,144,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,320,1] 13 (by decide) (choices 1) [32,128,256] r454 c454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u64
  · exact u65
  · exact u66

def b455 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 100 152 336 160 353 417 289), lower := (rows 7 42 100 152 336 160 64 128 256), losses := [] }

theorem u455 : Upper (D 10) (R 10) [6,40,96,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b455 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b456 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 197, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 42 100 152 336 288 225 161 417), lower := (rows 7 42 100 152 336 288 64 128 256), losses := [] }

theorem u456 : Upper (D 10) (R 10) [6,40,96,144,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b456 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b457 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 39, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 100 200 176 33 336 400 272), lower := (rows 7 42 100 200 176 33 64 128 256), losses := [] }

theorem u457 : Upper (D 10) (R 10) [6,40,96,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b457 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b458 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 100 200 176 48 321 385 257), lower := (rows 7 42 100 200 176 48 64 128 256), losses := [] }

theorem u458 : Upper (D 10) (R 10) [6,40,96,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b458 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r459 : Route 9 := (fun mask => (mask,id))

def c459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u459 : Upper (D 10) (R 10) [6,40,96,192,160,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,160,256] 13 (by decide) (choices 1) [1,16,256] r459 c459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u67
  · exact u68
  · exact u69

def b460 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 100 200 273 48 480 416 416), lower := (rows 7 42 100 200 273 48 64 128 256), losses := [] }

theorem u460 : Upper (D 10) (R 10) [6,40,96,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b460 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b461 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 100 200 273 160 368 432 304), lower := (rows 7 42 100 200 273 160 64 128 256), losses := [] }

theorem u461 : Upper (D 10) (R 10) [6,40,96,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b461 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r462 : Route 9 := (fun mask => (mask,id))

def c462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u462 : Upper (D 10) (R 10) [6,40,96,192,257,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,257,256] 13 (by decide) (choices 1) [16,32,128] r462 c462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u70
  · exact u71
  · exact u72

def b463 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 200 304 33 464 400 400), lower := (rows 7 42 100 200 304 33 64 128 256), losses := [] }

theorem u463 : Upper (D 10) (R 10) [6,40,96,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b463 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b464 : PairBound 9 := { available := 385, camps := [{ cop := 8, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 100 200 304 48 449 385 385), lower := (rows 7 42 100 200 304 48 64 128 256), losses := [] }

theorem u464 : Upper (D 10) (R 10) [6,40,96,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b464 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b465 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 100 200 304 160 337 401 273), lower := (rows 7 42 100 200 304 160 64 128 256), losses := [] }

theorem u465 : Upper (D 10) (R 10) [6,40,96,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b465 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b466 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 100 200 304 288 209 145 401), lower := (rows 7 42 100 200 304 288 64 128 256), losses := [] }

theorem u466 : Upper (D 10) (R 10) [6,40,96,192,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b466 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b467 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 200 400 33 368 432 304), lower := (rows 7 42 100 200 400 33 64 128 256), losses := [] }

theorem u467 : Upper (D 10) (R 10) [6,40,96,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b467 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b468 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 200 400 48 353 417 289), lower := (rows 7 42 100 200 400 48 64 128 256), losses := [] }

theorem u468 : Upper (D 10) (R 10) [6,40,96,192,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b468 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r469 : Route 9 := (fun mask => (mask,id))

def c469 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u469 : Upper (D 10) (R 10) [6,40,96,192,384,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,384,256] 13 (by decide) (choices 1) [1,16,32] r469 c469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u73
  · exact u74
  · exact u75

def b470 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 100 392 49 48 448 448 448), lower := (rows 7 42 100 392 49 48 64 128 256), losses := [] }

theorem u470 : Upper (D 10) (R 10) [6,40,96,384,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b470 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b471 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 392 49 96 464 400 400), lower := (rows 7 42 100 392 49 96 64 128 256), losses := [] }

theorem u471 : Upper (D 10) (R 10) [6,40,96,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b471 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b472 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 100 392 49 160 336 464 336), lower := (rows 7 42 100 392 49 160 64 128 256), losses := [] }

theorem u472 : Upper (D 10) (R 10) [6,40,96,384,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b472 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b473 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 392 145 48 352 480 352), lower := (rows 7 42 100 392 145 48 64 128 256), losses := [] }

theorem u473 : Upper (D 10) (R 10) [6,40,96,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b473 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b474 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 392 145 96 368 432 304), lower := (rows 7 42 100 392 145 96 64 128 256), losses := [] }

theorem u474 : Upper (D 10) (R 10) [6,40,96,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b474 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b475 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 213, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 42 100 392 145 288 112 240 368), lower := (rows 7 42 100 392 145 288 64 128 256), losses := [] }

theorem u475 : Upper (D 10) (R 10) [6,40,96,384,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b475 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b476 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 328, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 100 392 176 33 336 464 336), lower := (rows 7 42 100 392 176 33 64 128 256), losses := [] }

theorem u476 : Upper (D 10) (R 10) [6,40,96,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b476 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b477 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 50, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 100 392 176 48 321 449 321), lower := (rows 7 42 100 392 176 48 64 128 256), losses := [] }

theorem u477 : Upper (D 10) (R 10) [6,40,96,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b477 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b478 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 392 176 96 337 401 273), lower := (rows 7 42 100 392 176 96 64 128 256), losses := [] }

theorem u478 : Upper (D 10) (R 10) [6,40,96,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b478 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b479 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 213, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 42 100 392 176 288 81 209 337), lower := (rows 7 42 100 392 176 288 64 128 256), losses := [] }

theorem u479 : Upper (D 10) (R 10) [6,40,96,384,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b479 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u479
end Delivery.IrregularNine14.P10
