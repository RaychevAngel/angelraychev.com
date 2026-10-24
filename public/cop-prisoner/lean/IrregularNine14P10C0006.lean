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

def b360 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 76 168 112 160 336 400 272), lower := (rows 7 35 76 168 112 160 64 128 256), losses := [] }

theorem u360 : Upper (D 10) (R 10) [6,33,72,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b360 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r361 : Route 9 := (fun mask => (mask,id))

def c361 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u361 : Upper (D 10) (R 10) [6,33,72,160,96,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,96,256] 13 (by decide) (choices 1) [16,128,256] r361 c361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25
  · exact u26
  · exact u27

def b362 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8)], upper := (rows 7 35 76 168 208 48 352 416 288), lower := (rows 7 35 76 168 208 48 64 128 256), losses := [] }

theorem u362 : Upper (D 10) (R 10) [6,33,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b362 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r363 : Route 9 := (fun mask => (mask,id))

def c363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u363 : Upper (D 10) (R 10) [6,33,72,160,192,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,192,256] 13 (by decide) (choices 1) [16,32,256] r363 c363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28
  · exact u29
  · exact u30

def b364 : PairBound 9 := { available := 448, camps := [{ cop := 8, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 76 168 304 48 448 448 448), lower := (rows 7 35 76 168 304 48 64 128 256), losses := [] }

theorem u364 : Upper (D 10) (R 10) [6,33,72,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b364 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b365 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 76 168 304 96 464 400 400), lower := (rows 7 35 76 168 304 96 64 128 256), losses := [] }

theorem u365 : Upper (D 10) (R 10) [6,33,72,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b365 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b366 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 76 168 304 160 336 464 336), lower := (rows 7 35 76 168 304 160 64 128 256), losses := [] }

theorem u366 : Upper (D 10) (R 10) [6,33,72,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b366 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b367 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 35 76 168 304 288 208 208 464), lower := (rows 7 35 76 168 304 288 64 128 256), losses := [] }

theorem u367 : Upper (D 10) (R 10) [6,33,72,160,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b367 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b368 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 168 336 48 480 416 416), lower := (rows 7 35 76 168 336 48 64 128 256), losses := [] }

theorem u368 : Upper (D 10) (R 10) [6,33,72,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b368 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b369 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 76 168 336 160 368 432 304), lower := (rows 7 35 76 168 336 160 64 128 256), losses := [] }

theorem u369 : Upper (D 10) (R 10) [6,33,72,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b369 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r370 : Route 9 := (fun mask => (mask,id))

def c370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u370 : Upper (D 10) (R 10) [6,33,72,160,320,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,320,256] 13 (by decide) (choices 1) [16,32,128] r370 c370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u31
  · exact u32
  · exact u33

def b371 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 168 400 48 352 480 352), lower := (rows 7 35 76 168 400 48 64 128 256), losses := [] }

theorem u371 : Upper (D 10) (R 10) [6,33,72,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b371 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b372 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 76 168 400 96 368 432 304), lower := (rows 7 35 76 168 400 96 64 128 256), losses := [] }

theorem u372 : Upper (D 10) (R 10) [6,33,72,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b372 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r373 : Route 9 := (fun mask => (mask,id))

def c373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u373 : Upper (D 10) (R 10) [6,33,72,160,384,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,384,256] 13 (by decide) (choices 1) [16,32] r373 c373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u34
  · exact u35

def b374 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 51, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 392 112 48 480 416 416), lower := (rows 7 35 76 392 112 48 64 128 256), losses := [] }

theorem u374 : Upper (D 10) (R 10) [6,33,72,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b374 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b375 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 336, targets := 128 },{ cop := 4, region := 392, targets := 64 }], pairs := [(3,6),(4,7)], upper := (rows 7 35 76 392 112 160 368 432 304), lower := (rows 7 35 76 392 112 160 64 128 256), losses := [] }

theorem u375 : Upper (D 10) (R 10) [6,33,72,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b375 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b376 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 76 392 176 48 352 480 352), lower := (rows 7 35 76 392 176 48 64 128 256), losses := [] }

theorem u376 : Upper (D 10) (R 10) [6,33,72,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b376 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b377 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 76 392 176 96 368 432 304), lower := (rows 7 35 76 392 176 96 64 128 256), losses := [] }

theorem u377 : Upper (D 10) (R 10) [6,33,72,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b377 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b378 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 208, targets := 256 },{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6),(4,8)], upper := (rows 7 35 76 392 176 288 112 240 368), lower := (rows 7 35 76 392 176 288 64 128 256), losses := [] }

theorem u378 : Upper (D 10) (R 10) [6,33,72,384,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b378 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b379 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 392 208 48 352 416 288), lower := (rows 7 35 76 392 208 48 64 128 256), losses := [] }

theorem u379 : Upper (D 10) (R 10) [6,33,72,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b379 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b380 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 208, targets := 256 },{ cop := 4, region := 296, targets := 64 }], pairs := [(3,6),(4,8)], upper := (rows 7 35 76 392 208 288 112 176 304), lower := (rows 7 35 76 392 208 288 64 128 256), losses := [] }

theorem u380 : Upper (D 10) (R 10) [6,33,72,384,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b380 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b381 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 196 56 280 96 480 416 416), lower := (rows 7 35 196 56 280 96 64 128 256), losses := [] }

theorem u381 : Upper (D 10) (R 10) [6,33,192,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b381 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b382 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 24, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 35 196 56 280 288 224 224 480), lower := (rows 7 35 196 56 280 288 64 128 256), losses := [] }

theorem u382 : Upper (D 10) (R 10) [6,33,192,48,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b382 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b383 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 7 35 196 56 336 40 480 416 416), lower := (rows 7 35 196 56 336 40 64 128 256), losses := [] }

theorem u383 : Upper (D 10) (R 10) [6,33,192,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b383 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b384 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 35, targets := 320 }], pairs := [(0,6),(0,8)], upper := (rows 7 35 196 56 336 160 360 424 296), lower := (rows 7 35 196 56 336 160 64 128 256), losses := [] }

theorem u384 : Upper (D 10) (R 10) [6,33,192,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b384 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b385 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 35 196 56 336 288 232 168 424), lower := (rows 7 35 196 56 336 288 64 128 256), losses := [] }

theorem u385 : Upper (D 10) (R 10) [6,33,192,48,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b385 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b386 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 196 88 304 40 480 416 416), lower := (rows 7 35 196 88 304 40 64 128 256), losses := [] }

theorem u386 : Upper (D 10) (R 10) [6,33,192,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b386 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b387 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 35, targets := 320 }], pairs := [(0,6),(0,8)], upper := (rows 7 35 196 88 304 160 360 424 296), lower := (rows 7 35 196 88 304 160 64 128 256), losses := [] }

theorem u387 : Upper (D 10) (R 10) [6,33,192,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b387 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b388 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 35 196 88 304 288 232 168 424), lower := (rows 7 35 196 88 304 288 64 128 256), losses := [] }

theorem u388 : Upper (D 10) (R 10) [6,33,192,80,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b388 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b389 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 196 104 280 48 480 416 416), lower := (rows 7 35 196 104 280 48 64 128 256), losses := [] }

theorem u389 : Upper (D 10) (R 10) [6,33,192,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b389 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b390 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 35 196 104 280 160 368 432 304), lower := (rows 7 35 196 104 280 160 64 128 256), losses := [] }

theorem u390 : Upper (D 10) (R 10) [6,33,192,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b390 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r391 : Route 9 := (fun mask => (mask,id))

def c391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u391 : Upper (D 10) (R 10) [6,33,192,96,264,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,264,256] 13 (by decide) (choices 1) [16,32,128] r391 c391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u36
  · exact u37
  · exact u38

def b392 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 196 104 304 40 464 400 400), lower := (rows 7 35 196 104 304 40 64 128 256), losses := [] }

theorem u392 : Upper (D 10) (R 10) [6,33,192,96,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b392 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b393 : PairBound 9 := { available := 392, camps := [{ cop := 8, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 196 104 304 48 456 392 392), lower := (rows 7 35 196 104 304 48 64 128 256), losses := [] }

theorem u393 : Upper (D 10) (R 10) [6,33,192,96,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b393 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b394 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 35, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 35 196 104 304 160 344 408 280), lower := (rows 7 35 196 104 304 160 64 128 256), losses := [] }

theorem u394 : Upper (D 10) (R 10) [6,33,192,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b394 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b395 : PairBound 9 := { available := 152, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 35 196 104 304 288 216 152 408), lower := (rows 7 35 196 104 304 288 64 128 256), losses := [] }

theorem u395 : Upper (D 10) (R 10) [6,33,192,96,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b395 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b396 : PairBound 9 := { available := 176, camps := [{ cop := 8, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 296 336 40 240 176 432), lower := (rows 7 35 196 296 336 40 64 128 256), losses := [] }

theorem u396 : Upper (D 10) (R 10) [6,33,192,288,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b396 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b397 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 7 35 196 296 336 48 232 168 424), lower := (rows 7 35 196 296 336 48 64 128 256), losses := [] }

theorem u397 : Upper (D 10) (R 10) [6,33,192,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b397 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b398 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 35, targets := 320 }], pairs := [(0,6),(0,8)], upper := (rows 7 35 196 296 336 160 120 184 312), lower := (rows 7 35 196 296 336 160 64 128 256), losses := [] }

theorem u398 : Upper (D 10) (R 10) [6,33,192,288,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b398 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b399 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 42 52 73 400 96 480 416 416), lower := (rows 7 42 52 73 400 96 64 128 256), losses := [] }

theorem u399 : Upper (D 10) (R 10) [6,40,48,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b399 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b400 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 42 52 73 400 160 352 480 352), lower := (rows 7 42 52 73 400 160 64 128 256), losses := [] }

theorem u400 : Upper (D 10) (R 10) [6,40,48,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b400 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m401_256 : Upper (D 10) (R 10) [6,40,48,192,320,1,256] 13 :=
  permutation_upper _ _ _ [6,40,48,192,320,1,128] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40

def r401 : Route 9 := (fun mask => (mask,id))

def c401 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u401 : Upper (D 10) (R 10) [6,40,48,192,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,320,1] 13 (by decide) (choices 1) [32,128,256] r401 c401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u39
  · exact u40
  · exact m401_256

def b402 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 52 200 336 160 353 417 289), lower := (rows 7 42 52 200 336 160 64 128 256), losses := [] }

theorem u402 : Upper (D 10) (R 10) [6,40,48,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b402 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b403 : PairBound 9 := { available := 416, camps := [{ cop := 5, region := 410, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 7 42 69 152 304 96 480 416 416), lower := (rows 7 42 69 152 304 96 64 128 256), losses := [] }

theorem u403 : Upper (D 10) (R 10) [6,40,65,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b403 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b404 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 69 152 304 160 352 480 352), lower := (rows 7 42 69 152 304 160 64 128 256), losses := [] }

theorem u404 : Upper (D 10) (R 10) [6,40,65,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b404 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b405 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 69 152 304 288 224 224 480), lower := (rows 7 42 69 152 304 288 64 128 256), losses := [] }

theorem u405 : Upper (D 10) (R 10) [6,40,65,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b405 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b406 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 50, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 69 392 176 48 352 480 352), lower := (rows 7 42 69 392 176 48 64 128 256), losses := [] }

theorem u406 : Upper (D 10) (R 10) [6,40,65,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b406 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b407 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 410, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 7 42 69 392 176 96 368 432 304), lower := (rows 7 42 69 392 176 96 64 128 256), losses := [] }

theorem u407 : Upper (D 10) (R 10) [6,40,65,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b407 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b408 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 213, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 42 69 392 176 288 112 240 368), lower := (rows 7 42 69 392 176 288 64 128 256), losses := [] }

theorem u408 : Upper (D 10) (R 10) [6,40,65,384,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b408 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b409 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 400, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 42 84 137 304 96 480 416 416), lower := (rows 7 42 84 137 304 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 50 32 0 178 306), good := (rows 415 442 404 137 432 432 0 128 256) }] }

theorem u409 : Upper (D 10) (R 10) [6,40,80,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b409 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b410 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 84 137 304 160 352 480 352), lower := (rows 7 42 84 137 304 160 64 128 256), losses := [] }

theorem u410 : Upper (D 10) (R 10) [6,40,80,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b410 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b411 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 84 137 304 288 224 224 480), lower := (rows 7 42 84 137 304 288 64 128 256), losses := [] }

theorem u411 : Upper (D 10) (R 10) [6,40,80,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b411 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b412 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 84 200 176 33 352 416 288), lower := (rows 7 42 84 200 176 33 64 128 256), losses := [] }

theorem u412 : Upper (D 10) (R 10) [6,40,80,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b412 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r413 : Route 9 := (fun mask => (mask,id))

def c413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u413 : Upper (D 10) (R 10) [6,40,80,192,160,256] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,160,256] 13 (by decide) (choices 1) [1,32,256] r413 c413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u41
  · exact u42
  · exact u43

def b414 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 84 200 304 33 480 416 416), lower := (rows 7 42 84 200 304 33 64 128 256), losses := [] }

theorem u414 : Upper (D 10) (R 10) [6,40,80,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b414 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b415 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 84 200 304 160 353 417 289), lower := (rows 7 42 84 200 304 160 64 128 256), losses := [] }

theorem u415 : Upper (D 10) (R 10) [6,40,80,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b415 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b416 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 84 200 304 288 225 161 417), lower := (rows 7 42 84 200 304 288 64 128 256), losses := [] }

theorem u416 : Upper (D 10) (R 10) [6,40,80,192,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b416 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b417 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 84 200 400 33 352 416 288), lower := (rows 7 42 84 200 400 33 64 128 256), losses := [] }

theorem u417 : Upper (D 10) (R 10) [6,40,80,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b417 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r418 : Route 9 := (fun mask => (mask,id))

def c418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u418 : Upper (D 10) (R 10) [6,40,80,192,384,256] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,384,256] 13 (by decide) (choices 1) [1,32] r418 c418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u44
  · exact u45

def b419 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 394, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 7 42 84 392 49 96 480 416 416), lower := (rows 7 42 84 392 49 96 64 128 256), losses := [] }

theorem u419 : Upper (D 10) (R 10) [6,40,80,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b419 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u419
end Delivery.IrregularNine14.P10
