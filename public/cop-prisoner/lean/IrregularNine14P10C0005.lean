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

def b300 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 11 84 168 304 288 224 224 480), lower := (rows 7 11 84 168 304 288 64 128 256), losses := [] }

theorem u300 : Upper (D 10) (R 10) [6,9,80,160,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b300 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b301 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 408, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 11 84 168 400 96 352 416 288), lower := (rows 7 11 84 168 400 96 64 128 256), losses := [] }

theorem u301 : Upper (D 10) (R 10) [6,9,80,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b301 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b302 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 40, targets := 64 },{ cop := 4, region := 100, targets := 128 }], pairs := [(2,7),(3,6)], upper := (rows 7 11 84 168 400 288 96 224 352), lower := (rows 7 11 84 168 400 288 64 128 256), losses := [] }

theorem u302 : Upper (D 10) (R 10) [6,9,80,160,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b302 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b303 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 340, targets := 128 }], pairs := [(2,7),(4,7)], upper := (rows 7 11 84 200 304 160 352 416 288), lower := (rows 7 11 84 200 304 160 64 128 256), losses := [] }

theorem u303 : Upper (D 10) (R 10) [6,9,80,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b303 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b304 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 11 84 200 304 288 224 160 416), lower := (rows 7 11 84 200 304 288 64 128 256), losses := [] }

theorem u304 : Upper (D 10) (R 10) [6,9,80,192,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b304 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b305 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 408, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 11 84 392 176 96 352 416 288), lower := (rows 7 11 84 392 176 96 64 128 256), losses := [] }

theorem u305 : Upper (D 10) (R 10) [6,9,80,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b305 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b306 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 212, targets := 256 }], pairs := [(2,8),(4,8)], upper := (rows 7 11 84 392 176 288 96 224 352), lower := (rows 7 11 84 392 176 288 64 128 256), losses := [] }

theorem u306 : Upper (D 10) (R 10) [6,9,80,384,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b306 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b307 : PairBound 9 := { available := 448, camps := [{ cop := 8, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 100 168 304 48 448 448 448), lower := (rows 7 11 100 168 304 48 64 128 256), losses := [] }

theorem u307 : Upper (D 10) (R 10) [6,9,96,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b307 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b308 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 100 168 304 96 464 400 400), lower := (rows 7 11 100 168 304 96 64 128 256), losses := [] }

theorem u308 : Upper (D 10) (R 10) [6,9,96,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b308 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b309 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 11 100 168 304 288 208 208 464), lower := (rows 7 11 100 168 304 288 64 128 256), losses := [] }

theorem u309 : Upper (D 10) (R 10) [6,9,96,160,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b309 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b310 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 100 168 336 48 480 416 416), lower := (rows 7 11 100 168 336 48 64 128 256), losses := [] }

theorem u310 : Upper (D 10) (R 10) [6,9,96,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b310 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b311 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 11 100 168 336 160 368 432 304), lower := (rows 7 11 100 168 336 160 64 128 256), losses := [] }

theorem u311 : Upper (D 10) (R 10) [6,9,96,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b311 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b312 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 168, targets := 64 },{ cop := 4, region := 36, targets := 128 }], pairs := [(2,7),(3,6)], upper := (rows 7 11 100 168 336 288 240 176 432), lower := (rows 7 11 100 168 336 288 64 128 256), losses := [] }

theorem u312 : Upper (D 10) (R 10) [6,9,96,160,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b312 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b313 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 100 200 304 48 480 416 416), lower := (rows 7 11 100 200 304 48 64 128 256), losses := [] }

theorem u313 : Upper (D 10) (R 10) [6,9,96,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b313 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b314 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 11 100 200 304 160 368 432 304), lower := (rows 7 11 100 200 304 160 64 128 256), losses := [] }

theorem u314 : Upper (D 10) (R 10) [6,9,96,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b314 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b315 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 11 100 200 304 288 240 176 432), lower := (rows 7 11 100 200 304 288 64 128 256), losses := [] }

theorem u315 : Upper (D 10) (R 10) [6,9,96,192,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b315 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b316 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 100 392 176 48 352 480 352), lower := (rows 7 11 100 392 176 48 64 128 256), losses := [] }

theorem u316 : Upper (D 10) (R 10) [6,9,96,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b316 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b317 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 100 392 176 96 368 432 304), lower := (rows 7 11 100 392 176 96 64 128 256), losses := [] }

theorem u317 : Upper (D 10) (R 10) [6,9,96,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b317 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b318 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 212, targets := 256 }], pairs := [(2,8),(4,8)], upper := (rows 7 11 100 392 176 288 112 240 368), lower := (rows 7 11 100 392 176 288 64 128 256), losses := [] }

theorem u318 : Upper (D 10) (R 10) [6,9,96,384,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b318 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b319 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 26 37 104 176 96 448 384 384), lower := (rows 7 26 37 104 176 96 64 128 256), losses := [] }

theorem u319 : Upper (D 10) (R 10) [6,24,33,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b319 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r320 : Route 9 := (fun mask => (mask,id))

def c320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u320 : Upper (D 10) (R 10) [6,24,33,96,160,256] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,160,256] 13 (by decide) (choices 1) [128,256] r320 c320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14
  · exact u15

def b321 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 26 37 104 400 96 480 416 416), lower := (rows 7 26 37 104 400 96 64 128 256), losses := [] }

theorem u321 : Upper (D 10) (R 10) [6,24,33,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b321 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b322 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 328, targets := 128 }], pairs := [(0,6),(3,7)], upper := (rows 7 26 37 104 400 160 352 480 352), lower := (rows 7 26 37 104 400 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 6 8 16 176 0 128 256), good := (rows 7 63 37 40 432 160 0 160 256) }] }

theorem u322 : Upper (D 10) (R 10) [6,24,33,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b322 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b323 : PairBound 9 := { available := 416, camps := [{ cop := 5, region := 410, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 7 26 69 168 304 96 480 416 416), lower := (rows 7 26 69 168 304 96 64 128 256), losses := [] }

theorem u323 : Upper (D 10) (R 10) [6,24,65,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b323 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b324 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 26 69 168 304 160 352 480 352), lower := (rows 7 26 69 168 304 160 64 128 256), losses := [] }

theorem u324 : Upper (D 10) (R 10) [6,24,65,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b324 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b325 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 26 100 41 176 96 448 384 384), lower := (rows 7 26 100 41 176 96 64 128 256), losses := [] }

theorem u325 : Upper (D 10) (R 10) [6,24,96,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b325 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b326 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 26 100 41 176 160 320 448 320), lower := (rows 7 26 100 41 176 160 64 128 256), losses := [] }

theorem u326 : Upper (D 10) (R 10) [6,24,96,33,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b326 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r327 : Route 9 := (fun mask => (mask,id))

def c327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u327 : Upper (D 10) (R 10) [6,24,96,33,160,256] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,160,256] 13 (by decide) (choices 1) [128,256] r327 c327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16
  · exact u17

def b328 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 26 100 41 208 160 352 416 288), lower := (rows 7 26 100 41 208 160 64 128 256), losses := [] }

theorem u328 : Upper (D 10) (R 10) [6,24,96,33,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b328 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r329 : Route 9 := (fun mask => (mask,id))

def c329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u329 : Upper (D 10) (R 10) [6,24,96,33,192,256] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,192,256] 13 (by decide) (choices 1) [32,128,256] r329 c329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18
  · exact u19
  · exact u20

def b330 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 26 100 41 400 96 480 416 416), lower := (rows 7 26 100 41 400 96 64 128 256), losses := [] }

theorem u330 : Upper (D 10) (R 10) [6,24,96,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b330 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b331 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 324, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 26 100 41 400 160 352 480 352), lower := (rows 7 26 100 41 400 160 64 128 256), losses := [{ target := 7, region := (rows 3 2 44 8 16 32 108 0 300), good := (rows 327 351 356 365 272 356 64 0 256) }] }

theorem u331 : Upper (D 10) (R 10) [6,24,96,33,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b331 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b332 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 26 100 137 304 96 480 416 416), lower := (rows 7 26 100 137 304 96 64 128 256), losses := [] }

theorem u332 : Upper (D 10) (R 10) [6,24,96,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b332 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b333 : PairBound 9 := { available := 352, camps := [{ cop := 5, region := 340, targets := 128 }], pairs := [(2,7),(4,7)], upper := (rows 7 26 100 137 304 160 352 480 352), lower := (rows 7 26 100 137 304 160 64 128 256), losses := [] }

theorem u333 : Upper (D 10) (R 10) [6,24,96,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b333 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b334 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 26 100 137 304 288 224 224 480), lower := (rows 7 26 100 137 304 288 64 128 256), losses := [] }

theorem u334 : Upper (D 10) (R 10) [6,24,96,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b334 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b335 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 340, targets := 128 }], pairs := [(2,7),(4,7)], upper := (rows 7 26 100 137 336 160 352 416 288), lower := (rows 7 26 100 137 336 160 64 128 256), losses := [] }

theorem u335 : Upper (D 10) (R 10) [6,24,96,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b335 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b336 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 424, targets := 64 },{ cop := 4, region := 36, targets := 128 }], pairs := [(2,7),(3,6)], upper := (rows 7 26 100 137 336 288 224 160 416), lower := (rows 7 26 100 137 336 288 64 128 256), losses := [] }

theorem u336 : Upper (D 10) (R 10) [6,24,96,129,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b336 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m337_256 : Upper (D 10) (R 10) [6,24,96,160,288,1,256] 13 :=
  permutation_upper _ _ _ [6,24,96,160,288,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u21

def r337 : Route 9 := (fun mask => (mask,id))

def c337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u337 : Upper (D 10) (R 10) [6,24,96,160,288,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,288,1] 13 (by decide) (choices 1) [128,256] r337 c337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21
  · exact m337_256

def b338 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 26 100 168 304 96 449 385 385), lower := (rows 7 26 100 168 304 96 64 128 256), losses := [] }

theorem u338 : Upper (D 10) (R 10) [6,24,96,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b338 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b339 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 26 100 168 304 160 321 449 321), lower := (rows 7 26 100 168 304 160 64 128 256), losses := [] }

theorem u339 : Upper (D 10) (R 10) [6,24,96,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b339 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b340 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 7 26 100 168 336 33 480 416 416), lower := (rows 7 26 100 168 336 33 64 128 256), losses := [] }

theorem u340 : Upper (D 10) (R 10) [6,24,96,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b340 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b341 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 26 100 168 336 160 353 417 289), lower := (rows 7 26 100 168 336 160 64 128 256), losses := [] }

theorem u341 : Upper (D 10) (R 10) [6,24,96,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b341 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b342 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 424, targets := 64 },{ cop := 4, region := 36, targets := 128 }], pairs := [(2,7),(3,6)], upper := (rows 7 26 100 168 336 288 225 161 417), lower := (rows 7 26 100 168 336 288 64 128 256), losses := [] }

theorem u342 : Upper (D 10) (R 10) [6,24,96,160,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b342 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b343 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 59, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 26 196 41 112 160 352 416 288), lower := (rows 7 26 196 41 112 160 64 128 256), losses := [] }

theorem u343 : Upper (D 10) (R 10) [6,24,192,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b343 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r344 : Route 9 := (fun mask => (mask,id))

def c344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u344 : Upper (D 10) (R 10) [6,24,192,33,96,256] 13 := by
  apply FastRouting.sound _ _ [6,24,192,33,96,256] 13 (by decide) (choices 1) [32,128,256] r344 c344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22
  · exact u23
  · exact u24

def b345 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 402, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 26 196 41 304 96 480 416 416), lower := (rows 7 26 196 41 304 96 64 128 256), losses := [] }

theorem u345 : Upper (D 10) (R 10) [6,24,192,33,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b345 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b346 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 26 196 41 304 288 224 224 480), lower := (rows 7 26 196 41 304 288 64 128 256), losses := [] }

theorem u346 : Upper (D 10) (R 10) [6,24,192,33,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b346 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b347 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 338, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 26 196 41 336 160 352 416 288), lower := (rows 7 26 196 41 336 160 64 128 256), losses := [] }

theorem u347 : Upper (D 10) (R 10) [6,24,192,33,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b347 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b348 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 424, targets := 64 },{ cop := 3, region := 196, targets := 256 }], pairs := [(2,8),(3,6)], upper := (rows 7 26 196 41 336 288 224 160 416), lower := (rows 7 26 196 41 336 288 64 128 256), losses := [] }

theorem u348 : Upper (D 10) (R 10) [6,24,192,33,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b348 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b349 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 2, region := 40, targets := 256 }], pairs := [(3,8),(4,6)], upper := (rows 7 26 196 104 273 160 352 416 288), lower := (rows 7 26 196 104 273 160 64 128 256), losses := [] }

theorem u349 : Upper (D 10) (R 10) [6,24,192,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b349 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b350 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 204, targets := 256 }], pairs := [(2,8),(3,8)], upper := (rows 7 26 196 104 273 288 224 160 416), lower := (rows 7 26 196 104 273 288 64 128 256), losses := [] }

theorem u350 : Upper (D 10) (R 10) [6,24,192,96,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b350 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b351 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 402, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 196 104 304 33 480 416 416), lower := (rows 7 26 196 104 304 33 64 128 256), losses := [] }

theorem u351 : Upper (D 10) (R 10) [6,24,192,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b351 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b352 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 2, region := 40, targets := 256 }], pairs := [(3,8),(4,6)], upper := (rows 7 26 196 104 304 160 353 417 289), lower := (rows 7 26 196 104 304 160 64 128 256), losses := [] }

theorem u352 : Upper (D 10) (R 10) [6,24,192,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b352 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b353 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 26 196 104 304 288 225 161 417), lower := (rows 7 26 196 104 304 288 64 128 256), losses := [] }

theorem u353 : Upper (D 10) (R 10) [6,24,192,96,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b353 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b354 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 76 56 400 96 480 416 416), lower := (rows 7 35 76 56 400 96 64 128 256), losses := [] }

theorem u354 : Upper (D 10) (R 10) [6,33,72,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b354 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b355 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 76 56 400 160 352 480 352), lower := (rows 7 35 76 56 400 160 64 128 256), losses := [] }

theorem u355 : Upper (D 10) (R 10) [6,33,72,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b355 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b356 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 35, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 76 152 304 96 480 416 416), lower := (rows 7 35 76 152 304 96 64 128 256), losses := [] }

theorem u356 : Upper (D 10) (R 10) [6,33,72,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b356 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b357 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(4,7)], upper := (rows 7 35 76 152 304 160 352 480 352), lower := (rows 7 35 76 152 304 160 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 168 0 128 256), good := (rows 7 35 47 184 304 160 0 160 256) }] }

theorem u357 : Upper (D 10) (R 10) [6,33,72,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b357 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b358 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 35 76 152 304 288 224 224 480), lower := (rows 7 35 76 152 304 288 64 128 256), losses := [] }

theorem u358 : Upper (D 10) (R 10) [6,33,72,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b358 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b359 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 51, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 168 112 48 448 384 384), lower := (rows 7 35 76 168 112 48 64 128 256), losses := [] }

theorem u359 : Upper (D 10) (R 10) [6,33,72,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b359 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u359
end Delivery.IrregularNine14.P10
