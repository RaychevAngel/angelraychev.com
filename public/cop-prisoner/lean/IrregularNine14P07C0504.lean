import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0199
import IrregularNine14P07C0200

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30240 : Route 9 := (fun mask => (mask,id))

def c30240 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30240 : Upper (D 7) (R 7) [6,24,288,65,96] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,96] 13 (by decide) (choices 1) [1,2,128] r30240 c30240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11968
  · exact u11969
  · exact u11970

theorem m30241_128 : Upper (D 7) (R 7) [6,24,288,65,129,128] 13 :=
  permutation_upper _ _ _ [6,24,288,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u11972

def r30241 : Route 9 := (fun mask => (mask,id))

def c30241 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30241 : Upper (D 7) (R 7) [6,24,288,65,129] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,129] 13 (by decide) (choices 1) [2,64,128] r30241 c30241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11971
  · exact u11972
  · exact m30241_128

def r30242 : Route 9 := (fun mask => (mask,id))

def c30242 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30242 : Upper (D 7) (R 7) [6,24,288,65,130] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,130] 13 (by decide) (choices 1) [1,64,128] r30242 c30242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11973
  · exact u11974
  · exact u11975

def r30243 : Route 9 := (fun mask => (mask,id))

def c30243 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30243 : Upper (D 7) (R 7) [6,24,288,65,160] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,160] 13 (by decide) (choices 1) [1,2,64,128] r30243 c30243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11976
  · exact u11977
  · exact u11978
  · exact u11979

def r30244 : Route 9 := (fun mask => (mask,id))

def c30244 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30244 : Upper (D 7) (R 7) [6,24,288,65,192] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,192] 13 (by decide) (choices 1) [1,2,128] r30244 c30244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11980
  · exact u11981
  · exact u11982

def b30245 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 10, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 7 26 292 74 112 161 193 129 385), lower := (rows 7 26 292 74 112 32 64 128 256), losses := [] }

theorem u30245 : Upper (D 7) (R 7) [6,24,288,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30246 : Route 9 := (fun mask => (mask,id))

def c30246 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30246 : Upper (D 7) (R 7) [6,24,288,66,160] 13 := by
  apply FastRouting.sound _ _ [6,24,288,66,160] 13 (by decide) (choices 1) [1,64,128] r30246 c30246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11983
  · exact u11984
  · exact u11985

def b30247 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 10, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 7 26 292 74 208 161 225 161 417), lower := (rows 7 26 292 74 208 32 64 128 256), losses := [] }

theorem u30247 : Upper (D 7) (R 7) [6,24,288,66,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30248 : Route 9 := (fun mask => (mask,id))

def c30248 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30248 : Upper (D 7) (R 7) [6,24,288,96,192] 13 := by
  apply FastRouting.sound _ _ [6,24,288,96,192] 13 (by decide) (choices 1) [1,2,128] r30248 c30248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11986
  · exact u11987
  · exact u11988

def b30249 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 18, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 7 26 292 200 208 35 99 163 291), lower := (rows 7 26 292 200 208 32 64 128 256), losses := [] }

theorem u30249 : Upper (D 7) (R 7) [6,24,288,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30250 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 7 35 13 88 50 480 448 448 448), lower := (rows 7 35 13 88 50 32 64 128 256), losses := [] }

theorem u30250 : Upper (D 7) (R 7) [6,33,9,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30251 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 13, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 13 88 82 416 480 416 416), lower := (rows 7 35 13 88 82 32 64 128 256), losses := [] }

theorem u30251 : Upper (D 7) (R 7) [6,33,9,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30252 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 13 88 112 418 450 386 386), lower := (rows 7 35 13 88 112 32 64 128 256), losses := [] }

theorem u30252 : Upper (D 7) (R 7) [6,33,9,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30253 : Route 9 := (fun mask => (mask,id))

def c30253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30253 : Upper (D 7) (R 7) [6,33,9,80,130] 13 := by
  apply FastRouting.sound _ _ [6,33,9,80,130] 13 (by decide) (choices 1) [64,128,256] r30253 c30253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11989
  · exact u11990
  · exact u11991

def r30254 : Route 9 := (fun mask => (mask,id))

def c30254 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30254 : Upper (D 7) (R 7) [6,33,9,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,9,80,160] 13 (by decide) (choices 1) [2,64,128,256] r30254 c30254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11992
  · exact u11993
  · exact u11994
  · exact u11995

def b30255 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 35 13 88 208 418 482 418 418), lower := (rows 7 35 13 88 208 32 64 128 256), losses := [] }

theorem u30255 : Upper (D 7) (R 7) [6,33,9,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30256 : Route 9 := (fun mask => (mask,id))

def c30256 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30256 : Upper (D 7) (R 7) [6,33,9,80,258] 13 := by
  apply FastRouting.sound _ _ [6,33,9,80,258] 13 (by decide) (choices 1) [64,128] r30256 c30256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11996
  · exact u11997

def r30257 : Route 9 := (fun mask => (mask,id))

def c30257 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30257 : Upper (D 7) (R 7) [6,33,9,80,288] 13 := by
  apply FastRouting.sound _ _ [6,33,9,80,288] 13 (by decide) (choices 1) [2,64,128] r30257 c30257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11998
  · exact u11999
  · exact u12000

def b30258 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 7 35 13 88 336 162 226 162 418), lower := (rows 7 35 13 88 336 32 64 128 256), losses := [] }

theorem u30258 : Upper (D 7) (R 7) [6,33,9,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30259 : Route 9 := (fun mask => (mask,id))

def c30259 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30259 : Upper (D 7) (R 7) [6,33,9,80,384] 13 := by
  apply FastRouting.sound _ _ [6,33,9,80,384] 13 (by decide) (choices 1) [2,64,128] r30259 c30259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12001
  · exact u12002
  · exact u12003

def b30260 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 7 35 13 200 50 496 464 464 464), lower := (rows 7 35 13 200 50 32 64 128 256), losses := [] }

theorem u30260 : Upper (D 7) (R 7) [6,33,9,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30261 : Route 9 := (fun mask => (mask,id))

def c30261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u30261 : Upper (D 7) (R 7) [6,33,9,192,66] 13 := by
  apply FastRouting.sound _ _ [6,33,9,192,66] 13 (by decide) (choices 1) [16,128,256] r30261 c30261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12004
  · exact u12005
  · exact u12006

def r30262 : Route 9 := (fun mask => (mask,id))

def c30262 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u30262 : Upper (D 7) (R 7) [6,33,9,192,96] 13 := by
  apply FastRouting.sound _ _ [6,33,9,192,96] 13 (by decide) (choices 1) [2,16,128,256] r30262 c30262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12007
  · exact u12008
  · exact u12009
  · exact u12010

def b30263 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 7 35 13 200 208 306 370 434 306), lower := (rows 7 35 13 200 208 32 64 128 256), losses := [] }

theorem u30263 : Upper (D 7) (R 7) [6,33,9,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30264 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30264 : Upper (D 7) (R 7) [6,33,9,192,258] 13 := by
  apply FastRouting.sound _ _ [6,33,9,192,258] 13 (by decide) (choices 1) [16,64] r30264 c30264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12011
  · exact u12012

def r30265 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30265 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30265 : Upper (D 7) (R 7) [6,33,9,192,288] 13 := by
  apply FastRouting.sound _ _ [6,33,9,192,288] 13 (by decide) (choices 1) [2,16,64] r30265 c30265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12013
  · exact u12014
  · exact u12015

def r30266 : Route 9 := (fun mask => (mask,id))

def c30266 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30266 : Upper (D 7) (R 7) [6,33,9,192,320] 13 := by
  apply FastRouting.sound _ _ [6,33,9,192,320] 13 (by decide) (choices 1) [2,16,128] r30266 c30266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12016
  · exact u12017
  · exact u12018

def b30267 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 7 35 13 280 50 224 192 192 448), lower := (rows 7 35 13 280 50 32 64 128 256), losses := [] }

theorem u30267 : Upper (D 7) (R 7) [6,33,9,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30268 : Route 9 := (fun mask => (mask,id))

def c30268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30268 : Upper (D 7) (R 7) [6,33,9,272,66] 13 := by
  apply FastRouting.sound _ _ [6,33,9,272,66] 13 (by decide) (choices 1) [64,128] r30268 c30268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12019
  · exact u12020

def r30269 : Route 9 := (fun mask => (mask,id))

def c30269 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30269 : Upper (D 7) (R 7) [6,33,9,272,96] 13 := by
  apply FastRouting.sound _ _ [6,33,9,272,96] 13 (by decide) (choices 1) [2,64,128] r30269 c30269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12021
  · exact u12022
  · exact u12023

def r30270 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30270 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30270 : Upper (D 7) (R 7) [6,33,9,272,192] 13 := by
  apply FastRouting.sound _ _ [6,33,9,272,192] 13 (by decide) (choices 1) [2,64] r30270 c30270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12024
  · exact u12025

def b30271 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 7 35 13 328 50 240 208 208 464), lower := (rows 7 35 13 328 50 32 64 128 256), losses := [] }

theorem u30271 : Upper (D 7) (R 7) [6,33,9,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30272 : Route 9 := (fun mask => (mask,id))

def c30272 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30272 : Upper (D 7) (R 7) [6,33,9,320,66] 13 := by
  apply FastRouting.sound _ _ [6,33,9,320,66] 13 (by decide) (choices 1) [16,128] r30272 c30272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12026
  · exact u12027

def r30273 : Route 9 := (fun mask => (mask,id))

def c30273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30273 : Upper (D 7) (R 7) [6,33,9,320,96] 13 := by
  apply FastRouting.sound _ _ [6,33,9,320,96] 13 (by decide) (choices 1) [2,16,128] r30273 c30273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12028
  · exact u12029
  · exact u12030

def r30274 : Route 9 := (fun mask => (mask,id))

def c30274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30274 : Upper (D 7) (R 7) [6,33,9,320,130] 13 := by
  apply FastRouting.sound _ _ [6,33,9,320,130] 13 (by decide) (choices 1) [16,64,128] r30274 c30274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12031
  · exact u12032
  · exact u12033

def r30275 : Route 9 := (fun mask => (mask,id))

def c30275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30275 : Upper (D 7) (R 7) [6,33,9,320,160] 13 := by
  apply FastRouting.sound _ _ [6,33,9,320,160] 13 (by decide) (choices 1) [2,16,64,128] r30275 c30275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12034
  · exact u12035
  · exact u12036
  · exact u12037

def r30276 : Route 9 := (fun mask => (mask,id))

def c30276 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30276 : Upper (D 7) (R 7) [6,33,9,320,192] 13 := by
  apply FastRouting.sound _ _ [6,33,9,320,192] 13 (by decide) (choices 1) [2,16,128] r30276 c30276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12038
  · exact u12039
  · exact u12040

def b30277 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 15, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 11 112 480 448 448 448), lower := (rows 7 35 28 11 112 32 64 128 256), losses := [] }

theorem u30277 : Upper (D 7) (R 7) [6,33,24,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30278 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 28 11 208 480 480 480 480), lower := (rows 7 35 28 11 208 32 64 128 256), losses := [] }

theorem u30278 : Upper (D 7) (R 7) [6,33,24,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30279 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 15, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 28 11 304 224 192 192 448), lower := (rows 7 35 28 11 304 32 64 128 256), losses := [] }

theorem u30279 : Upper (D 7) (R 7) [6,33,24,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30280 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 28 11 336 224 224 224 480), lower := (rows 7 35 28 11 336 32 64 128 256), losses := [] }

theorem u30280 : Upper (D 7) (R 7) [6,33,24,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30281 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 28 41 82 480 448 448 448), lower := (rows 7 35 28 41 82 32 64 128 256), losses := [] }

theorem u30281 : Upper (D 7) (R 7) [6,33,24,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30282 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 28 41 208 482 450 450 450), lower := (rows 7 35 28 41 208 32 64 128 256), losses := [] }

theorem u30282 : Upper (D 7) (R 7) [6,33,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30283 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 28 41 274 224 192 192 448), lower := (rows 7 35 28 41 274 32 64 128 256), losses := [] }

theorem u30283 : Upper (D 7) (R 7) [6,33,24,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30284 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 8, targets := 192 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 35 28 41 336 226 194 194 450), lower := (rows 7 35 28 41 336 32 64 128 256), losses := [] }

theorem u30284 : Upper (D 7) (R 7) [6,33,24,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30285 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 469, targets := 32 },{ cop := 1, region := 8, targets := 64 }], pairs := [(0,5),(2,5),(3,6),(4,5)], upper := (rows 7 35 28 42 81 480 448 448 448), lower := (rows 7 35 28 42 81 32 64 128 256), losses := [] }

theorem u30285 : Upper (D 7) (R 7) [6,33,24,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30286 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 35 28 42 208 481 449 449 449), lower := (rows 7 35 28 42 208 32 64 128 256), losses := [] }

theorem u30286 : Upper (D 7) (R 7) [6,33,24,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30287 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 469, targets := 32 },{ cop := 1, region := 8, targets := 64 }], pairs := [(0,5),(2,5),(3,6),(4,5)], upper := (rows 7 35 28 42 273 224 192 192 448), lower := (rows 7 35 28 42 273 32 64 128 256), losses := [] }

theorem u30287 : Upper (D 7) (R 7) [6,33,24,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30288 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 35 28 42 336 225 193 193 449), lower := (rows 7 35 28 42 336 32 64 128 256), losses := [] }

theorem u30288 : Upper (D 7) (R 7) [6,33,24,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30289 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 13, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 28 73 82 416 480 416 416), lower := (rows 7 35 28 73 82 32 64 128 256), losses := [] }

theorem u30289 : Upper (D 7) (R 7) [6,33,24,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30290 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 28 73 112 418 450 386 386), lower := (rows 7 35 28 73 112 32 64 128 256), losses := [] }

theorem u30290 : Upper (D 7) (R 7) [6,33,24,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30290 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30291 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 0, region := 488, targets := 2 }], pairs := [(2,0),(2,1),(3,1),(4,0)], upper := (rows 7 35 28 73 146 480 480 480 480), lower := (rows 7 35 28 73 146 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 511 511 511 511), good := (rows 502 498 508 508 498 480 480 480 480) },{ target := 1, region := (rows 1 0 20 11 16 511 511 511 511), good := (rows 493 489 508 489 508 480 480 480 480) }] }

theorem u30291 : Upper (D 7) (R 7) [6,33,24,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30292 : Route 9 := (fun mask => (mask,id))

def c30292 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30292 : Upper (D 7) (R 7) [6,33,24,65,160] 13 := by
  apply FastRouting.sound _ _ [6,33,24,65,160] 13 (by decide) (choices 1) [2,64,128,256] r30292 c30292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12041
  · exact u12042
  · exact u12043
  · exact u12044

def b30293 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 496, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 7 35 28 73 208 418 482 418 418), lower := (rows 7 35 28 73 208 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 35 67 131 259), good := (rows 502 498 28 508 208 32 64 128 256) }] }

theorem u30293 : Upper (D 7) (R 7) [6,33,24,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30294 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 0, region := 232, targets := 2 }], pairs := [(2,0),(2,1),(3,1),(4,0)], upper := (rows 7 35 28 73 274 224 224 224 480), lower := (rows 7 35 28 73 274 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 511 511 511 511), good := (rows 502 498 508 508 498 480 480 480 480) },{ target := 1, region := (rows 1 0 20 11 16 511 511 511 511), good := (rows 493 489 508 489 508 480 480 480 480) }] }

theorem u30294 : Upper (D 7) (R 7) [6,33,24,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30295 : Route 9 := (fun mask => (mask,id))

def c30295 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30295 : Upper (D 7) (R 7) [6,33,24,65,288] 13 := by
  apply FastRouting.sound _ _ [6,33,24,65,288] 13 (by decide) (choices 1) [2,64,128] r30295 c30295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12045
  · exact u12046
  · exact u12047

def b30296 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 0, region := 496, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 7 35 28 73 336 162 226 162 418), lower := (rows 7 35 28 73 336 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 35 67 131 259), good := (rows 502 498 28 508 336 32 64 128 256) }] }

theorem u30296 : Upper (D 7) (R 7) [6,33,24,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30297 : Route 9 := (fun mask => (mask,id))

def c30297 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30297 : Upper (D 7) (R 7) [6,33,24,65,384] 13 := by
  apply FastRouting.sound _ _ [6,33,24,65,384] 13 (by decide) (choices 1) [2,64,128] r30297 c30297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12048
  · exact u12049
  · exact u12050

def b30298 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 28 74 112 417 449 385 385), lower := (rows 7 35 28 74 112 32 64 128 256), losses := [] }

theorem u30298 : Upper (D 7) (R 7) [6,33,24,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30299 : Route 9 := (fun mask => (mask,id))

def c30299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30299 : Upper (D 7) (R 7) [6,33,24,66,160] 13 := by
  apply FastRouting.sound _ _ [6,33,24,66,160] 13 (by decide) (choices 1) [1,64,128,256] r30299 c30299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12051
  · exact u12052
  · exact u12053
  · exact u12054

#print axioms u30299
end Delivery.IrregularNine14.P07
