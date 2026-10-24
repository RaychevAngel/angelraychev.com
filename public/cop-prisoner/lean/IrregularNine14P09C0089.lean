import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0033
import IrregularNine14P09C0034

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r5340 : Route 9 := (fun mask => (mask,id))

def c5340 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5340 : Upper (D 9) (R 9) [34,192,72,384,260,16] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,260,16] 13 (by decide) (choices 1) [1,32] r5340 c5340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2006
  · exact u2007

def r5341 : Route 9 := (fun mask => (mask,id))

def c5341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5341 : Upper (D 9) (R 9) [34,192,72,384,288,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,288,1] 13 (by decide) (choices 1) [1,4,16] r5341 c5341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2008
  · exact u2009
  · exact u2010

def b5342 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 4, region := 195, targets := 256 }], pairs := [(0,8),(1,8),(3,6),(4,6)], upper := (rows 35 194 76 392 304 36 81 145 273), lower := (rows 35 194 76 392 304 36 64 128 256), losses := [] }

theorem u5342 : Upper (D 9) (R 9) [34,192,72,384,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5342 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5343 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 194 76 392 304 48 69 133 261), lower := (rows 35 194 76 392 304 48 64 128 256), losses := [] }

theorem u5343 : Upper (D 9) (R 9) [34,192,72,384,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5343 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5344 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 37, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(2,7),(2,8)], upper := (rows 35 194 100 265 276 33 216 152 408), lower := (rows 35 194 100 265 276 33 64 128 256), losses := [] }

theorem u5344 : Upper (D 9) (R 9) [34,192,96,257,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5344 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5345 : Route 9 := (fun mask => (mask,id))

def c5345 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5345 : Upper (D 9) (R 9) [34,192,96,257,260,8] 13 := by
  apply FastRouting.sound _ _ [34,192,96,257,260,8] 13 (by decide) (choices 1) [1,16,128] r5345 c5345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2011
  · exact u2012
  · exact u2013

def b5346 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 0, region := 392, targets := 64 },{ cop := 3, region := 194, targets := 256 }], pairs := [(1,5),(1,8),(3,5),(3,6)], upper := (rows 35 194 100 265 276 48 201 137 393), lower := (rows 35 194 100 265 276 48 64 128 256), losses := [] }

theorem u5346 : Upper (D 9) (R 9) [34,192,96,257,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5346 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5347 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 37, targets := 256 }], pairs := [(0,8),(2,7),(2,8),(3,7),(4,7)], upper := (rows 35 194 100 265 276 160 89 153 281), lower := (rows 35 194 100 265 276 160 64 128 256), losses := [] }

theorem u5347 : Upper (D 9) (R 9) [34,192,96,257,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5347 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5348 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 37, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(2,7),(2,8)], upper := (rows 35 194 100 265 400 33 92 156 284), lower := (rows 35 194 100 265 400 33 64 128 256), losses := [] }

theorem u5348 : Upper (D 9) (R 9) [34,192,96,257,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5348 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5349 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 37, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8)], upper := (rows 35 194 100 265 400 36 89 153 281), lower := (rows 35 194 100 265 400 36 64 128 256), losses := [] }

theorem u5349 : Upper (D 9) (R 9) [34,192,96,257,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5349 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5350 : Route 9 := (fun mask => (mask,id))

def c5350 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5350 : Upper (D 9) (R 9) [34,192,96,257,384,8] 13 := by
  apply FastRouting.sound _ _ [34,192,96,257,384,8] 13 (by decide) (choices 1) [1,4,16] r5350 c5350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2014
  · exact u2015
  · exact u2016

def r5351 : Route 9 := (fun mask => (mask,id))

def c5351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5351 : Upper (D 9) (R 9) [34,192,96,257,384,16] 13 := by
  apply FastRouting.sound _ _ [34,192,96,257,384,16] 13 (by decide) (choices 1) [1,4,8] r5351 c5351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2017
  · exact u2018
  · exact u2019

def b5352 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 37, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(2,7),(2,8)], upper := (rows 35 194 100 268 400 33 89 153 281), lower := (rows 35 194 100 268 400 33 64 128 256), losses := [] }

theorem u5352 : Upper (D 9) (R 9) [34,192,96,260,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5352 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5353 : Route 9 := (fun mask => (mask,id))

def c5353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5353 : Upper (D 9) (R 9) [34,192,96,260,384,8] 13 := by
  apply FastRouting.sound _ _ [34,192,96,260,384,8] 13 (by decide) (choices 1) [1,16] r5353 c5353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2020
  · exact u2021

def r5354 : Route 9 := (fun mask => (mask,id))

def c5354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5354 : Upper (D 9) (R 9) [34,192,96,260,384,16] 13 := by
  apply FastRouting.sound _ _ [34,192,96,260,384,16] 13 (by decide) (choices 1) [1,8] r5354 c5354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2022
  · exact u2023

def b5355 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 14 56 145 96 448 384 384), lower := (rows 97 7 14 56 145 96 64 128 256), losses := [] }

theorem u5355 : Upper (D 9) (R 9) [96,5,10,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5355 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5356 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 46, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8),(3,6)], upper := (rows 97 7 14 56 145 160 320 448 320), lower := (rows 97 7 14 56 145 160 64 128 256), losses := [] }

theorem u5356 : Upper (D 9) (R 9) [96,5,10,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5356 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5357 : Route 9 := (fun mask => (mask,id))

def c5357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5357 : Upper (D 9) (R 9) [96,5,10,48,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,10,48,129,256] 13 (by decide) (choices 1) [128,256] r5357 c5357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2024
  · exact u2025

def b5358 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 97 7 14 56 208 33 448 384 384), lower := (rows 97 7 14 56 208 33 64 128 256), losses := [] }

theorem u5358 : Upper (D 9) (R 9) [96,5,10,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5358 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5359 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 14 56 208 160 321 385 257), lower := (rows 97 7 14 56 208 160 64 128 256), losses := [] }

theorem u5359 : Upper (D 9) (R 9) [96,5,10,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5359 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5360 : Route 9 := (fun mask => (mask,id))

def c5360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5360 : Upper (D 9) (R 9) [96,5,10,48,192,256] 13 := by
  apply FastRouting.sound _ _ [96,5,10,48,192,256] 13 (by decide) (choices 1) [1,128,256] r5360 c5360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2026
  · exact u2027
  · exact u2028

def b5361 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(0,8),(3,0),(4,0),(4,5)], upper := (rows 97 7 14 56 400 33 448 448 448), lower := (rows 97 7 14 56 400 33 64 128 256), losses := [] }

theorem u5361 : Upper (D 9) (R 9) [96,5,10,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5361 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5362 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 14 56 400 96 449 385 385), lower := (rows 97 7 14 56 400 96 64 128 256), losses := [] }

theorem u5362 : Upper (D 9) (R 9) [96,5,10,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5362 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5363 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,6)], upper := (rows 97 7 14 56 400 160 321 449 321), lower := (rows 97 7 14 56 400 160 64 128 256), losses := [] }

theorem u5363 : Upper (D 9) (R 9) [96,5,10,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5363 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5364 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 14 152 273 96 480 416 416), lower := (rows 97 7 14 152 273 96 64 128 256), losses := [] }

theorem u5364 : Upper (D 9) (R 9) [96,5,10,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5364 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5365_32 : Upper (D 9) (R 9) [96,5,10,144,257,128,32] 13 :=
  permutation_upper _ _ _ [96,5,10,144,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2029

def r5365 : Route 9 := (fun mask => (mask,id))

def c5365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u5365 : Upper (D 9) (R 9) [96,5,10,144,257,128] 13 := by
  apply FastRouting.sound _ _ [96,5,10,144,257,128] 13 (by decide) (choices 1) [32,256] r5365 c5365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5365_32
  · exact u2030

def b5366 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 232, targets := 1 },{ cop := 5, region := 193, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,8)], upper := (rows 97 7 14 152 273 288 224 224 480), lower := (rows 97 7 14 152 273 288 64 128 256), losses := [{ target := 8, region := (rows 33 18 28 24 16 32 97 161 0), good := (rows 225 199 14 158 223 225 64 128 0) }] }

theorem u5366 : Upper (D 9) (R 9) [96,5,10,144,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5366 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5367 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 6, region := 33, targets := 384 },{ cop := 4, region := 200, targets := 32 }], pairs := [(0,7),(0,8),(3,0),(3,5),(4,0)], upper := (rows 97 7 14 152 304 33 448 448 448), lower := (rows 97 7 14 152 304 33 64 128 256), losses := [] }

theorem u5367 : Upper (D 9) (R 9) [96,5,10,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5367 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5368 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 14 152 304 96 449 385 385), lower := (rows 97 7 14 152 304 96 64 128 256), losses := [] }

theorem u5368 : Upper (D 9) (R 9) [96,5,10,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5368 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5369 : Route 9 := (fun mask => (mask,id))

def c5369 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5369 : Upper (D 9) (R 9) [96,5,10,144,288,128] 13 := by
  apply FastRouting.sound _ _ [96,5,10,144,288,128] 13 (by decide) (choices 1) [1,256] r5369 c5369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2031
  · exact u2032

def b5370 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 7 14 152 304 288 193 193 449), lower := (rows 97 7 14 152 304 288 64 128 256), losses := [] }

theorem u5370 : Upper (D 9) (R 9) [96,5,10,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5370 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5371 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 46, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 14 168 145 48 320 448 320), lower := (rows 97 7 14 168 145 48 64 128 256), losses := [] }

theorem u5371 : Upper (D 9) (R 9) [96,5,10,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5371 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5372 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 14 168 145 96 336 400 272), lower := (rows 97 7 14 168 145 96 64 128 256), losses := [] }

theorem u5372 : Upper (D 9) (R 9) [96,5,10,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5372 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5373 : Route 9 := (fun mask => (mask,id))

def c5373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5373 : Upper (D 9) (R 9) [96,5,10,160,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,10,160,129,256] 13 (by decide) (choices 1) [16,256] r5373 c5373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2033
  · exact u2034

def b5374 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 0, region := 408, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,8)], upper := (rows 97 7 14 168 208 33 336 400 272), lower := (rows 97 7 14 168 208 33 64 128 256), losses := [] }

theorem u5374 : Upper (D 9) (R 9) [96,5,10,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5374 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5375 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 14 168 208 48 321 385 257), lower := (rows 97 7 14 168 208 48 64 128 256), losses := [] }

theorem u5375 : Upper (D 9) (R 9) [96,5,10,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5375 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5376 : Route 9 := (fun mask => (mask,id))

def c5376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5376 : Upper (D 9) (R 9) [96,5,10,160,192,256] 13 := by
  apply FastRouting.sound _ _ [96,5,10,160,192,256] 13 (by decide) (choices 1) [1,16,256] r5376 c5376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2035
  · exact u2036
  · exact u2037

def r5377 : Route 9 := (fun mask => (mask,id))

def c5377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5377 : Upper (D 9) (R 9) [96,5,10,160,257,16] 13 := by
  apply FastRouting.sound _ _ [96,5,10,160,257,16] 13 (by decide) (choices 1) [128,256] r5377 c5377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2038
  · exact u2039

def b5378 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 14 168 273 96 464 400 400), lower := (rows 97 7 14 168 273 96 64 128 256), losses := [] }

theorem u5378 : Upper (D 9) (R 9) [96,5,10,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5378 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5379 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 97 7 14 168 273 160 336 464 336), lower := (rows 97 7 14 168 273 160 64 128 256), losses := [] }

theorem u5379 : Upper (D 9) (R 9) [96,5,10,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5379 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5380 : Route 9 := (fun mask => (mask,id))

def c5380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5380 : Upper (D 9) (R 9) [96,5,10,160,257,256] 13 := by
  apply FastRouting.sound _ _ [96,5,10,160,257,256] 13 (by decide) (choices 1) [16,128] r5380 c5380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2040
  · exact u2041

def b5381 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 4, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(0,8),(3,0),(4,0),(4,5)], upper := (rows 97 7 14 168 336 33 464 400 400), lower := (rows 97 7 14 168 336 33 64 128 256), losses := [] }

theorem u5381 : Upper (D 9) (R 9) [96,5,10,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5381 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5382 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 7 14 168 336 48 449 385 385), lower := (rows 97 7 14 168 336 48 64 128 256), losses := [] }

theorem u5382 : Upper (D 9) (R 9) [96,5,10,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5382 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5383 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 97 7 14 168 336 160 337 401 273), lower := (rows 97 7 14 168 336 160 64 128 256), losses := [] }

theorem u5383 : Upper (D 9) (R 9) [96,5,10,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5383 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5384 : Route 9 := (fun mask => (mask,id))

def c5384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5384 : Upper (D 9) (R 9) [96,5,10,160,320,256] 13 := by
  apply FastRouting.sound _ _ [96,5,10,160,320,256] 13 (by decide) (choices 1) [1,16,128] r5384 c5384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2042
  · exact u2043
  · exact u2044

def b5385 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(0,8),(3,0),(4,0),(4,5)], upper := (rows 97 7 14 168 400 33 336 464 336), lower := (rows 97 7 14 168 400 33 64 128 256), losses := [] }

theorem u5385 : Upper (D 9) (R 9) [96,5,10,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5385 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5386 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 7 14 168 400 48 321 449 321), lower := (rows 97 7 14 168 400 48 64 128 256), losses := [] }

theorem u5386 : Upper (D 9) (R 9) [96,5,10,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5386 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5387 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 14 168 400 96 337 401 273), lower := (rows 97 7 14 168 400 96 64 128 256), losses := [] }

theorem u5387 : Upper (D 9) (R 9) [96,5,10,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5387 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5388 : Route 9 := (fun mask => (mask,id))

def c5388 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5388 : Upper (D 9) (R 9) [96,5,10,160,384,256] 13 := by
  apply FastRouting.sound _ _ [96,5,10,160,384,256] 13 (by decide) (choices 1) [1,16] r5388 c5388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2045
  · exact u2046

def r5389 : Route 9 := (fun mask => (mask,id))

def c5389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u5389 : Upper (D 9) (R 9) [96,5,10,384,129,16] 13 := by
  apply FastRouting.sound _ _ [96,5,10,384,129,16] 13 (by decide) (choices 1) [32,256] r5389 c5389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2047
  · exact u2048

def b5390 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 14 392 145 96 368 432 304), lower := (rows 97 7 14 392 145 96 64 128 256), losses := [] }

theorem u5390 : Upper (D 9) (R 9) [96,5,10,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5390 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5391_16 : Upper (D 9) (R 9) [96,5,10,384,129,256,16] 13 :=
  permutation_upper _ _ _ [96,5,10,384,129,16,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2048

theorem m5391_32 : Upper (D 9) (R 9) [96,5,10,384,129,256,32] 13 :=
  permutation_upper _ _ _ [96,5,10,384,129,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2049

def r5391 : Route 9 := (fun mask => (mask,id))

def c5391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5391 : Upper (D 9) (R 9) [96,5,10,384,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,10,384,129,256] 13 (by decide) (choices 1) [16,32] r5391 c5391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5391_16
  · exact m5391_32

def b5392 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 6, region := 33, targets := 384 },{ cop := 4, region := 328, targets := 32 }], pairs := [(0,7),(0,8),(3,0),(3,5),(4,0)], upper := (rows 97 7 14 392 176 33 336 464 336), lower := (rows 97 7 14 392 176 33 64 128 256), losses := [] }

theorem u5392 : Upper (D 9) (R 9) [96,5,10,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5392 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5393 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 7 14 392 176 48 321 449 321), lower := (rows 97 7 14 392 176 48 64 128 256), losses := [] }

theorem u5393 : Upper (D 9) (R 9) [96,5,10,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5393 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5394 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 14 392 176 96 337 401 273), lower := (rows 97 7 14 392 176 96 64 128 256), losses := [] }

theorem u5394 : Upper (D 9) (R 9) [96,5,10,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5394 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5395 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 65 },{ cop := 5, region := 209, targets := 256 },{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7),(0,8),(4,0),(4,6),(4,8)], upper := (rows 97 7 14 392 176 288 81 209 337), lower := (rows 97 7 14 392 176 288 64 128 256), losses := [] }

theorem u5395 : Upper (D 9) (R 9) [96,5,10,384,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5395 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5396 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 28 42 145 96 448 384 384), lower := (rows 97 7 28 42 145 96 64 128 256), losses := [] }

theorem u5396 : Upper (D 9) (R 9) [96,5,24,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5396 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5397 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 46, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8),(3,6)], upper := (rows 97 7 28 42 145 160 320 448 320), lower := (rows 97 7 28 42 145 160 64 128 256), losses := [] }

theorem u5397 : Upper (D 9) (R 9) [96,5,24,34,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5397 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5398 : Route 9 := (fun mask => (mask,id))

def c5398 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u5398 : Upper (D 9) (R 9) [96,5,24,34,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,24,34,129,256] 13 (by decide) (choices 1) [128,256] r5398 c5398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2050
  · exact u2051

def b5399 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 97 7 28 42 208 33 448 384 384), lower := (rows 97 7 28 42 208 33 64 128 256), losses := [] }

theorem u5399 : Upper (D 9) (R 9) [96,5,24,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5399 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u5399
end Delivery.IrregularNine14.P09
