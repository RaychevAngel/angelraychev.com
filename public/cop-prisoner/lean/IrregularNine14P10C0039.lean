import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0016
import IrregularNine14P10C0017

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2340 : Route 9 := (fun mask => (mask,id))

def c2340 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2340 : Upper (D 10) (R 10) [34,192,72,288,160] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,160] 13 (by decide) (choices 1) [1,4,16,256] r2340 c2340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1006
  · exact u1007
  · exact u1008
  · exact u1009

def r2341 : Route 9 := (fun mask => (mask,id))

def c2341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2341 : Upper (D 10) (R 10) [34,192,72,288,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,257] 13 (by decide) (choices 1) [4,16,128] r2341 c2341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1010
  · exact u1011
  · exact u1012

def b2342 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 227, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 76 296 276 177 241 177 433), lower := (rows 35 194 76 296 276 32 64 128 256), losses := [] }

theorem u2342 : Upper (D 10) (R 10) [34,192,72,288,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2342 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2343 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 35 194 76 296 304 181 213 149 405), lower := (rows 35 194 76 296 304 32 64 128 256), losses := [] }

theorem u2343 : Upper (D 10) (R 10) [34,192,72,288,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2343 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2344 : Route 9 := (fun mask => (mask,id))

def c2344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2344 : Upper (D 10) (R 10) [34,192,72,288,384] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,384] 13 (by decide) (choices 1) [1,4,16] r2344 c2344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1013
  · exact u1014
  · exact u1015

def r2345 : Route 9 := (fun mask => (mask,id))

def c2345 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2345 : Upper (D 10) (R 10) [34,192,72,384,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,257] 13 (by decide) (choices 1) [4,16] r2345 c2345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1016
  · exact u1017

def b2346 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 227, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 76 392 276 49 113 177 305), lower := (rows 35 194 76 392 276 32 64 128 256), losses := [] }

theorem u2346 : Upper (D 10) (R 10) [34,192,72,384,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2346 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2347 : Route 9 := (fun mask => (mask,id))

def c2347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2347 : Upper (D 10) (R 10) [34,192,72,384,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,288] 13 (by decide) (choices 1) [1,4,16] r2347 c2347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1018
  · exact u1019
  · exact u1020

theorem m2348_8 : Upper (D 10) (R 10) [34,192,96,160,257,8] 13 :=
  permutation_upper _ _ _ [34,192,96,160,257,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1021

def r2348 : Route 9 := (fun mask => (mask,id))

def c2348 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2348 : Upper (D 10) (R 10) [34,192,96,160,257] 13 := by
  apply FastRouting.sound _ _ [34,192,96,160,257] 13 (by decide) (choices 1) [4,8,16,256] r2348 c2348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1021
  · exact m2348_8
  · exact u1022
  · exact u1023

def r2349 : Route 9 := (fun mask => (mask,id))

def c2349 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2349 : Upper (D 10) (R 10) [34,192,96,160,260] 13 := by
  apply FastRouting.sound _ _ [34,192,96,160,260] 13 (by decide) (choices 1) [1,8,16,256] r2349 c2349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1024
  · exact u1025
  · exact u1026
  · exact u1027

def r2350 : Route 9 := (fun mask => (mask,id))

def c2350 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2350 : Upper (D 10) (R 10) [34,192,96,257,260] 13 := by
  apply FastRouting.sound _ _ [34,192,96,257,260] 13 (by decide) (choices 1) [8,16,128] r2350 c2350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1028
  · exact u1029
  · exact u1030

def b2351 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 35 194 100 265 280 180 244 180 436), lower := (rows 35 194 100 265 280 32 64 128 256), losses := [] }

theorem u2351 : Upper (D 10) (R 10) [34,192,96,257,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2351 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2352 : Route 9 := (fun mask => (mask,id))

def c2352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2352 : Upper (D 10) (R 10) [34,192,96,257,288] 13 := by
  apply FastRouting.sound _ _ [34,192,96,257,288] 13 (by decide) (choices 1) [4,8,16,128] r2352 c2352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1031
  · exact u1032
  · exact u1033
  · exact u1034

def r2353 : Route 9 := (fun mask => (mask,id))

def c2353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2353 : Upper (D 10) (R 10) [34,192,96,257,384] 13 := by
  apply FastRouting.sound _ _ [34,192,96,257,384] 13 (by decide) (choices 1) [4,8,16] r2353 c2353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1035
  · exact u1036
  · exact u1037

def b2354 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 35 194 100 268 280 177 241 177 433), lower := (rows 35 194 100 268 280 32 64 128 256), losses := [] }

theorem u2354 : Upper (D 10) (R 10) [34,192,96,260,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2354 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2355 : Route 9 := (fun mask => (mask,id))

def c2355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2355 : Upper (D 10) (R 10) [34,192,96,260,288] 13 := by
  apply FastRouting.sound _ _ [34,192,96,260,288] 13 (by decide) (choices 1) [1,8,16,128] r2355 c2355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1038
  · exact u1039
  · exact u1040
  · exact u1041

def r2356 : Route 9 := (fun mask => (mask,id))

def c2356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2356 : Upper (D 10) (R 10) [34,192,96,260,384] 13 := by
  apply FastRouting.sound _ _ [34,192,96,260,384] 13 (by decide) (choices 1) [1,8,16] r2356 c2356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1042
  · exact u1043
  · exact u1044

def b2357 : PairBound 9 := { available := 165, camps := [{ cop := 8, region := 24, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 35 194 100 280 280 165 229 165 421), lower := (rows 35 194 100 280 280 32 64 128 256), losses := [] }

theorem u2357 : Upper (D 10) (R 10) [34,192,96,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2357 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2358 : PairBound 9 := { available := 141, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 100 280 304 173 205 141 397), lower := (rows 35 194 100 280 304 32 64 128 256), losses := [] }

theorem u2358 : Upper (D 10) (R 10) [34,192,96,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2358 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2359 : PairBound 9 := { available := 45, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 100 280 400 45 109 173 301), lower := (rows 35 194 100 280 400 32 64 128 256), losses := [] }

theorem u2359 : Upper (D 10) (R 10) [34,192,96,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2359 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2360 : Route 9 := (fun mask => (mask,id))

def c2360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2360 : Upper (D 10) (R 10) [34,192,96,288,384] 13 := by
  apply FastRouting.sound _ _ [34,192,96,288,384] 13 (by decide) (choices 1) [1,4,8,16] r2360 c2360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1045
  · exact u1046
  · exact u1047
  · exact u1048

def b2361 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 4, targets := 288 }], pairs := [(2,5),(2,8)], upper := (rows 35 194 196 265 276 56 120 184 312), lower := (rows 35 194 196 265 276 32 64 128 256), losses := [] }

theorem u2361 : Upper (D 10) (R 10) [34,192,192,257,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2361 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2362 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 4, targets := 288 }], pairs := [(2,5),(2,8)], upper := (rows 35 194 196 265 304 60 124 188 316), lower := (rows 35 194 196 265 304 32 64 128 256), losses := [] }

theorem u2362 : Upper (D 10) (R 10) [34,192,192,257,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2362 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2363 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 4, targets := 288 }], pairs := [(2,5),(2,8)], upper := (rows 35 194 196 268 304 57 121 185 313), lower := (rows 35 194 196 268 304 32 64 128 256), losses := [] }

theorem u2363 : Upper (D 10) (R 10) [34,192,192,260,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2363 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2364 : PairBound 9 := { available := 308, camps := [{ cop := 6, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 67 67 140 296 176 308 372 436 308), lower := (rows 67 67 140 296 176 32 64 128 256), losses := [] }

theorem u2364 : Upper (D 10) (R 10) [66,65,136,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2364 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2365 : PairBound 9 := { available := 52, camps := [{ cop := 6, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 67 67 140 296 400 52 116 180 308), lower := (rows 67 67 140 296 400 32 64 128 256), losses := [] }

theorem u2365 : Upper (D 10) (R 10) [66,65,136,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2365 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2366 : PairBound 9 := { available := 60, camps := [{ cop := 6, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 67 67 164 296 400 60 124 188 316), lower := (rows 67 67 164 296 400 32 64 128 256), losses := [] }

theorem u2366 : Upper (D 10) (R 10) [66,65,160,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2366 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2367 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 133 152 304 296 360 424 296), lower := (rows 67 70 133 152 304 32 64 128 256), losses := [] }

theorem u2367 : Upper (D 10) (R 10) [66,68,129,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2367 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2368 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 133 168 280 304 368 432 304), lower := (rows 67 70 133 168 280 32 64 128 256), losses := [] }

theorem u2368 : Upper (D 10) (R 10) [66,68,129,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2368 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2369 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 133 168 304 312 376 440 312), lower := (rows 67 70 133 168 304 32 64 128 256), losses := [] }

theorem u2369 : Upper (D 10) (R 10) [66,68,129,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2369 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2370 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 133 296 400 56 120 184 312), lower := (rows 67 70 133 296 400 32 64 128 256), losses := [] }

theorem u2370 : Upper (D 10) (R 10) [66,68,129,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2370 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2371 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 140 265 176 304 368 432 304), lower := (rows 67 70 140 265 176 32 64 128 256), losses := [] }

theorem u2371 : Upper (D 10) (R 10) [66,68,136,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2371 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2372 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 140 265 304 176 240 176 432), lower := (rows 67 70 140 265 304 32 64 128 256), losses := [] }

theorem u2372 : Upper (D 10) (R 10) [66,68,136,257,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2372 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2373 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 140 265 400 48 112 176 304), lower := (rows 67 70 140 265 400 32 64 128 256), losses := [] }

theorem u2373 : Upper (D 10) (R 10) [66,68,136,257,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2373 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2374 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 140 296 145 304 368 432 304), lower := (rows 67 70 140 296 145 32 64 128 256), losses := [] }

theorem u2374 : Upper (D 10) (R 10) [66,68,136,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2374 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2375 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 140 296 176 305 369 433 305), lower := (rows 67 70 140 296 176 32 64 128 256), losses := [] }

theorem u2375 : Upper (D 10) (R 10) [66,68,136,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2375 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2376 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 140 296 273 176 240 176 432), lower := (rows 67 70 140 296 273 32 64 128 256), losses := [] }

theorem u2376 : Upper (D 10) (R 10) [66,68,136,288,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2376 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2377 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 140 296 400 49 113 177 305), lower := (rows 67 70 140 296 400 32 64 128 256), losses := [] }

theorem u2377 : Upper (D 10) (R 10) [66,68,136,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2377 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2378 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 164 137 280 304 368 432 304), lower := (rows 67 70 164 137 280 32 64 128 256), losses := [] }

theorem u2378 : Upper (D 10) (R 10) [66,68,160,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2378 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2379 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 164 137 304 312 376 440 312), lower := (rows 67 70 164 137 304 32 64 128 256), losses := [] }

theorem u2379 : Upper (D 10) (R 10) [66,68,160,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2379 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2380 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 164 152 273 296 360 424 296), lower := (rows 67 70 164 152 273 32 64 128 256), losses := [] }

theorem u2380 : Upper (D 10) (R 10) [66,68,160,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2380 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2381 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 164 152 304 297 361 425 297), lower := (rows 67 70 164 152 304 32 64 128 256), losses := [] }

theorem u2381 : Upper (D 10) (R 10) [66,68,160,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2381 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2382 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 164 265 304 184 248 184 440), lower := (rows 67 70 164 265 304 32 64 128 256), losses := [] }

theorem u2382 : Upper (D 10) (R 10) [66,68,160,257,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2382 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2383 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 164 265 400 56 120 184 312), lower := (rows 67 70 164 265 400 32 64 128 256), losses := [] }

theorem u2383 : Upper (D 10) (R 10) [66,68,160,257,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2383 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2384 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 164 296 400 57 121 185 313), lower := (rows 67 70 164 296 400 32 64 128 256), losses := [] }

theorem u2384 : Upper (D 10) (R 10) [66,68,160,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2384 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2385 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 388 137 280 48 112 176 304), lower := (rows 67 70 388 137 280 32 64 128 256), losses := [] }

theorem u2385 : Upper (D 10) (R 10) [66,68,384,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2385 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2386 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 388 137 304 56 120 184 312), lower := (rows 67 70 388 137 304 32 64 128 256), losses := [] }

theorem u2386 : Upper (D 10) (R 10) [66,68,384,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2386 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2387 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 388 152 304 41 105 169 297), lower := (rows 67 70 388 152 304 32 64 128 256), losses := [] }

theorem u2387 : Upper (D 10) (R 10) [66,68,384,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2387 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2388 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 388 168 304 57 121 185 313), lower := (rows 67 70 388 168 304 32 64 128 256), losses := [] }

theorem u2388 : Upper (D 10) (R 10) [66,68,384,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2388 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2389 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 133 152 304 300 364 428 300), lower := (rows 67 98 133 152 304 32 64 128 256), losses := [] }

theorem u2389 : Upper (D 10) (R 10) [66,96,129,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2389 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2390 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 133 168 276 312 376 440 312), lower := (rows 67 98 133 168 276 32 64 128 256), losses := [] }

theorem u2390 : Upper (D 10) (R 10) [66,96,129,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2390 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2391 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 133 168 280 308 372 436 308), lower := (rows 67 98 133 168 280 32 64 128 256), losses := [] }

theorem u2391 : Upper (D 10) (R 10) [66,96,129,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2391 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2392 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 133 168 304 316 348 412 284), lower := (rows 67 98 133 168 304 32 64 128 256), losses := [] }

theorem u2392 : Upper (D 10) (R 10) [66,96,129,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2392 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2393 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 133 268 304 184 248 184 440), lower := (rows 67 98 133 268 304 32 64 128 256), losses := [] }

theorem u2393 : Upper (D 10) (R 10) [66,96,129,260,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2393 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2394 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 133 268 400 56 120 184 312), lower := (rows 67 98 133 268 400 32 64 128 256), losses := [] }

theorem u2394 : Upper (D 10) (R 10) [66,96,129,260,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2394 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2395 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 133 296 400 60 124 188 316), lower := (rows 67 98 133 296 400 32 64 128 256), losses := [] }

theorem u2395 : Upper (D 10) (R 10) [66,96,129,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2395 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2396 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 140 296 176 309 341 405 277), lower := (rows 67 98 140 296 176 32 64 128 256), losses := [] }

theorem u2396 : Upper (D 10) (R 10) [66,96,136,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2396 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2397 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 140 296 400 53 117 181 309), lower := (rows 67 98 140 296 400 32 64 128 256), losses := [] }

theorem u2397 : Upper (D 10) (R 10) [66,96,136,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2397 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2398 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 164 296 400 61 93 157 285), lower := (rows 67 98 164 296 400 32 64 128 256), losses := [] }

theorem u2398 : Upper (D 10) (R 10) [66,96,160,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2398 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2399 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 76 152 276 288 352 416 288), lower := (rows 67 131 76 152 276 32 64 128 256), losses := [] }

theorem u2399 : Upper (D 10) (R 10) [66,129,72,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2399 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u2399
end Delivery.IrregularNine14.P10
