import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0007
import IrregularNine14P09C0008

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3300 : Route 9 := (fun mask => (mask,id))

def c3300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3300 : Upper (D 9) (R 9) [6,40,80,65,129,256] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65,129,256] 13 (by decide) (choices 1) [32,128,256] r3300 c3300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u427
  · exact u428
  · exact u429

def b3301 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 42 84 73 176 33 448 384 384), lower := (rows 7 42 84 73 176 33 64 128 256), losses := [] }

theorem u3301 : Upper (D 9) (R 9) [6,40,80,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3301 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3302 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 335, targets := 128 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 7 42 84 73 176 160 321 385 257), lower := (rows 7 42 84 73 176 160 64 128 256), losses := [] }

theorem u3302 : Upper (D 9) (R 9) [6,40,80,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3302 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3303 : Route 9 := (fun mask => (mask,id))

def c3303 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3303 : Upper (D 9) (R 9) [6,40,80,65,160,256] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65,160,256] 13 (by decide) (choices 1) [1,128,256] r3303 c3303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u430
  · exact u431
  · exact u432

def b3304 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 42 84 73 400 33 480 416 416), lower := (rows 7 42 84 73 400 33 64 128 256), losses := [] }

theorem u3304 : Upper (D 9) (R 9) [6,40,80,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3304 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3305 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(0,8),(1,6),(1,8),(3,8),(4,6)], upper := (rows 7 42 84 73 400 160 353 417 289), lower := (rows 7 42 84 73 400 160 64 128 256), losses := [{ target := 8, region := (rows 5 6 4 12 16 176 64 128 0), good := (rows 15 42 127 73 176 160 64 160 0) }] }

theorem u3305 : Upper (D 9) (R 9) [6,40,80,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3305 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3306 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 50, targets := 320 },{ cop := 1, region := 468, targets := 1 }], pairs := [(1,6),(1,8),(2,0),(4,6),(4,8)], upper := (rows 7 42 84 137 176 33 320 448 320), lower := (rows 7 42 84 137 176 33 64 128 256), losses := [] }

theorem u3306 : Upper (D 9) (R 9) [6,40,80,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3306 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3307 : Route 9 := (fun mask => (mask,id))

def c3307 : Nat → Fin 9 := (fun mask => match mask with | 1 => 8 | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3307 : Upper (D 9) (R 9) [6,40,80,129,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,160,64] 13 (by decide) (choices 1) [256] r3307 c3307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u433

def r3308 : Route 9 := (fun mask => (mask,id))

def c3308 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3308 : Upper (D 9) (R 9) [6,40,80,129,160,256] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,160,256] 13 (by decide) (choices 1) [1,256] r3308 c3308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u434
  · exact u435

def r3309 : Route 9 := (fun mask => (mask,id))

def c3309 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3309 : Upper (D 9) (R 9) [6,40,80,129,257,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,257,64] 13 (by decide) (choices 1) [32,128,256] r3309 c3309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u436
  · exact u437
  · exact u438

def b3310 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 320 }], pairs := [(0,7),(1,6),(1,8),(2,7),(4,7)], upper := (rows 7 42 84 137 273 160 352 480 352), lower := (rows 7 42 84 137 273 160 64 128 256), losses := [] }

theorem u3310 : Upper (D 9) (R 9) [6,40,80,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3310 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m3311_32 : Upper (D 9) (R 9) [6,40,80,129,257,256,32] 13 :=
  permutation_upper _ _ _ [6,40,80,129,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u437

def r3311 : Route 9 := (fun mask => (mask,id))

def c3311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3311 : Upper (D 9) (R 9) [6,40,80,129,257,256] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,257,256] 13 (by decide) (choices 1) [32,128] r3311 c3311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m3311_32
  · exact u439

def b3312 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 34, targets := 448 },{ cop := 1, region := 468, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(2,0),(4,0)], upper := (rows 7 42 84 137 304 33 448 448 448), lower := (rows 7 42 84 137 304 33 64 128 256), losses := [] }

theorem u3312 : Upper (D 9) (R 9) [6,40,80,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3312 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3313 : Route 9 := (fun mask => (mask,id))

def c3313 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3313 : Upper (D 9) (R 9) [6,40,80,129,288,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,288,64] 13 (by decide) (choices 1) [1,128,256] r3313 c3313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u440
  · exact u441
  · exact u442

def b3314 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(2,7),(4,7)], upper := (rows 7 42 84 137 304 160 321 449 321), lower := (rows 7 42 84 137 304 160 64 128 256), losses := [] }

theorem u3314 : Upper (D 9) (R 9) [6,40,80,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3314 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3315 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 42 84 137 304 288 193 193 449), lower := (rows 7 42 84 137 304 288 64 128 256), losses := [] }

theorem u3315 : Upper (D 9) (R 9) [6,40,80,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3315 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3316 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 320 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(1,8),(2,0),(4,0)], upper := (rows 7 42 84 137 400 33 352 480 352), lower := (rows 7 42 84 137 400 33 64 128 256), losses := [] }

theorem u3316 : Upper (D 9) (R 9) [6,40,80,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3316 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3317 : Route 9 := (fun mask => (mask,id))

def c3317 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3317 : Upper (D 9) (R 9) [6,40,80,129,384,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,384,64] 13 (by decide) (choices 1) [1,32,256] r3317 c3317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u443
  · exact u444
  · exact u445

def r3318 : Route 9 := (fun mask => (mask,id))

def c3318 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3318 : Upper (D 9) (R 9) [6,40,80,129,384,256] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,384,256] 13 (by decide) (choices 1) [1,32] r3318 c3318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u446
  · exact u447

def b3319 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 55, targets := 256 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,8)], upper := (rows 7 42 84 200 176 33 321 385 257), lower := (rows 7 42 84 200 176 33 64 128 256), losses := [] }

theorem u3319 : Upper (D 9) (R 9) [6,40,80,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3319 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m3320_1 : Upper (D 9) (R 9) [6,40,80,192,160,256,1] 13 :=
  permutation_upper _ _ _ [6,40,80,192,160,1,256] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u448

def r3320 : Route 9 := (fun mask => (mask,id))

def c3320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3320 : Upper (D 9) (R 9) [6,40,80,192,160,256] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,160,256] 13 (by decide) (choices 1) [1,256] r3320 c3320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m3320_1
  · exact u449

def r3321 : Route 9 := (fun mask => (mask,id))

def c3321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3321 : Upper (D 9) (R 9) [6,40,80,192,288,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,288,1] 13 (by decide) (choices 1) [1,128,256] r3321 c3321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u450
  · exact u451
  · exact u452

def b3322 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(2,7),(4,7)], upper := (rows 7 42 84 200 304 160 321 385 257), lower := (rows 7 42 84 200 304 160 64 128 256), losses := [] }

theorem u3322 : Upper (D 9) (R 9) [6,40,80,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3322 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3323 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 42 84 200 304 288 193 129 385), lower := (rows 7 42 84 200 304 288 64 128 256), losses := [] }

theorem u3323 : Upper (D 9) (R 9) [6,40,80,192,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3323 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3324 : Route 9 := (fun mask => (mask,id))

def c3324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3324 : Upper (D 9) (R 9) [6,40,80,192,384,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,384,1] 13 (by decide) (choices 1) [1,32,256] r3324 c3324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u453
  · exact u454
  · exact u455

def r3325 : Route 9 := (fun mask => (mask,id))

def c3325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3325 : Upper (D 9) (R 9) [6,40,80,192,384,256] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,384,256] 13 (by decide) (choices 1) [1,32] r3325 c3325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u456
  · exact u457

def b3326 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 42 100 25 208 33 448 384 384), lower := (rows 7 42 100 25 208 33 64 128 256), losses := [] }

theorem u3326 : Upper (D 9) (R 9) [6,40,96,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3326 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3327 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(3,8)], upper := (rows 7 42 100 25 208 160 321 385 257), lower := (rows 7 42 100 25 208 160 64 128 256), losses := [] }

theorem u3327 : Upper (D 9) (R 9) [6,40,96,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3327 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3328 : Route 9 := (fun mask => (mask,id))

def c3328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3328 : Upper (D 9) (R 9) [6,40,96,17,192,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17,192,256] 13 (by decide) (choices 1) [1,128,256] r3328 c3328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u458
  · exact u459
  · exact u460

def b3329 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 34, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(3,5),(4,5)], upper := (rows 7 42 100 25 400 33 448 448 448), lower := (rows 7 42 100 25 400 33 64 128 256), losses := [] }

theorem u3329 : Upper (D 9) (R 9) [6,40,96,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3329 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3330 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 42 100 25 400 96 449 385 385), lower := (rows 7 42 100 25 400 96 64 128 256), losses := [] }

theorem u3330 : Upper (D 9) (R 9) [6,40,96,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3330 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3331 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(1,0),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 25 400 160 321 449 321), lower := (rows 7 42 100 25 400 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 6 42 100 58 432 160 64 160 256) }] }

theorem u3331 : Upper (D 9) (R 9) [6,40,96,17,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3331 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3332 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 42 100 88 145 33 448 384 384), lower := (rows 7 42 100 88 145 33 64 128 256), losses := [] }

theorem u3332 : Upper (D 9) (R 9) [6,40,96,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3332 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3333 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 325, targets := 128 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,7),(2,7),(3,5),(4,5),(4,6)], upper := (rows 7 42 100 88 145 160 321 385 257), lower := (rows 7 42 100 88 145 160 64 128 256), losses := [] }

theorem u3333 : Upper (D 9) (R 9) [6,40,96,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3333 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3334 : Route 9 := (fun mask => (mask,id))

def c3334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3334 : Upper (D 9) (R 9) [6,40,96,80,129,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,80,129,256] 13 (by decide) (choices 1) [1,128,256] r3334 c3334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u461
  · exact u462
  · exact u463

def b3335 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 42 100 88 400 33 449 385 385), lower := (rows 7 42 100 88 400 33 64 128 256), losses := [] }

theorem u3335 : Upper (D 9) (R 9) [6,40,96,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3335 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3336 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 325, targets := 128 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,7),(2,7),(3,5),(4,5),(4,6)], upper := (rows 7 42 100 88 400 160 321 385 257), lower := (rows 7 42 100 88 400 160 64 128 256), losses := [] }

theorem u3336 : Upper (D 9) (R 9) [6,40,96,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3336 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3337 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(3,8)], upper := (rows 7 42 100 137 208 33 336 400 272), lower := (rows 7 42 100 137 208 33 64 128 256), losses := [] }

theorem u3337 : Upper (D 9) (R 9) [6,40,96,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3337 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3338 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 42 100 137 208 48 321 385 257), lower := (rows 7 42 100 137 208 48 64 128 256), losses := [] }

theorem u3338 : Upper (D 9) (R 9) [6,40,96,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3338 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3339 : Route 9 := (fun mask => (mask,id))

def c3339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3339 : Upper (D 9) (R 9) [6,40,96,129,192,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,192,256] 13 (by decide) (choices 1) [1,16,256] r3339 c3339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u464
  · exact u465
  · exact u466

def r3340 : Route 9 := (fun mask => (mask,id))

def c3340 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3340 : Upper (D 9) (R 9) [6,40,96,129,257,16] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,257,16] 13 (by decide) (choices 1) [128,256] r3340 c3340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u467
  · exact u468

def b3341 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 42 100 137 273 96 464 400 400), lower := (rows 7 42 100 137 273 96 64 128 256), losses := [] }

theorem u3341 : Upper (D 9) (R 9) [6,40,96,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3341 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3342 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(2,7),(4,7)], upper := (rows 7 42 100 137 273 160 336 464 336), lower := (rows 7 42 100 137 273 160 64 128 256), losses := [] }

theorem u3342 : Upper (D 9) (R 9) [6,40,96,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3342 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3343 : Route 9 := (fun mask => (mask,id))

def c3343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3343 : Upper (D 9) (R 9) [6,40,96,129,257,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,257,256] 13 (by decide) (choices 1) [16,128] r3343 c3343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u469
  · exact u470

def b3344 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 34, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(3,5),(4,5)], upper := (rows 7 42 100 137 336 33 464 400 400), lower := (rows 7 42 100 137 336 33 64 128 256), losses := [] }

theorem u3344 : Upper (D 9) (R 9) [6,40,96,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3344 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3345 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 42 100 137 336 48 449 385 385), lower := (rows 7 42 100 137 336 48 64 128 256), losses := [] }

theorem u3345 : Upper (D 9) (R 9) [6,40,96,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3345 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3346 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(2,7),(4,7)], upper := (rows 7 42 100 137 336 160 337 401 273), lower := (rows 7 42 100 137 336 160 64 128 256), losses := [] }

theorem u3346 : Upper (D 9) (R 9) [6,40,96,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3346 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3347 : Route 9 := (fun mask => (mask,id))

def c3347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3347 : Upper (D 9) (R 9) [6,40,96,129,320,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,320,256] 13 (by decide) (choices 1) [1,16,128] r3347 c3347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u471
  · exact u472
  · exact u473

def b3348 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 34, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(3,5),(4,5)], upper := (rows 7 42 100 137 400 33 336 464 336), lower := (rows 7 42 100 137 400 33 64 128 256), losses := [] }

theorem u3348 : Upper (D 9) (R 9) [6,40,96,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3348 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3349 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 137 400 48 321 449 321), lower := (rows 7 42 100 137 400 48 64 128 256), losses := [] }

theorem u3349 : Upper (D 9) (R 9) [6,40,96,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3349 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3350 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 42 100 137 400 96 337 401 273), lower := (rows 7 42 100 137 400 96 64 128 256), losses := [] }

theorem u3350 : Upper (D 9) (R 9) [6,40,96,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3350 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3351 : Route 9 := (fun mask => (mask,id))

def c3351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3351 : Upper (D 9) (R 9) [6,40,96,129,384,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,384,256] 13 (by decide) (choices 1) [1,16] r3351 c3351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u474
  · exact u475

def b3352 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 426, targets := 64 },{ cop := 4, region := 36, targets := 128 }], pairs := [(1,6),(2,7),(3,5),(3,6),(4,5)], upper := (rows 7 42 100 152 81 33 448 384 384), lower := (rows 7 42 100 152 81 33 64 128 256), losses := [] }

theorem u3352 : Upper (D 9) (R 9) [6,40,96,144,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3352 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3353 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(2,7),(4,7)], upper := (rows 7 42 100 152 81 160 321 385 257), lower := (rows 7 42 100 152 81 160 64 128 256), losses := [] }

theorem u3353 : Upper (D 9) (R 9) [6,40,96,144,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3353 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3354 : Route 9 := (fun mask => (mask,id))

def c3354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3354 : Upper (D 9) (R 9) [6,40,96,144,65,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,65,256] 13 (by decide) (choices 1) [1,128,256] r3354 c3354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u476
  · exact u477
  · exact u478

def b3355 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 452, targets := 1 },{ cop := 4, region := 200, targets := 1 }], pairs := [(1,6),(2,0),(3,0),(3,5),(4,5)], upper := (rows 7 42 100 152 273 33 448 448 448), lower := (rows 7 42 100 152 273 33 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 16 49 0 128 256), good := (rows 39 42 36 186 305 33 0 128 256) }] }

theorem u3355 : Upper (D 9) (R 9) [6,40,96,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3355 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3356 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 42 100 152 273 96 449 385 385), lower := (rows 7 42 100 152 273 96 64 128 256), losses := [] }

theorem u3356 : Upper (D 9) (R 9) [6,40,96,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3356 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3357 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(2,7),(4,7)], upper := (rows 7 42 100 152 273 160 321 449 321), lower := (rows 7 42 100 152 273 160 64 128 256), losses := [] }

theorem u3357 : Upper (D 9) (R 9) [6,40,96,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3357 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3358 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 197, targets := 256 },{ cop := 4, region := 200, targets := 256 }], pairs := [(0,8),(2,8),(3,5),(3,8),(4,5)], upper := (rows 7 42 100 152 273 288 193 193 449), lower := (rows 7 42 100 152 273 288 64 128 256), losses := [] }

theorem u3358 : Upper (D 9) (R 9) [6,40,96,144,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3358 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3359 : Route 9 := (fun mask => (mask,id))

def c3359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3359 : Upper (D 9) (R 9) [6,40,96,144,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,320,1] 13 (by decide) (choices 1) [1,128,256] r3359 c3359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u479
  · exact u480
  · exact u481

#print axioms u3359
end Delivery.IrregularNine14.P09
