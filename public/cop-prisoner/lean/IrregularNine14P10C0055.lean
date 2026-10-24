import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0024
import IrregularNine14P10C0025
import IrregularNine14P10C0026
import IrregularNine14P10C0027
import IrregularNine14P10C0028
import IrregularNine14P10C0029
import IrregularNine14P10C0030
import IrregularNine14P10C0032
import IrregularNine14P10C0034
import IrregularNine14P10C0035
import IrregularNine14P10C0036
import IrregularNine14P10C0037
import IrregularNine14P10C0038
import IrregularNine14P10C0039
import IrregularNine14P10C0040
import IrregularNine14P10C0041

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3300 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 67 131 292 296 252 252 252 252 508), lower := (rows 67 131 292 296 16 32 64 128 256), losses := [] }

theorem u3300 : Upper (D 10) (R 10) [66,129,288,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3300 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3301 : PairBound 9 := { available := 188, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 67 131 292 328 188 188 252 188 444), lower := (rows 67 131 292 328 16 32 64 128 256), losses := [] }

theorem u3301 : Upper (D 10) (R 10) [66,129,288,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3301 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3302 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 324 392 60 60 124 188 316), lower := (rows 67 131 324 392 16 32 64 128 256), losses := [] }

theorem u3302 : Upper (D 10) (R 10) [66,129,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3302 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3303 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 168 305 305 369 433 305), lower := (rows 67 134 76 168 16 32 64 128 256), losses := [] }

theorem u3303 : Upper (D 10) (R 10) [66,132,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3303 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3304 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 265 432 432 496 432 432), lower := (rows 67 134 76 265 16 32 64 128 256), losses := [] }

theorem u3304 : Upper (D 10) (R 10) [66,132,72,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3304 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3305 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 296 433 433 497 433 433), lower := (rows 67 134 76 296 16 32 64 128 256), losses := [] }

theorem u3305 : Upper (D 10) (R 10) [66,132,72,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3305 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3306 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 392 305 305 369 433 305), lower := (rows 67 134 76 392 16 32 64 128 256), losses := [] }

theorem u3306 : Upper (D 10) (R 10) [66,132,72,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3306 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3307 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 84 168 313 297 361 425 297), lower := (rows 67 134 84 168 16 32 64 128 256), losses := [] }

theorem u3307 : Upper (D 10) (R 10) [66,132,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3307 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3308 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 84 265 440 424 488 424 424), lower := (rows 67 134 84 265 16 32 64 128 256), losses := [] }

theorem u3308 : Upper (D 10) (R 10) [66,132,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3308 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3309 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 84 296 441 425 489 425 425), lower := (rows 67 134 84 296 16 32 64 128 256), losses := [] }

theorem u3309 : Upper (D 10) (R 10) [66,132,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3309 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3310 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 84 392 313 297 361 425 297), lower := (rows 67 134 84 392 16 32 64 128 256), losses := [] }

theorem u3310 : Upper (D 10) (R 10) [66,132,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3310 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3311 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 100 168 313 313 377 441 313), lower := (rows 67 134 100 168 16 32 64 128 256), losses := [] }

theorem u3311 : Upper (D 10) (R 10) [66,132,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3311 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3312 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 100 265 440 440 504 440 440), lower := (rows 67 134 100 265 16 32 64 128 256), losses := [] }

theorem u3312 : Upper (D 10) (R 10) [66,132,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3312 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3313 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 100 296 441 441 505 441 441), lower := (rows 67 134 100 296 16 32 64 128 256), losses := [] }

theorem u3313 : Upper (D 10) (R 10) [66,132,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3313 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3314 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 100 392 313 313 377 441 313), lower := (rows 67 134 100 392 16 32 64 128 256), losses := [] }

theorem u3314 : Upper (D 10) (R 10) [66,132,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3314 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3315 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 3, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 67 134 196 265 312 312 376 440 312), lower := (rows 67 134 196 265 16 32 64 128 256), losses := [] }

theorem u3315 : Upper (D 10) (R 10) [66,132,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3315 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3316 : PairBound 9 := { available := 313, camps := [{ cop := 2, region := 3, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 67 134 196 296 313 313 377 441 313), lower := (rows 67 134 196 296 16 32 64 128 256), losses := [] }

theorem u3316 : Upper (D 10) (R 10) [66,132,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3316 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3317_40 : Upper (D 10) (R 10) [66,132,257,80,40] 13 :=
  permutation_upper _ _ _ [34,65,72,144,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1969

theorem m3317_136 : Upper (D 10) (R 10) [66,132,257,80,136] 13 :=
  permutation_upper _ _ _ [66,129,72,144,260] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2399

theorem m3317_264 : Upper (D 10) (R 10) [66,132,257,80,264] 13 :=
  permutation_upper _ _ _ [66,129,72,144,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2399

def r3317 : Route 9 := (fun mask => (mask,id))

def c3317 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3317 : Upper (D 10) (R 10) [66,132,257,80] 13 := by
  apply FastRouting.sound _ _ [66,132,257,80] 13 (by decide) (choices 2) [40,136,160,264,288,384] r3317 c3317
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3317_40
  · exact m3317_136
  · exact u2436
  · exact m3317_264
  · exact u2437
  · exact u2438

theorem m3318_40 : Upper (D 10) (R 10) [66,132,257,96,40] 13 :=
  permutation_upper _ _ _ [34,96,72,144,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2266

theorem m3318_136 : Upper (D 10) (R 10) [66,132,257,96,136] 13 :=
  permutation_upper _ _ _ [66,132,257,80,288] (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2437

theorem m3318_264 : Upper (D 10) (R 10) [66,132,257,96,264] 13 :=
  permutation_upper _ _ _ [66,132,257,80,160] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2436

theorem m3318_288 : Upper (D 10) (R 10) [66,132,257,96,288] 13 :=
  permutation_upper _ _ _ [66,132,257,96,160] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2439

def r3318 : Route 9 := (fun mask => (mask,id))

def c3318 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3318 : Upper (D 10) (R 10) [66,132,257,96] 13 := by
  apply FastRouting.sound _ _ [66,132,257,96] 13 (by decide) (choices 2) [40,136,160,264,288,384] r3318 c3318
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3318_40
  · exact m3318_136
  · exact u2439
  · exact m3318_264
  · exact m3318_288
  · exact u2440

def b3319 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 304, targets := 64 },{ cop := 3, region := 304, targets := 128 }], pairs := [(4,6),(4,7)], upper := (rows 67 134 261 200 312 312 376 440 312), lower := (rows 67 134 261 200 16 32 64 128 256), losses := [] }

theorem u3319 : Upper (D 10) (R 10) [66,132,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3319 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3320_33 : Upper (D 10) (R 10) [66,132,264,80,33] 13 :=
  permutation_upper _ _ _ [34,68,136,272,65] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2140

theorem m3320_129 : Upper (D 10) (R 10) [66,132,264,80,129] 13 :=
  permutation_upper _ _ _ [66,132,72,144,257] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2415

theorem m3320_257 : Upper (D 10) (R 10) [66,132,264,80,257] 13 :=
  permutation_upper _ _ _ [66,132,72,144,257] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2415

theorem m3320_288 : Upper (D 10) (R 10) [66,132,264,80,288] 13 :=
  permutation_upper _ _ _ [66,132,96,144,257] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2427

def r3320 : Route 9 := (fun mask => (mask,id))

def c3320 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3320 : Upper (D 10) (R 10) [66,132,264,80] 13 := by
  apply FastRouting.sound _ _ [66,132,264,80] 13 (by decide) (choices 2) [33,129,160,257,288,384] r3320 c3320
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3320_33
  · exact m3320_129
  · exact u2441
  · exact m3320_257
  · exact m3320_288
  · exact u2442

theorem m3321_33 : Upper (D 10) (R 10) [66,132,264,96,33] 13 :=
  permutation_upper _ _ _ [34,68,136,272,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2141

theorem m3321_129 : Upper (D 10) (R 10) [66,132,264,96,129] 13 :=
  permutation_upper _ _ _ [66,132,72,272,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2421

theorem m3321_257 : Upper (D 10) (R 10) [66,132,264,96,257] 13 :=
  permutation_upper _ _ _ [66,132,264,80,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2441

def r3321 : Route 9 := (fun mask => (mask,id))

def c3321 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3321 : Upper (D 10) (R 10) [66,132,264,96] 13 := by
  apply FastRouting.sound _ _ [66,132,264,96] 13 (by decide) (choices 2) [33,129,160,257,288,384] r3321 c3321
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3321_33
  · exact m3321_129
  · exact u2443
  · exact m3321_257
  · exact u2444
  · exact u2445

def b3322 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(4,7)], upper := (rows 67 134 268 200 305 305 369 433 305), lower := (rows 67 134 268 200 16 32 64 128 256), losses := [] }

theorem u3322 : Upper (D 10) (R 10) [66,132,264,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3322 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3323 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 243, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 67 134 268 328 177 177 241 177 433), lower := (rows 67 134 268 328 16 32 64 128 256), losses := [] }

theorem u3323 : Upper (D 10) (R 10) [66,132,264,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3323 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3324_9 : Upper (D 10) (R 10) [66,132,272,96,9] 13 :=
  permutation_upper _ _ _ [6,72,96,144,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1553

theorem m3324_33 : Upper (D 10) (R 10) [66,132,272,96,33] 13 :=
  permutation_upper _ _ _ [34,68,136,257,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2134

theorem m3324_40 : Upper (D 10) (R 10) [66,132,272,96,40] 13 :=
  permutation_upper _ _ _ [34,96,72,144,257] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2265

theorem m3324_129 : Upper (D 10) (R 10) [66,132,272,96,129] 13 :=
  permutation_upper _ _ _ [66,132,72,257,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2419

theorem m3324_136 : Upper (D 10) (R 10) [66,132,272,96,136] 13 :=
  permutation_upper _ _ _ [66,132,72,288,257] (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2423

theorem m3324_160 : Upper (D 10) (R 10) [66,132,272,96,160] 13 :=
  permutation_upper _ _ _ [66,132,96,257,288] (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2432

theorem m3324_257 : Upper (D 10) (R 10) [66,132,272,96,257] 13 :=
  permutation_upper _ _ _ [66,68,136,257,160] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2371

theorem m3324_264 : Upper (D 10) (R 10) [66,132,272,96,264] 13 :=
  permutation_upper _ _ _ [66,68,160,144,257] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2380

theorem m3324_288 : Upper (D 10) (R 10) [66,132,272,96,288] 13 :=
  permutation_upper _ _ _ [66,96,129,260,288] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2393

theorem m3324_384 : Upper (D 10) (R 10) [66,132,272,96,384] 13 :=
  permutation_upper _ _ _ [66,132,192,257,288] (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2435

def r3324 : Route 9 := (fun mask => (mask,id))

def c3324 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3324 : Upper (D 10) (R 10) [66,132,272,96] 13 := by
  apply FastRouting.sound _ _ [66,132,272,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r3324 c3324
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3324_9
  · exact m3324_33
  · exact m3324_40
  · exact m3324_129
  · exact m3324_136
  · exact m3324_160
  · exact m3324_257
  · exact m3324_264
  · exact m3324_288
  · exact m3324_384

theorem m3325_9 : Upper (D 10) (R 10) [66,132,272,160,9] 13 :=
  permutation_upper _ _ _ [6,72,160,144,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1620

theorem m3325_33 : Upper (D 10) (R 10) [66,132,272,160,33] 13 :=
  permutation_upper _ _ _ [34,68,136,257,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2135

theorem m3325_40 : Upper (D 10) (R 10) [66,132,272,160,40] 13 :=
  permutation_upper _ _ _ [34,96,72,129,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2260

theorem m3325_65 : Upper (D 10) (R 10) [66,132,272,160,65] 13 :=
  permutation_upper _ _ _ [66,68,136,257,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2371

theorem m3325_72 : Upper (D 10) (R 10) [66,132,272,160,72] 13 :=
  permutation_upper _ _ _ [66,132,264,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2441

theorem m3325_96 : Upper (D 10) (R 10) [66,132,272,160,96] 13 :=
  permutation_upper _ _ _ [66,132,264,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2443

theorem m3325_257 : Upper (D 10) (R 10) [66,132,272,160,257] 13 :=
  permutation_upper _ _ _ [66,68,136,257,288] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2372

theorem m3325_264 : Upper (D 10) (R 10) [66,132,272,160,264] 13 :=
  permutation_upper _ _ _ [66,68,160,129,264] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2378

theorem m3325_288 : Upper (D 10) (R 10) [66,132,272,160,288] 13 :=
  permutation_upper _ _ _ [66,96,129,160,260] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2390

theorem m3325_320 : Upper (D 10) (R 10) [66,132,272,160,320] 13 :=
  permutation_upper _ _ _ [66,132,264,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2447

def r3325 : Route 9 := (fun mask => (mask,id))

def c3325 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3325 : Upper (D 10) (R 10) [66,132,272,160] 13 := by
  apply FastRouting.sound _ _ [66,132,272,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r3325 c3325
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3325_9
  · exact m3325_33
  · exact m3325_40
  · exact m3325_65
  · exact m3325_72
  · exact m3325_96
  · exact m3325_257
  · exact m3325_264
  · exact m3325_288
  · exact m3325_320

theorem m3326_9 : Upper (D 10) (R 10) [66,132,272,192,9] 13 :=
  permutation_upper _ _ _ [6,72,192,144,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1675

theorem m3326_33 : Upper (D 10) (R 10) [66,132,272,192,33] 13 :=
  permutation_upper _ _ _ [34,68,136,257,192] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2136

theorem m3326_40 : Upper (D 10) (R 10) [66,132,272,192,40] 13 :=
  permutation_upper _ _ _ [34,192,72,144,257] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2321

theorem m3326_257 : Upper (D 10) (R 10) [66,132,272,192,257] 13 :=
  permutation_upper _ _ _ [66,68,136,257,384] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2373

theorem m3326_264 : Upper (D 10) (R 10) [66,132,272,192,264] 13 :=
  permutation_upper _ _ _ [66,68,384,129,264] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2385

theorem m3326_288 : Upper (D 10) (R 10) [66,132,272,192,288] 13 :=
  permutation_upper _ _ _ [66,96,129,260,384] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2394

def r3326 : Route 9 := (fun mask => (mask,id))

def c3326 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3326 : Upper (D 10) (R 10) [66,132,272,192] 13 := by
  apply FastRouting.sound _ _ [66,132,272,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r3326 c3326
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3326_9
  · exact m3326_33
  · exact m3326_40
  · exact m3326_257
  · exact m3326_264
  · exact m3326_288

theorem m3327_9 : Upper (D 10) (R 10) [66,132,272,288,9] 13 :=
  permutation_upper _ _ _ [6,72,160,272,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1640

theorem m3327_33 : Upper (D 10) (R 10) [66,132,272,288,33] 13 :=
  permutation_upper _ _ _ [34,68,136,257,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2137

theorem m3327_40 : Upper (D 10) (R 10) [66,132,272,288,40] 13 :=
  permutation_upper _ _ _ [34,96,65,132,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2253

theorem m3327_65 : Upper (D 10) (R 10) [66,132,272,288,65] 13 :=
  permutation_upper _ _ _ [66,68,136,257,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2372

theorem m3327_72 : Upper (D 10) (R 10) [66,132,272,288,72] 13 :=
  permutation_upper _ _ _ [66,132,96,144,257] (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2427

theorem m3327_96 : Upper (D 10) (R 10) [66,132,272,288,96] 13 :=
  permutation_upper _ _ _ [66,132,264,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2444

theorem m3327_129 : Upper (D 10) (R 10) [66,132,272,288,129] 13 :=
  permutation_upper _ _ _ [66,132,72,257,160] (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2419

theorem m3327_136 : Upper (D 10) (R 10) [66,132,272,288,136] 13 :=
  permutation_upper _ _ _ [66,132,72,160,257] (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2417

theorem m3327_160 : Upper (D 10) (R 10) [66,132,272,288,160] 13 :=
  permutation_upper _ _ _ [66,132,96,160,257] (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2429

theorem m3327_192 : Upper (D 10) (R 10) [66,132,272,288,192] 13 :=
  permutation_upper _ _ _ [66,132,264,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2446

def r3327 : Route 9 := (fun mask => (mask,id))

def c3327 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3327 : Upper (D 10) (R 10) [66,132,272,288] 13 := by
  apply FastRouting.sound _ _ [66,132,272,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r3327 c3327
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3327_9
  · exact m3327_33
  · exact m3327_40
  · exact m3327_65
  · exact m3327_72
  · exact m3327_96
  · exact m3327_129
  · exact m3327_136
  · exact m3327_160
  · exact m3327_192

theorem m3328_9 : Upper (D 10) (R 10) [66,132,272,320,9] 13 :=
  permutation_upper _ _ _ [6,72,192,272,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1684

theorem m3328_33 : Upper (D 10) (R 10) [66,132,272,320,33] 13 :=
  permutation_upper _ _ _ [34,68,136,257,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2138

theorem m3328_40 : Upper (D 10) (R 10) [66,132,272,320,40] 13 :=
  permutation_upper _ _ _ [34,192,65,144,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2310

theorem m3328_129 : Upper (D 10) (R 10) [66,132,272,320,129] 13 :=
  permutation_upper _ _ _ [66,132,72,257,384] (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2420

theorem m3328_136 : Upper (D 10) (R 10) [66,132,272,320,136] 13 :=
  permutation_upper _ _ _ [66,132,72,384,257] (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2425

theorem m3328_160 : Upper (D 10) (R 10) [66,132,272,320,160] 13 :=
  permutation_upper _ _ _ [66,132,96,257,384] (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2433

def r3328 : Route 9 := (fun mask => (mask,id))

def c3328 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u3328 : Upper (D 10) (R 10) [66,132,272,320] 13 := by
  apply FastRouting.sound _ _ [66,132,272,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r3328 c3328
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3328_9
  · exact m3328_33
  · exact m3328_40
  · exact m3328_129
  · exact m3328_136
  · exact m3328_160

theorem m3329_9 : Upper (D 10) (R 10) [66,132,272,384,9] 13 :=
  permutation_upper _ _ _ [6,72,384,144,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1716

theorem m3329_33 : Upper (D 10) (R 10) [66,132,272,384,33] 13 :=
  permutation_upper _ _ _ [34,68,136,257,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2139

theorem m3329_40 : Upper (D 10) (R 10) [66,132,272,384,40] 13 :=
  permutation_upper _ _ _ [34,192,65,132,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2308

theorem m3329_65 : Upper (D 10) (R 10) [66,132,272,384,65] 13 :=
  permutation_upper _ _ _ [66,68,136,257,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2373

theorem m3329_72 : Upper (D 10) (R 10) [66,132,272,384,72] 13 :=
  permutation_upper _ _ _ [66,132,264,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2442

theorem m3329_96 : Upper (D 10) (R 10) [66,132,272,384,96] 13 :=
  permutation_upper _ _ _ [66,132,264,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2445

def r3329 : Route 9 := (fun mask => (mask,id))

def c3329 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u3329 : Upper (D 10) (R 10) [66,132,272,384] 13 := by
  apply FastRouting.sound _ _ [66,132,272,384] 13 (by decide) (choices 2) [9,33,40,65,72,96] r3329 c3329
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3329_9
  · exact m3329_33
  · exact m3329_40
  · exact m3329_65
  · exact m3329_72
  · exact m3329_96

theorem m3330_9 : Upper (D 10) (R 10) [66,132,288,80,9] 13 :=
  permutation_upper _ _ _ [6,65,72,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1440

theorem m3330_33 : Upper (D 10) (R 10) [66,132,288,80,33] 13 :=
  permutation_upper _ _ _ [34,68,136,288,65] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2149

theorem m3330_40 : Upper (D 10) (R 10) [66,132,288,80,40] 13 :=
  permutation_upper _ _ _ [34,65,72,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1970

theorem m3330_129 : Upper (D 10) (R 10) [66,132,288,80,129] 13 :=
  permutation_upper _ _ _ [66,132,72,144,288] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2416

theorem m3330_136 : Upper (D 10) (R 10) [66,132,288,80,136] 13 :=
  permutation_upper _ _ _ [66,129,72,144,288] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2400

theorem m3330_257 : Upper (D 10) (R 10) [66,132,288,80,257] 13 :=
  permutation_upper _ _ _ [66,132,72,272,160] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2421

theorem m3330_264 : Upper (D 10) (R 10) [66,132,288,80,264] 13 :=
  permutation_upper _ _ _ [66,129,72,272,160] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2404

def r3330 : Route 9 := (fun mask => (mask,id))

def c3330 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3330 : Upper (D 10) (R 10) [66,132,288,80] 13 := by
  apply FastRouting.sound _ _ [66,132,288,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r3330 c3330
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3330_9
  · exact m3330_33
  · exact m3330_40
  · exact m3330_129
  · exact m3330_136
  · exact u2448
  · exact m3330_257
  · exact m3330_264
  · exact u2449
  · exact u2450

theorem m3331_9 : Upper (D 10) (R 10) [66,132,288,96,9] 13 :=
  permutation_upper _ _ _ [6,72,96,144,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1554

theorem m3331_33 : Upper (D 10) (R 10) [66,132,288,96,33] 13 :=
  permutation_upper _ _ _ [34,68,136,288,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2150

theorem m3331_40 : Upper (D 10) (R 10) [66,132,288,96,40] 13 :=
  permutation_upper _ _ _ [34,96,72,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2267

theorem m3331_129 : Upper (D 10) (R 10) [66,132,288,96,129] 13 :=
  permutation_upper _ _ _ [66,132,72,288,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2422

theorem m3331_257 : Upper (D 10) (R 10) [66,132,288,96,257] 13 :=
  permutation_upper _ _ _ [66,132,264,96,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2443

def r3331 : Route 9 := (fun mask => (mask,id))

def c3331 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3331 : Upper (D 10) (R 10) [66,132,288,96] 13 := by
  apply FastRouting.sound _ _ [66,132,288,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r3331 c3331
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3331_9
  · exact m3331_33
  · exact m3331_40
  · exact m3331_129
  · exact u2451
  · exact u2452
  · exact m3331_257
  · exact u2453
  · exact u2454
  · exact u2455

theorem m3332_9 : Upper (D 10) (R 10) [66,132,288,144,9] 13 :=
  permutation_upper _ _ _ [6,65,136,80,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1457

theorem m3332_33 : Upper (D 10) (R 10) [66,132,288,144,33] 13 :=
  permutation_upper _ _ _ [34,68,136,288,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2151

theorem m3332_40 : Upper (D 10) (R 10) [66,132,288,144,40] 13 :=
  permutation_upper _ _ _ [34,65,72,160,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1972

theorem m3332_65 : Upper (D 10) (R 10) [66,132,288,144,65] 13 :=
  permutation_upper _ _ _ [66,68,136,288,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2374

theorem m3332_72 : Upper (D 10) (R 10) [66,132,288,144,72] 13 :=
  permutation_upper _ _ _ [66,129,72,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2400

theorem m3332_96 : Upper (D 10) (R 10) [66,132,288,144,96] 13 :=
  permutation_upper _ _ _ [66,132,288,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2451

theorem m3332_257 : Upper (D 10) (R 10) [66,132,288,144,257] 13 :=
  permutation_upper _ _ _ [66,132,264,80,160] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2441

theorem m3332_264 : Upper (D 10) (R 10) [66,132,288,144,264] 13 :=
  permutation_upper _ _ _ [66,129,72,160,260] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2401

def r3332 : Route 9 := (fun mask => (mask,id))

def c3332 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3332 : Upper (D 10) (R 10) [66,132,288,144] 13 := by
  apply FastRouting.sound _ _ [66,132,288,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r3332 c3332
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3332_9
  · exact m3332_33
  · exact m3332_40
  · exact m3332_65
  · exact m3332_72
  · exact m3332_96
  · exact m3332_257
  · exact m3332_264
  · exact u2456
  · exact u2457

theorem m3333_9 : Upper (D 10) (R 10) [66,132,288,160,9] 13 :=
  permutation_upper _ _ _ [6,72,160,144,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1621

theorem m3333_33 : Upper (D 10) (R 10) [66,132,288,160,33] 13 :=
  permutation_upper _ _ _ [34,68,136,288,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2152

theorem m3333_40 : Upper (D 10) (R 10) [66,132,288,160,40] 13 :=
  permutation_upper _ _ _ [34,96,72,160,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2270

theorem m3333_65 : Upper (D 10) (R 10) [66,132,288,160,65] 13 :=
  permutation_upper _ _ _ [66,68,136,288,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2375

theorem m3333_72 : Upper (D 10) (R 10) [66,132,288,160,72] 13 :=
  permutation_upper _ _ _ [66,132,288,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2448

theorem m3333_96 : Upper (D 10) (R 10) [66,132,288,160,96] 13 :=
  permutation_upper _ _ _ [66,132,288,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2452

theorem m3333_257 : Upper (D 10) (R 10) [66,132,288,160,257] 13 :=
  permutation_upper _ _ _ [66,132,264,96,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2444

def r3333 : Route 9 := (fun mask => (mask,id))

def c3333 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3333 : Upper (D 10) (R 10) [66,132,288,160] 13 := by
  apply FastRouting.sound _ _ [66,132,288,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r3333 c3333
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3333_9
  · exact m3333_33
  · exact m3333_40
  · exact m3333_65
  · exact m3333_72
  · exact m3333_96
  · exact m3333_257
  · exact u2458
  · exact u2459
  · exact u2460

theorem m3334_9 : Upper (D 10) (R 10) [66,132,288,192,9] 13 :=
  permutation_upper _ _ _ [6,72,192,144,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1676

theorem m3334_33 : Upper (D 10) (R 10) [66,132,288,192,33] 13 :=
  permutation_upper _ _ _ [34,68,136,288,192] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2153

theorem m3334_40 : Upper (D 10) (R 10) [66,132,288,192,40] 13 :=
  permutation_upper _ _ _ [34,192,72,144,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2323

theorem m3334_257 : Upper (D 10) (R 10) [66,132,288,192,257] 13 :=
  permutation_upper _ _ _ [66,132,264,96,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2445

def r3334 : Route 9 := (fun mask => (mask,id))

def c3334 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3334 : Upper (D 10) (R 10) [66,132,288,192] 13 := by
  apply FastRouting.sound _ _ [66,132,288,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r3334 c3334
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3334_9
  · exact m3334_33
  · exact m3334_40
  · exact m3334_257
  · exact u2461
  · exact u2462

theorem m3335_9 : Upper (D 10) (R 10) [66,132,288,272,9] 13 :=
  permutation_upper _ _ _ [6,65,136,272,96] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1465

theorem m3335_33 : Upper (D 10) (R 10) [66,132,288,272,33] 13 :=
  permutation_upper _ _ _ [34,68,136,288,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2154

theorem m3335_40 : Upper (D 10) (R 10) [66,132,288,272,40] 13 :=
  permutation_upper _ _ _ [34,65,96,132,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1978

theorem m3335_65 : Upper (D 10) (R 10) [66,132,288,272,65] 13 :=
  permutation_upper _ _ _ [66,68,136,288,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2376

theorem m3335_72 : Upper (D 10) (R 10) [66,132,288,272,72] 13 :=
  permutation_upper _ _ _ [66,129,72,272,160] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2404

theorem m3335_96 : Upper (D 10) (R 10) [66,132,288,272,96] 13 :=
  permutation_upper _ _ _ [66,132,288,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2453

theorem m3335_129 : Upper (D 10) (R 10) [66,132,288,272,129] 13 :=
  permutation_upper _ _ _ [66,132,72,288,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2423

theorem m3335_136 : Upper (D 10) (R 10) [66,132,288,272,136] 13 :=
  permutation_upper _ _ _ [66,129,72,160,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2401

theorem m3335_160 : Upper (D 10) (R 10) [66,132,288,272,160] 13 :=
  permutation_upper _ _ _ [66,132,288,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2458

theorem m3335_192 : Upper (D 10) (R 10) [66,132,288,272,192] 13 :=
  permutation_upper _ _ _ [66,132,288,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2461

def r3335 : Route 9 := (fun mask => (mask,id))

def c3335 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3335 : Upper (D 10) (R 10) [66,132,288,272] 13 := by
  apply FastRouting.sound _ _ [66,132,288,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r3335 c3335
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3335_9
  · exact m3335_33
  · exact m3335_40
  · exact m3335_65
  · exact m3335_72
  · exact m3335_96
  · exact m3335_129
  · exact m3335_136
  · exact m3335_160
  · exact m3335_192

def b3336 : PairBound 9 := { available := 249, camps := [{ cop := 2, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 67 134 292 296 249 249 249 249 505), lower := (rows 67 134 292 296 16 32 64 128 256), losses := [] }

theorem u3336 : Upper (D 10) (R 10) [66,132,288,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3336 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3337_9 : Upper (D 10) (R 10) [66,132,288,320,9] 13 :=
  permutation_upper _ _ _ [6,72,192,272,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1685

theorem m3337_33 : Upper (D 10) (R 10) [66,132,288,320,33] 13 :=
  permutation_upper _ _ _ [34,68,136,288,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2156

theorem m3337_40 : Upper (D 10) (R 10) [66,132,288,320,40] 13 :=
  permutation_upper _ _ _ [34,192,72,272,160] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2335

theorem m3337_129 : Upper (D 10) (R 10) [66,132,288,320,129] 13 :=
  permutation_upper _ _ _ [66,132,72,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2424

theorem m3337_136 : Upper (D 10) (R 10) [66,132,288,320,136] 13 :=
  permutation_upper _ _ _ [66,132,288,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2457

theorem m3337_160 : Upper (D 10) (R 10) [66,132,288,320,160] 13 :=
  permutation_upper _ _ _ [66,132,288,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2460

def r3337 : Route 9 := (fun mask => (mask,id))

def c3337 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u3337 : Upper (D 10) (R 10) [66,132,288,320] 13 := by
  apply FastRouting.sound _ _ [66,132,288,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r3337 c3337
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3337_9
  · exact m3337_33
  · exact m3337_40
  · exact m3337_129
  · exact m3337_136
  · exact m3337_160

theorem m3338_9 : Upper (D 10) (R 10) [66,132,288,384,9] 13 :=
  permutation_upper _ _ _ [6,72,384,144,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1717

theorem m3338_33 : Upper (D 10) (R 10) [66,132,288,384,33] 13 :=
  permutation_upper _ _ _ [34,68,136,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2157

theorem m3338_40 : Upper (D 10) (R 10) [66,132,288,384,40] 13 :=
  permutation_upper _ _ _ [34,192,72,160,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2325

theorem m3338_65 : Upper (D 10) (R 10) [66,132,288,384,65] 13 :=
  permutation_upper _ _ _ [66,68,136,288,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2377

theorem m3338_72 : Upper (D 10) (R 10) [66,132,288,384,72] 13 :=
  permutation_upper _ _ _ [66,132,288,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2450

theorem m3338_96 : Upper (D 10) (R 10) [66,132,288,384,96] 13 :=
  permutation_upper _ _ _ [66,132,288,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2455

def r3338 : Route 9 := (fun mask => (mask,id))

def c3338 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u3338 : Upper (D 10) (R 10) [66,132,288,384] 13 := by
  apply FastRouting.sound _ _ [66,132,288,384] 13 (by decide) (choices 2) [9,33,40,65,72,96] r3338 c3338
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3338_9
  · exact m3338_33
  · exact m3338_40
  · exact m3338_65
  · exact m3338_72
  · exact m3338_96

def b3339 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 324 168 313 313 377 441 313), lower := (rows 67 134 324 168 16 32 64 128 256), losses := [] }

theorem u3339 : Upper (D 10) (R 10) [66,132,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3339 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3340 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 324 296 185 185 249 185 441), lower := (rows 67 134 324 296 16 32 64 128 256), losses := [] }

theorem u3340 : Upper (D 10) (R 10) [66,132,320,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3340 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3341 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 324 392 57 57 121 185 313), lower := (rows 67 134 324 392 16 32 64 128 256), losses := [] }

theorem u3341 : Upper (D 10) (R 10) [66,132,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3341 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3342 : PairBound 9 := { available := 313, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 67 134 388 104 313 313 377 441 313), lower := (rows 67 134 388 104 16 32 64 128 256), losses := [] }

theorem u3342 : Upper (D 10) (R 10) [66,132,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3342 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3343 : PairBound 9 := { available := 121, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 67 134 388 296 121 121 121 249 377), lower := (rows 67 134 388 296 16 32 64 128 256), losses := [] }

theorem u3343 : Upper (D 10) (R 10) [66,132,384,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3343 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3344 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 67 134 388 328 57 57 121 185 313), lower := (rows 67 134 388 328 16 32 64 128 256), losses := [] }

theorem u3344 : Upper (D 10) (R 10) [66,132,384,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3344 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3345_5 : Upper (D 10) (R 10) [66,144,72,160,5] 13 :=
  permutation_upper _ _ _ [6,72,80,129,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1540

theorem m3345_33 : Upper (D 10) (R 10) [66,144,72,160,33] 13 :=
  permutation_upper _ _ _ [34,68,129,80,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2077

theorem m3345_36 : Upper (D 10) (R 10) [66,144,72,160,36] 13 :=
  permutation_upper _ _ _ [34,68,160,80,129] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2174

theorem m3345_257 : Upper (D 10) (R 10) [66,144,72,160,257] 13 :=
  permutation_upper _ _ _ [66,132,257,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2436

theorem m3345_260 : Upper (D 10) (R 10) [66,144,72,160,260] 13 :=
  permutation_upper _ _ _ [66,132,264,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2441

theorem m3345_288 : Upper (D 10) (R 10) [66,144,72,160,288] 13 :=
  permutation_upper _ _ _ [66,132,288,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2448

def r3345 : Route 9 := (fun mask => (mask,id))

def c3345 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3345 : Upper (D 10) (R 10) [66,144,72,160] 13 := by
  apply FastRouting.sound _ _ [66,144,72,160] 13 (by decide) (choices 2) [5,33,36,257,260,288] r3345 c3345
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3345_5
  · exact m3345_33
  · exact m3345_36
  · exact m3345_257
  · exact m3345_260
  · exact m3345_288

theorem m3346_5 : Upper (D 10) (R 10) [66,144,72,288,5] 13 :=
  permutation_upper _ _ _ [6,72,80,129,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1541

theorem m3346_33 : Upper (D 10) (R 10) [66,144,72,288,33] 13 :=
  permutation_upper _ _ _ [34,68,129,80,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2079

theorem m3346_36 : Upper (D 10) (R 10) [66,144,72,288,36] 13 :=
  permutation_upper _ _ _ [34,68,160,80,257] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2177

theorem m3346_129 : Upper (D 10) (R 10) [66,144,72,288,129] 13 :=
  permutation_upper _ _ _ [66,68,129,144,288] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2367

theorem m3346_132 : Upper (D 10) (R 10) [66,144,72,288,132] 13 :=
  permutation_upper _ _ _ [66,68,136,288,129] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2374

theorem m3346_160 : Upper (D 10) (R 10) [66,144,72,288,160] 13 :=
  permutation_upper _ _ _ [66,96,129,144,288] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2389

theorem m3346_257 : Upper (D 10) (R 10) [66,144,72,288,257] 13 :=
  permutation_upper _ _ _ [66,132,257,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2437

theorem m3346_260 : Upper (D 10) (R 10) [66,144,72,288,260] 13 :=
  permutation_upper _ _ _ [66,132,96,144,257] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2427

theorem m3346_288 : Upper (D 10) (R 10) [66,144,72,288,288] 13 :=
  permutation_upper _ _ _ [66,132,288,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2449

theorem m3346_384 : Upper (D 10) (R 10) [66,144,72,288,384] 13 :=
  permutation_upper _ _ _ [66,132,384,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2466

def r3346 : Route 9 := (fun mask => (mask,id))

def c3346 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3346 : Upper (D 10) (R 10) [66,144,72,288] 13 := by
  apply FastRouting.sound _ _ [66,144,72,288] 13 (by decide) (choices 2) [5,33,36,129,132,160,257,260,288,384] r3346 c3346
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3346_5
  · exact m3346_33
  · exact m3346_36
  · exact m3346_129
  · exact m3346_132
  · exact m3346_160
  · exact m3346_257
  · exact m3346_260
  · exact m3346_288
  · exact m3346_384

theorem m3347_5 : Upper (D 10) (R 10) [66,144,72,384,5] 13 :=
  permutation_upper _ _ _ [6,72,80,129,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1542

theorem m3347_33 : Upper (D 10) (R 10) [66,144,72,384,33] 13 :=
  permutation_upper _ _ _ [34,68,129,80,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2080

theorem m3347_36 : Upper (D 10) (R 10) [66,144,72,384,36] 13 :=
  permutation_upper _ _ _ [34,68,384,80,129] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2228

theorem m3347_257 : Upper (D 10) (R 10) [66,144,72,384,257] 13 :=
  permutation_upper _ _ _ [66,132,257,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2438

theorem m3347_260 : Upper (D 10) (R 10) [66,144,72,384,260] 13 :=
  permutation_upper _ _ _ [66,132,264,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2442

theorem m3347_288 : Upper (D 10) (R 10) [66,144,72,384,288] 13 :=
  permutation_upper _ _ _ [66,132,288,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2450

def r3347 : Route 9 := (fun mask => (mask,id))

def c3347 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3347 : Upper (D 10) (R 10) [66,144,72,384] 13 := by
  apply FastRouting.sound _ _ [66,144,72,384] 13 (by decide) (choices 2) [5,33,36,257,260,288] r3347 c3347
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3347_5
  · exact m3347_33
  · exact m3347_36
  · exact m3347_257
  · exact m3347_260
  · exact m3347_288

theorem m3348_9 : Upper (D 10) (R 10) [66,144,96,132,9] 13 :=
  permutation_upper _ _ _ [6,72,144,129,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1572

theorem m3348_33 : Upper (D 10) (R 10) [66,144,96,132,33] 13 :=
  permutation_upper _ _ _ [34,68,129,96,136] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2081

theorem m3348_40 : Upper (D 10) (R 10) [66,144,96,132,40] 13 :=
  permutation_upper _ _ _ [34,68,160,65,136] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2170

theorem m3348_257 : Upper (D 10) (R 10) [66,144,96,132,257] 13 :=
  permutation_upper _ _ _ [66,132,257,80,288] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2437

theorem m3348_264 : Upper (D 10) (R 10) [66,144,96,132,264] 13 :=
  permutation_upper _ _ _ [66,132,72,288,257] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2423

theorem m3348_288 : Upper (D 10) (R 10) [66,144,96,132,288] 13 :=
  permutation_upper _ _ _ [66,132,288,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2451

def r3348 : Route 9 := (fun mask => (mask,id))

def c3348 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3348 : Upper (D 10) (R 10) [66,144,96,132] 13 := by
  apply FastRouting.sound _ _ [66,144,96,132] 13 (by decide) (choices 2) [9,33,40,257,264,288] r3348 c3348
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3348_9
  · exact m3348_33
  · exact m3348_40
  · exact m3348_257
  · exact m3348_264
  · exact m3348_288

theorem m3349_5 : Upper (D 10) (R 10) [66,144,96,160,5] 13 :=
  permutation_upper _ _ _ [6,72,96,129,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1549

theorem m3349_9 : Upper (D 10) (R 10) [66,144,96,160,9] 13 :=
  permutation_upper _ _ _ [6,72,160,129,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1614

theorem m3349_12 : Upper (D 10) (R 10) [66,144,96,160,12] 13 :=
  permutation_upper _ _ _ [6,96,160,65,136] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1751

theorem m3349_33 : Upper (D 10) (R 10) [66,144,96,160,33] 13 :=
  permutation_upper _ _ _ [34,68,129,96,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2082

theorem m3349_36 : Upper (D 10) (R 10) [66,144,96,160,36] 13 :=
  permutation_upper _ _ _ [34,96,72,129,160] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2259

theorem m3349_40 : Upper (D 10) (R 10) [66,144,96,160,40] 13 :=
  permutation_upper _ _ _ [34,96,65,132,160] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2252

theorem m3349_257 : Upper (D 10) (R 10) [66,144,96,160,257] 13 :=
  permutation_upper _ _ _ [66,132,257,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2439

theorem m3349_260 : Upper (D 10) (R 10) [66,144,96,160,260] 13 :=
  permutation_upper _ _ _ [66,132,264,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2443

theorem m3349_264 : Upper (D 10) (R 10) [66,144,96,160,264] 13 :=
  permutation_upper _ _ _ [66,132,96,257,288] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2432

theorem m3349_288 : Upper (D 10) (R 10) [66,144,96,160,288] 13 :=
  permutation_upper _ _ _ [66,132,288,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2452

def r3349 : Route 9 := (fun mask => (mask,id))

def c3349 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3349 : Upper (D 10) (R 10) [66,144,96,160] 13 := by
  apply FastRouting.sound _ _ [66,144,96,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r3349 c3349
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3349_5
  · exact m3349_9
  · exact m3349_12
  · exact m3349_33
  · exact m3349_36
  · exact m3349_40
  · exact m3349_257
  · exact m3349_260
  · exact m3349_264
  · exact m3349_288

theorem m3350_9 : Upper (D 10) (R 10) [66,144,96,260,9] 13 :=
  permutation_upper _ _ _ [6,72,144,160,257] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1576

theorem m3350_33 : Upper (D 10) (R 10) [66,144,96,260,33] 13 :=
  permutation_upper _ _ _ [34,68,129,96,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2083

theorem m3350_40 : Upper (D 10) (R 10) [66,144,96,260,40] 13 :=
  permutation_upper _ _ _ [34,68,160,144,257] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2189

theorem m3350_129 : Upper (D 10) (R 10) [66,144,96,260,129] 13 :=
  permutation_upper _ _ _ [66,68,129,160,264] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2368

theorem m3350_136 : Upper (D 10) (R 10) [66,144,96,260,136] 13 :=
  permutation_upper _ _ _ [66,68,136,288,257] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2376

theorem m3350_160 : Upper (D 10) (R 10) [66,144,96,260,160] 13 :=
  permutation_upper _ _ _ [66,96,129,160,264] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2391

theorem m3350_257 : Upper (D 10) (R 10) [66,144,96,260,257] 13 :=
  permutation_upper _ _ _ [66,132,257,80,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2436

theorem m3350_264 : Upper (D 10) (R 10) [66,144,96,260,264] 13 :=
  permutation_upper _ _ _ [66,68,160,144,257] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2380

theorem m3350_288 : Upper (D 10) (R 10) [66,144,96,260,288] 13 :=
  permutation_upper _ _ _ [66,132,288,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2453

theorem m3350_384 : Upper (D 10) (R 10) [66,144,96,260,384] 13 :=
  permutation_upper _ _ _ [66,132,384,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2467

def r3350 : Route 9 := (fun mask => (mask,id))

def c3350 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3350 : Upper (D 10) (R 10) [66,144,96,260] 13 := by
  apply FastRouting.sound _ _ [66,144,96,260] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r3350 c3350
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3350_9
  · exact m3350_33
  · exact m3350_40
  · exact m3350_129
  · exact m3350_136
  · exact m3350_160
  · exact m3350_257
  · exact m3350_264
  · exact m3350_288
  · exact m3350_384

theorem m3351_5 : Upper (D 10) (R 10) [66,144,96,288,5] 13 :=
  permutation_upper _ _ _ [6,72,96,129,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1550

theorem m3351_9 : Upper (D 10) (R 10) [66,144,96,288,9] 13 :=
  permutation_upper _ _ _ [6,72,160,257,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1631

theorem m3351_12 : Upper (D 10) (R 10) [66,144,96,288,12] 13 :=
  permutation_upper _ _ _ [6,96,160,80,257] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1757

theorem m3351_33 : Upper (D 10) (R 10) [66,144,96,288,33] 13 :=
  permutation_upper _ _ _ [34,68,129,96,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2084

theorem m3351_36 : Upper (D 10) (R 10) [66,144,96,288,36] 13 :=
  permutation_upper _ _ _ [34,96,72,129,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2261

theorem m3351_40 : Upper (D 10) (R 10) [66,144,96,288,40] 13 :=
  permutation_upper _ _ _ [34,96,129,260,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2289

theorem m3351_129 : Upper (D 10) (R 10) [66,144,96,288,129] 13 :=
  permutation_upper _ _ _ [66,68,129,160,288] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2369

theorem m3351_132 : Upper (D 10) (R 10) [66,144,96,288,132] 13 :=
  permutation_upper _ _ _ [66,68,160,129,288] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2379

theorem m3351_136 : Upper (D 10) (R 10) [66,144,96,288,136] 13 :=
  permutation_upper _ _ _ [66,68,160,257,288] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2382

theorem m3351_160 : Upper (D 10) (R 10) [66,144,96,288,160] 13 :=
  permutation_upper _ _ _ [66,96,129,160,288] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2392

theorem m3351_257 : Upper (D 10) (R 10) [66,144,96,288,257] 13 :=
  permutation_upper _ _ _ [66,132,257,96,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2439

theorem m3351_260 : Upper (D 10) (R 10) [66,144,96,288,260] 13 :=
  permutation_upper _ _ _ [66,132,264,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2444

theorem m3351_264 : Upper (D 10) (R 10) [66,144,96,288,264] 13 :=
  permutation_upper _ _ _ [66,96,129,260,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2393

theorem m3351_288 : Upper (D 10) (R 10) [66,144,96,288,288] 13 :=
  permutation_upper _ _ _ [66,132,288,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2454

theorem m3351_384 : Upper (D 10) (R 10) [66,144,96,288,384] 13 :=
  permutation_upper _ _ _ [66,132,384,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2468

def r3351 : Route 9 := (fun mask => (mask,id))

def c3351 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3351 : Upper (D 10) (R 10) [66,144,96,288] 13 := by
  apply FastRouting.sound _ _ [66,144,96,288] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160,257,260,264,288,384] r3351 c3351
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3351_5
  · exact m3351_9
  · exact m3351_12
  · exact m3351_33
  · exact m3351_36
  · exact m3351_40
  · exact m3351_129
  · exact m3351_132
  · exact m3351_136
  · exact m3351_160
  · exact m3351_257
  · exact m3351_260
  · exact m3351_264
  · exact m3351_288
  · exact m3351_384

theorem m3352_5 : Upper (D 10) (R 10) [66,144,96,384,5] 13 :=
  permutation_upper _ _ _ [6,72,96,129,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1551

theorem m3352_9 : Upper (D 10) (R 10) [66,144,96,384,9] 13 :=
  permutation_upper _ _ _ [6,72,384,129,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1710

theorem m3352_12 : Upper (D 10) (R 10) [66,144,96,384,12] 13 :=
  permutation_upper _ _ _ [6,96,384,80,129] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1814

theorem m3352_33 : Upper (D 10) (R 10) [66,144,96,384,33] 13 :=
  permutation_upper _ _ _ [34,68,129,96,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2085

theorem m3352_36 : Upper (D 10) (R 10) [66,144,96,384,36] 13 :=
  permutation_upper _ _ _ [34,96,72,129,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2262

theorem m3352_40 : Upper (D 10) (R 10) [66,144,96,384,40] 13 :=
  permutation_upper _ _ _ [34,192,65,260,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2316

theorem m3352_257 : Upper (D 10) (R 10) [66,144,96,384,257] 13 :=
  permutation_upper _ _ _ [66,132,257,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2440

theorem m3352_260 : Upper (D 10) (R 10) [66,144,96,384,260] 13 :=
  permutation_upper _ _ _ [66,132,264,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2445

theorem m3352_264 : Upper (D 10) (R 10) [66,144,96,384,264] 13 :=
  permutation_upper _ _ _ [66,132,192,257,288] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2435

theorem m3352_288 : Upper (D 10) (R 10) [66,144,96,384,288] 13 :=
  permutation_upper _ _ _ [66,132,288,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2455

def r3352 : Route 9 := (fun mask => (mask,id))

def c3352 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3352 : Upper (D 10) (R 10) [66,144,96,384] 13 := by
  apply FastRouting.sound _ _ [66,144,96,384] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r3352 c3352
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3352_5
  · exact m3352_9
  · exact m3352_12
  · exact m3352_33
  · exact m3352_36
  · exact m3352_40
  · exact m3352_257
  · exact m3352_260
  · exact m3352_264
  · exact m3352_288

theorem m3353_5 : Upper (D 10) (R 10) [66,144,136,288,5] 13 :=
  permutation_upper _ _ _ [6,72,144,129,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1573

theorem m3353_33 : Upper (D 10) (R 10) [66,144,136,288,33] 13 :=
  permutation_upper _ _ _ [34,68,129,144,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2087

theorem m3353_36 : Upper (D 10) (R 10) [66,144,136,288,36] 13 :=
  permutation_upper _ _ _ [34,68,160,65,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2171

theorem m3353_65 : Upper (D 10) (R 10) [66,144,136,288,65] 13 :=
  permutation_upper _ _ _ [66,68,129,144,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2367

theorem m3353_68 : Upper (D 10) (R 10) [66,144,136,288,68] 13 :=
  permutation_upper _ _ _ [66,132,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2416

theorem m3353_96 : Upper (D 10) (R 10) [66,144,136,288,96] 13 :=
  permutation_upper _ _ _ [66,132,96,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2428

theorem m3353_257 : Upper (D 10) (R 10) [66,144,136,288,257] 13 :=
  permutation_upper _ _ _ [66,132,257,80,160] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2436

theorem m3353_260 : Upper (D 10) (R 10) [66,144,136,288,260] 13 :=
  permutation_upper _ _ _ [66,132,72,160,257] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2417

theorem m3353_288 : Upper (D 10) (R 10) [66,144,136,288,288] 13 :=
  permutation_upper _ _ _ [66,132,288,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2456

theorem m3353_320 : Upper (D 10) (R 10) [66,144,136,288,320] 13 :=
  permutation_upper _ _ _ [66,132,320,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2463

def r3353 : Route 9 := (fun mask => (mask,id))

def c3353 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3353 : Upper (D 10) (R 10) [66,144,136,288] 13 := by
  apply FastRouting.sound _ _ [66,144,136,288] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r3353 c3353
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3353_5
  · exact m3353_33
  · exact m3353_36
  · exact m3353_65
  · exact m3353_68
  · exact m3353_96
  · exact m3353_257
  · exact m3353_260
  · exact m3353_288
  · exact m3353_320

theorem m3354_5 : Upper (D 10) (R 10) [66,144,136,320,5] 13 :=
  permutation_upper _ _ _ [6,72,144,129,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1574

theorem m3354_33 : Upper (D 10) (R 10) [66,144,136,320,33] 13 :=
  permutation_upper _ _ _ [34,68,129,144,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2088

theorem m3354_36 : Upper (D 10) (R 10) [66,144,136,320,36] 13 :=
  permutation_upper _ _ _ [34,68,384,65,136] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2226

theorem m3354_257 : Upper (D 10) (R 10) [66,144,136,320,257] 13 :=
  permutation_upper _ _ _ [66,132,257,80,384] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2438

theorem m3354_260 : Upper (D 10) (R 10) [66,144,136,320,260] 13 :=
  permutation_upper _ _ _ [66,132,72,384,257] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2425

theorem m3354_288 : Upper (D 10) (R 10) [66,144,136,320,288] 13 :=
  permutation_upper _ _ _ [66,132,288,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2457

def r3354 : Route 9 := (fun mask => (mask,id))

def c3354 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3354 : Upper (D 10) (R 10) [66,144,136,320] 13 := by
  apply FastRouting.sound _ _ [66,144,136,320] 13 (by decide) (choices 2) [5,33,36,257,260,288] r3354 c3354
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3354_5
  · exact m3354_33
  · exact m3354_36
  · exact m3354_257
  · exact m3354_260
  · exact m3354_288

theorem m3355_9 : Upper (D 10) (R 10) [66,144,160,260,9] 13 :=
  permutation_upper _ _ _ [6,72,144,257,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1581

theorem m3355_33 : Upper (D 10) (R 10) [66,144,160,260,33] 13 :=
  permutation_upper _ _ _ [34,68,129,160,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2089

theorem m3355_40 : Upper (D 10) (R 10) [66,144,160,260,40] 13 :=
  permutation_upper _ _ _ [34,68,160,129,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2186

theorem m3355_65 : Upper (D 10) (R 10) [66,144,160,260,65] 13 :=
  permutation_upper _ _ _ [66,68,129,160,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2368

theorem m3355_72 : Upper (D 10) (R 10) [66,144,160,260,72] 13 :=
  permutation_upper _ _ _ [66,132,72,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2421

theorem m3355_96 : Upper (D 10) (R 10) [66,144,160,260,96] 13 :=
  permutation_upper _ _ _ [66,132,96,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2430

theorem m3355_257 : Upper (D 10) (R 10) [66,144,160,260,257] 13 :=
  permutation_upper _ _ _ [66,132,257,80,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2437

theorem m3355_264 : Upper (D 10) (R 10) [66,144,160,260,264] 13 :=
  permutation_upper _ _ _ [66,68,160,129,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2378

theorem m3355_288 : Upper (D 10) (R 10) [66,144,160,260,288] 13 :=
  permutation_upper _ _ _ [66,132,288,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2458

theorem m3355_320 : Upper (D 10) (R 10) [66,144,160,260,320] 13 :=
  permutation_upper _ _ _ [66,132,320,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2464

def r3355 : Route 9 := (fun mask => (mask,id))

def c3355 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3355 : Upper (D 10) (R 10) [66,144,160,260] 13 := by
  apply FastRouting.sound _ _ [66,144,160,260] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r3355 c3355
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3355_9
  · exact m3355_33
  · exact m3355_40
  · exact m3355_65
  · exact m3355_72
  · exact m3355_96
  · exact m3355_257
  · exact m3355_264
  · exact m3355_288
  · exact m3355_320

theorem m3356_5 : Upper (D 10) (R 10) [66,144,160,288,5] 13 :=
  permutation_upper _ _ _ [6,72,160,129,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1615

theorem m3356_9 : Upper (D 10) (R 10) [66,144,160,288,9] 13 :=
  permutation_upper _ _ _ [6,72,160,257,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1634

theorem m3356_12 : Upper (D 10) (R 10) [66,144,160,288,12] 13 :=
  permutation_upper _ _ _ [6,96,160,65,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1752

theorem m3356_33 : Upper (D 10) (R 10) [66,144,160,288,33] 13 :=
  permutation_upper _ _ _ [34,68,129,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2090

theorem m3356_36 : Upper (D 10) (R 10) [66,144,160,288,36] 13 :=
  permutation_upper _ _ _ [34,96,65,132,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2254

theorem m3356_40 : Upper (D 10) (R 10) [66,144,160,288,40] 13 :=
  permutation_upper _ _ _ [34,96,129,160,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2283

theorem m3356_65 : Upper (D 10) (R 10) [66,144,160,288,65] 13 :=
  permutation_upper _ _ _ [66,68,129,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2369

theorem m3356_68 : Upper (D 10) (R 10) [66,144,160,288,68] 13 :=
  permutation_upper _ _ _ [66,132,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2418

theorem m3356_72 : Upper (D 10) (R 10) [66,144,160,288,72] 13 :=
  permutation_upper _ _ _ [66,132,72,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2422

theorem m3356_96 : Upper (D 10) (R 10) [66,144,160,288,96] 13 :=
  permutation_upper _ _ _ [66,132,96,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2431

theorem m3356_257 : Upper (D 10) (R 10) [66,144,160,288,257] 13 :=
  permutation_upper _ _ _ [66,132,257,96,160] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2439

theorem m3356_260 : Upper (D 10) (R 10) [66,144,160,288,260] 13 :=
  permutation_upper _ _ _ [66,132,96,160,257] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2429

theorem m3356_264 : Upper (D 10) (R 10) [66,144,160,288,264] 13 :=
  permutation_upper _ _ _ [66,96,129,160,260] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2390

theorem m3356_288 : Upper (D 10) (R 10) [66,144,160,288,288] 13 :=
  permutation_upper _ _ _ [66,132,288,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2459

theorem m3356_320 : Upper (D 10) (R 10) [66,144,160,288,320] 13 :=
  permutation_upper _ _ _ [66,132,320,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2465

def r3356 : Route 9 := (fun mask => (mask,id))

def c3356 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3356 : Upper (D 10) (R 10) [66,144,160,288] 13 := by
  apply FastRouting.sound _ _ [66,144,160,288] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,257,260,264,288,320] r3356 c3356
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3356_5
  · exact m3356_9
  · exact m3356_12
  · exact m3356_33
  · exact m3356_36
  · exact m3356_40
  · exact m3356_65
  · exact m3356_68
  · exact m3356_72
  · exact m3356_96
  · exact m3356_257
  · exact m3356_260
  · exact m3356_264
  · exact m3356_288
  · exact m3356_320

theorem m3357_5 : Upper (D 10) (R 10) [66,144,160,320,5] 13 :=
  permutation_upper _ _ _ [6,72,160,129,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1616

theorem m3357_9 : Upper (D 10) (R 10) [66,144,160,320,9] 13 :=
  permutation_upper _ _ _ [6,72,192,257,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1681

theorem m3357_12 : Upper (D 10) (R 10) [66,144,160,320,12] 13 :=
  permutation_upper _ _ _ [6,96,384,65,136] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1812

theorem m3357_33 : Upper (D 10) (R 10) [66,144,160,320,33] 13 :=
  permutation_upper _ _ _ [34,68,129,160,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2091

theorem m3357_36 : Upper (D 10) (R 10) [66,144,160,320,36] 13 :=
  permutation_upper _ _ _ [34,96,65,132,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2255

theorem m3357_40 : Upper (D 10) (R 10) [66,144,160,320,40] 13 :=
  permutation_upper _ _ _ [34,192,72,257,288] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2329

theorem m3357_257 : Upper (D 10) (R 10) [66,144,160,320,257] 13 :=
  permutation_upper _ _ _ [66,132,257,96,384] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2440

theorem m3357_260 : Upper (D 10) (R 10) [66,144,160,320,260] 13 :=
  permutation_upper _ _ _ [66,132,96,257,384] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2433

theorem m3357_264 : Upper (D 10) (R 10) [66,144,160,320,264] 13 :=
  permutation_upper _ _ _ [66,132,264,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2447

theorem m3357_288 : Upper (D 10) (R 10) [66,144,160,320,288] 13 :=
  permutation_upper _ _ _ [66,132,288,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2460

def r3357 : Route 9 := (fun mask => (mask,id))

def c3357 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3357 : Upper (D 10) (R 10) [66,144,160,320] 13 := by
  apply FastRouting.sound _ _ [66,144,160,320] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r3357 c3357
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3357_5
  · exact m3357_9
  · exact m3357_12
  · exact m3357_33
  · exact m3357_36
  · exact m3357_40
  · exact m3357_257
  · exact m3357_260
  · exact m3357_264
  · exact m3357_288

theorem m3358_9 : Upper (D 10) (R 10) [66,144,192,260,9] 13 :=
  permutation_upper _ _ _ [6,72,144,257,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1582

theorem m3358_33 : Upper (D 10) (R 10) [66,144,192,260,33] 13 :=
  permutation_upper _ _ _ [34,68,129,192,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2092

theorem m3358_40 : Upper (D 10) (R 10) [66,144,192,260,40] 13 :=
  permutation_upper _ _ _ [34,68,384,129,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2236

theorem m3358_257 : Upper (D 10) (R 10) [66,144,192,260,257] 13 :=
  permutation_upper _ _ _ [66,132,257,80,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2438

theorem m3358_264 : Upper (D 10) (R 10) [66,144,192,260,264] 13 :=
  permutation_upper _ _ _ [66,68,384,129,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2385

theorem m3358_288 : Upper (D 10) (R 10) [66,144,192,260,288] 13 :=
  permutation_upper _ _ _ [66,132,288,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2461

def r3358 : Route 9 := (fun mask => (mask,id))

def c3358 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3358 : Upper (D 10) (R 10) [66,144,192,260] 13 := by
  apply FastRouting.sound _ _ [66,144,192,260] 13 (by decide) (choices 2) [9,33,40,257,264,288] r3358 c3358
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3358_9
  · exact m3358_33
  · exact m3358_40
  · exact m3358_257
  · exact m3358_264
  · exact m3358_288

theorem m3359_5 : Upper (D 10) (R 10) [66,144,192,288,5] 13 :=
  permutation_upper _ _ _ [6,72,192,129,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1673

theorem m3359_9 : Upper (D 10) (R 10) [66,144,192,288,9] 13 :=
  permutation_upper _ _ _ [6,72,160,257,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1635

theorem m3359_12 : Upper (D 10) (R 10) [66,144,192,288,12] 13 :=
  permutation_upper _ _ _ [6,96,384,129,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1820

theorem m3359_33 : Upper (D 10) (R 10) [66,144,192,288,33] 13 :=
  permutation_upper _ _ _ [34,68,129,192,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2093

theorem m3359_36 : Upper (D 10) (R 10) [66,144,192,288,36] 13 :=
  permutation_upper _ _ _ [34,192,65,132,288] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2309

theorem m3359_40 : Upper (D 10) (R 10) [66,144,192,288,40] 13 :=
  permutation_upper _ _ _ [34,96,129,260,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2291

theorem m3359_257 : Upper (D 10) (R 10) [66,144,192,288,257] 13 :=
  permutation_upper _ _ _ [66,132,257,96,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2440

theorem m3359_260 : Upper (D 10) (R 10) [66,144,192,288,260] 13 :=
  permutation_upper _ _ _ [66,132,264,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2446

theorem m3359_264 : Upper (D 10) (R 10) [66,144,192,288,264] 13 :=
  permutation_upper _ _ _ [66,96,129,260,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2394

theorem m3359_288 : Upper (D 10) (R 10) [66,144,192,288,288] 13 :=
  permutation_upper _ _ _ [66,132,288,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2462

def r3359 : Route 9 := (fun mask => (mask,id))

def c3359 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3359 : Upper (D 10) (R 10) [66,144,192,288] 13 := by
  apply FastRouting.sound _ _ [66,144,192,288] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r3359 c3359
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3359_5
  · exact m3359_9
  · exact m3359_12
  · exact m3359_33
  · exact m3359_36
  · exact m3359_40
  · exact m3359_257
  · exact m3359_260
  · exact m3359_264
  · exact m3359_288

#print axioms u3359
end Delivery.IrregularNine14.P10
