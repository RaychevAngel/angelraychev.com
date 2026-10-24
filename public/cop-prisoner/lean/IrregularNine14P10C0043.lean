import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0019
import IrregularNine14P10C0021
import IrregularNine14P10C0022
import IrregularNine14P10C0023
import IrregularNine14P10C0024

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2580 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2580 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2580 : Upper (D 10) (R 10) [6,40,96,80] 13 := by
  apply FastRouting.sound _ _ [6,40,96,80] 13 (by decide) (choices 2) [33,129,160,384] r2580 c2580
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1352
  · exact u1353
  · exact u1354
  · exact u1355

def b2581 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 11, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 100 104 401 433 465 401 401), lower := (rows 7 42 100 104 16 32 64 128 256), losses := [] }

theorem u2581 : Upper (D 10) (R 10) [6,40,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2581 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2582 : Route 9 := (fun mask => (mask,id))

def c2582 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2582 : Upper (D 10) (R 10) [6,40,96,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2582 c2582
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1358
  · exact u1359
  · exact u1360
  · exact u1361
  · exact u1362
  · exact u1363

def r2583 : Route 9 := (fun mask => (mask,id))

def c2583 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2583 : Upper (D 10) (R 10) [6,40,96,144] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r2583 c2583
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1364
  · exact u1365
  · exact u1366
  · exact u1367
  · exact u1368
  · exact u1369
  · exact u1370
  · exact u1371
  · exact u1372
  · exact u1373

def b2584 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 100 168 465 497 465 465 465), lower := (rows 7 42 100 168 16 32 64 128 256), losses := [] }

theorem u2584 : Upper (D 10) (R 10) [6,40,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2584 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2585 : Route 9 := (fun mask => (mask,id))

def c2585 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2585 : Upper (D 10) (R 10) [6,40,96,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192] 13 (by decide) (choices 2) [33,129,160,257,288,384] r2585 c2585
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1379
  · exact u1380
  · exact u1381
  · exact u1382
  · exact u1383
  · exact u1384

def r2586 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2586 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2586 : Upper (D 10) (R 10) [6,40,96,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r2586 c2586
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1385
  · exact u1386
  · exact u1387
  · exact u1388
  · exact u1389
  · exact u1390
  · exact u1391

theorem m2587_96 : Upper (D 10) (R 10) [6,40,192,17,96] 13 :=
  permutation_upper _ _ _ [6,24,96,33,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1169

theorem m2587_192 : Upper (D 10) (R 10) [6,40,192,17,192] 13 :=
  permutation_upper _ _ _ [6,24,192,33,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1189

theorem m2587_288 : Upper (D 10) (R 10) [6,40,192,17,288] 13 :=
  permutation_upper _ _ _ [6,24,96,33,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1170

theorem m2587_320 : Upper (D 10) (R 10) [6,40,192,17,320] 13 :=
  permutation_upper _ _ _ [6,24,192,33,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1191

def r2587 : Route 9 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2587 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2587 : Upper (D 10) (R 10) [6,40,192,17] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17] 13 (by decide) (choices 2) [96,192,288,320] r2587 c2587
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2587_96
  · exact m2587_192
  · exact m2587_288
  · exact m2587_320

def b2588 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 41 496 496 496 496 496), lower := (rows 7 42 196 41 16 32 64 128 256), losses := [] }

theorem u2588 : Upper (D 10) (R 10) [6,40,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2588 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2589 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 56 497 481 481 481 481), lower := (rows 7 42 196 56 16 32 64 128 256), losses := [] }

theorem u2589 : Upper (D 10) (R 10) [6,40,192,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2589 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2590 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 196 73 432 432 496 432 432), lower := (rows 7 42 196 73 16 32 64 128 256), losses := [] }

theorem u2590 : Upper (D 10) (R 10) [6,40,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2590 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2591 : Route 9 := (fun mask => (mask,id))

def c2591 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2591 : Upper (D 10) (R 10) [6,40,192,80] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80] 13 (by decide) (choices 2) [33,129,160,257,288,384] r2591 c2591
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1403
  · exact u1404
  · exact u1405
  · exact u1406
  · exact u1407
  · exact u1408

def b2592 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 104 433 433 497 433 433), lower := (rows 7 42 196 104 16 32 64 128 256), losses := [] }

theorem u2592 : Upper (D 10) (R 10) [6,40,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2592 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2593 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 8, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 7 42 196 200 305 305 369 433 305), lower := (rows 7 42 196 200 16 32 64 128 256), losses := [] }

theorem u2593 : Upper (D 10) (R 10) [6,40,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2593 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2594 : Route 9 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2594 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2594 : Upper (D 10) (R 10) [6,40,192,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257] 13 (by decide) (choices 2) [96,192,288,320] r2594 c2594
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1417
  · exact u1418
  · exact u1419
  · exact u1420

def r2595 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2595 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2595 : Upper (D 10) (R 10) [6,40,192,272] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r2595 c2595
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1421
  · exact u1422
  · exact u1423
  · exact u1424
  · exact u1425
  · exact u1426
  · exact u1427

def b2596 : PairBound 9 := { available := 497, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 296 497 497 497 497 497), lower := (rows 7 42 196 296 16 32 64 128 256), losses := [] }

theorem u2596 : Upper (D 10) (R 10) [6,40,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2596 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2597 : Route 9 := (fun mask => (mask,id))

def c2597 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2597 : Upper (D 10) (R 10) [6,40,192,320] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320] 13 (by decide) (choices 2) [33,129,160,257,288,384] r2597 c2597
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1433
  · exact u1434
  · exact u1435
  · exact u1436
  · exact u1437
  · exact u1438

def b2598 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 402, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 50 69 104 440 424 488 424 424), lower := (rows 7 50 69 104 16 32 64 128 256), losses := [] }

theorem u2598 : Upper (D 10) (R 10) [6,48,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2598 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2599_40 : Upper (D 10) (R 10) [6,48,65,160,40] 13 :=
  permutation_upper _ _ _ [6,40,65,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1290

theorem m2599_72 : Upper (D 10) (R 10) [6,48,65,160,72] 13 :=
  permutation_upper _ _ _ [6,40,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1292

theorem m2599_96 : Upper (D 10) (R 10) [6,48,65,160,96] 13 :=
  permutation_upper _ _ _ [6,40,65,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1294

theorem m2599_136 : Upper (D 10) (R 10) [6,48,65,160,136] 13 :=
  permutation_upper _ _ _ [6,40,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1297

theorem m2599_160 : Upper (D 10) (R 10) [6,48,65,160,160] 13 :=
  permutation_upper _ _ _ [6,40,65,160,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1302

theorem m2599_192 : Upper (D 10) (R 10) [6,48,65,160,192] 13 :=
  permutation_upper _ _ _ [6,40,65,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1305

theorem m2599_264 : Upper (D 10) (R 10) [6,48,65,160,264] 13 :=
  permutation_upper _ _ _ [6,40,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1299

theorem m2599_288 : Upper (D 10) (R 10) [6,48,65,160,288] 13 :=
  permutation_upper _ _ _ [6,40,65,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1303

theorem m2599_320 : Upper (D 10) (R 10) [6,48,65,160,320] 13 :=
  permutation_upper _ _ _ [6,40,65,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1306

theorem m2599_384 : Upper (D 10) (R 10) [6,48,65,160,384] 13 :=
  permutation_upper _ _ _ [6,40,65,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1309

def r2599 : Route 9 := (fun mask => (mask,id))

def c2599 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2599 : Upper (D 10) (R 10) [6,48,65,160] 13 := by
  apply FastRouting.sound _ _ [6,48,65,160] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2599 c2599
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2599_40
  · exact m2599_72
  · exact m2599_96
  · exact m2599_136
  · exact m2599_160
  · exact m2599_192
  · exact m2599_264
  · exact m2599_288
  · exact m2599_320
  · exact m2599_384

def b2600 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 306, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 50 69 200 440 424 488 424 424), lower := (rows 7 50 69 200 16 32 64 128 256), losses := [] }

theorem u2600 : Upper (D 10) (R 10) [6,48,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2600 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2601_40 : Upper (D 10) (R 10) [6,48,65,384,40] 13 :=
  permutation_upper _ _ _ [6,40,65,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1291

theorem m2601_72 : Upper (D 10) (R 10) [6,48,65,384,72] 13 :=
  permutation_upper _ _ _ [6,40,65,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1293

theorem m2601_96 : Upper (D 10) (R 10) [6,48,65,384,96] 13 :=
  permutation_upper _ _ _ [6,40,65,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1295

theorem m2601_136 : Upper (D 10) (R 10) [6,48,65,384,136] 13 :=
  permutation_upper _ _ _ [6,40,65,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1301

theorem m2601_160 : Upper (D 10) (R 10) [6,48,65,384,160] 13 :=
  permutation_upper _ _ _ [6,40,65,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1304

theorem m2601_192 : Upper (D 10) (R 10) [6,48,65,384,192] 13 :=
  permutation_upper _ _ _ [6,40,65,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1307

theorem m2601_384 : Upper (D 10) (R 10) [6,48,65,384,384] 13 :=
  permutation_upper _ _ _ [6,40,65,384,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1311

def r2601 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2601 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2601 : Upper (D 10) (R 10) [6,48,65,384] 13 := by
  apply FastRouting.sound _ _ [6,48,65,384] 13 (by decide) (choices 2) [40,72,96,136,160,192,384] r2601 c2601
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2601_40
  · exact m2601_72
  · exact m2601_96
  · exact m2601_136
  · exact m2601_160
  · exact m2601_192
  · exact m2601_384

theorem m2602_96 : Upper (D 10) (R 10) [6,48,72,33,96] 13 :=
  permutation_upper _ _ _ [6,40,80,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1316

theorem m2602_160 : Upper (D 10) (R 10) [6,48,72,33,160] 13 :=
  permutation_upper _ _ _ [6,40,80,160,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1326

theorem m2602_192 : Upper (D 10) (R 10) [6,48,72,33,192] 13 :=
  permutation_upper _ _ _ [6,40,80,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1332

theorem m2602_384 : Upper (D 10) (R 10) [6,48,72,33,384] 13 :=
  permutation_upper _ _ _ [6,40,80,384,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1338

def r2602 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2602 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2602 : Upper (D 10) (R 10) [6,48,72,33] 13 := by
  apply FastRouting.sound _ _ [6,48,72,33] 13 (by decide) (choices 2) [96,160,192,384] r2602 c2602
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2602_96
  · exact m2602_160
  · exact m2602_192
  · exact m2602_384

def b2603 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 50 76 73 432 416 480 416 416), lower := (rows 7 50 76 73 16 32 64 128 256), losses := [] }

theorem u2603 : Upper (D 10) (R 10) [6,48,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2603 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2604 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 50 76 104 433 417 481 417 417), lower := (rows 7 50 76 104 16 32 64 128 256), losses := [] }

theorem u2604 : Upper (D 10) (R 10) [6,48,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2604 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2605_96 : Upper (D 10) (R 10) [6,48,72,129,96] 13 :=
  permutation_upper _ _ _ [6,40,80,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1317

theorem m2605_160 : Upper (D 10) (R 10) [6,48,72,129,160] 13 :=
  permutation_upper _ _ _ [6,40,80,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1327

theorem m2605_192 : Upper (D 10) (R 10) [6,48,72,129,192] 13 :=
  permutation_upper _ _ _ [6,40,80,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1333

theorem m2605_288 : Upper (D 10) (R 10) [6,48,72,129,288] 13 :=
  permutation_upper _ _ _ [6,40,80,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1329

theorem m2605_320 : Upper (D 10) (R 10) [6,48,72,129,320] 13 :=
  permutation_upper _ _ _ [6,40,80,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1335

theorem m2605_384 : Upper (D 10) (R 10) [6,48,72,129,384] 13 :=
  permutation_upper _ _ _ [6,40,80,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1341

def r2605 : Route 9 := (fun mask => (mask,id))

def c2605 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2605 : Upper (D 10) (R 10) [6,48,72,129] 13 := by
  apply FastRouting.sound _ _ [6,48,72,129] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2605 c2605
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2605_96
  · exact m2605_160
  · exact m2605_192
  · exact m2605_288
  · exact m2605_320
  · exact m2605_384

theorem m2606_33 : Upper (D 10) (R 10) [6,48,72,160,33] 13 :=
  permutation_upper _ _ _ [6,40,80,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1312

theorem m2606_65 : Upper (D 10) (R 10) [6,48,72,160,65] 13 :=
  permutation_upper _ _ _ [6,40,80,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1314

theorem m2606_96 : Upper (D 10) (R 10) [6,48,72,160,96] 13 :=
  permutation_upper _ _ _ [6,40,80,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1318

theorem m2606_129 : Upper (D 10) (R 10) [6,48,72,160,129] 13 :=
  permutation_upper _ _ _ [6,40,80,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1321

theorem m2606_160 : Upper (D 10) (R 10) [6,48,72,160,160] 13 :=
  permutation_upper _ _ _ [6,40,80,160,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1328

theorem m2606_192 : Upper (D 10) (R 10) [6,48,72,160,192] 13 :=
  permutation_upper _ _ _ [6,40,80,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1334

theorem m2606_257 : Upper (D 10) (R 10) [6,48,72,160,257] 13 :=
  permutation_upper _ _ _ [6,40,80,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1323

theorem m2606_288 : Upper (D 10) (R 10) [6,48,72,160,288] 13 :=
  permutation_upper _ _ _ [6,40,80,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1330

theorem m2606_320 : Upper (D 10) (R 10) [6,48,72,160,320] 13 :=
  permutation_upper _ _ _ [6,40,80,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1336

theorem m2606_384 : Upper (D 10) (R 10) [6,48,72,160,384] 13 :=
  permutation_upper _ _ _ [6,40,80,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1342

def r2606 : Route 9 := (fun mask => (mask,id))

def c2606 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2606 : Upper (D 10) (R 10) [6,48,72,160] 13 := by
  apply FastRouting.sound _ _ [6,48,72,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r2606 c2606
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2606_33
  · exact m2606_65
  · exact m2606_96
  · exact m2606_129
  · exact m2606_160
  · exact m2606_192
  · exact m2606_257
  · exact m2606_288
  · exact m2606_320
  · exact m2606_384

def b2607 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 50 76 200 433 417 481 417 417), lower := (rows 7 50 76 200 16 32 64 128 256), losses := [] }

theorem u2607 : Upper (D 10) (R 10) [6,48,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2607 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2608_33 : Upper (D 10) (R 10) [6,48,72,384,33] 13 :=
  permutation_upper _ _ _ [6,40,80,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1313

theorem m2608_65 : Upper (D 10) (R 10) [6,48,72,384,65] 13 :=
  permutation_upper _ _ _ [6,40,80,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1315

theorem m2608_96 : Upper (D 10) (R 10) [6,48,72,384,96] 13 :=
  permutation_upper _ _ _ [6,40,80,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1319

theorem m2608_129 : Upper (D 10) (R 10) [6,48,72,384,129] 13 :=
  permutation_upper _ _ _ [6,40,80,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1325

theorem m2608_160 : Upper (D 10) (R 10) [6,48,72,384,160] 13 :=
  permutation_upper _ _ _ [6,40,80,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1331

theorem m2608_192 : Upper (D 10) (R 10) [6,48,72,384,192] 13 :=
  permutation_upper _ _ _ [6,40,80,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1337

theorem m2608_384 : Upper (D 10) (R 10) [6,48,72,384,384] 13 :=
  permutation_upper _ _ _ [6,40,80,384,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1344

def r2608 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2608 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2608 : Upper (D 10) (R 10) [6,48,72,384] 13 := by
  apply FastRouting.sound _ _ [6,48,72,384] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r2608 c2608
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2608_33
  · exact m2608_65
  · exact m2608_96
  · exact m2608_129
  · exact m2608_160
  · exact m2608_192
  · exact m2608_384

theorem m2609_72 : Upper (D 10) (R 10) [6,48,96,33,72] 13 :=
  permutation_upper _ _ _ [6,40,96,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1352

theorem m2609_136 : Upper (D 10) (R 10) [6,48,96,33,136] 13 :=
  permutation_upper _ _ _ [6,40,96,144,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1364

theorem m2609_192 : Upper (D 10) (R 10) [6,48,96,33,192] 13 :=
  permutation_upper _ _ _ [6,40,96,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1379

theorem m2609_384 : Upper (D 10) (R 10) [6,48,96,33,384] 13 :=
  permutation_upper _ _ _ [6,40,96,384,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1385

def r2609 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2609 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u2609 : Upper (D 10) (R 10) [6,48,96,33] 13 := by
  apply FastRouting.sound _ _ [6,48,96,33] 13 (by decide) (choices 2) [72,136,192,384] r2609 c2609
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2609_72
  · exact m2609_136
  · exact m2609_192
  · exact m2609_384

def b2610 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 50 100 73 440 424 488 424 424), lower := (rows 7 50 100 73 16 32 64 128 256), losses := [] }

theorem u2610 : Upper (D 10) (R 10) [6,48,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2610 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2611 : PairBound 9 := { available := 393, camps := [{ cop := 2, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 50 100 104 409 425 457 393 393), lower := (rows 7 50 100 104 16 32 64 128 256), losses := [] }

theorem u2611 : Upper (D 10) (R 10) [6,48,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2611 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2612_40 : Upper (D 10) (R 10) [6,48,96,129,40] 13 :=
  permutation_upper _ _ _ [6,40,96,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1347

theorem m2612_72 : Upper (D 10) (R 10) [6,48,96,129,72] 13 :=
  permutation_upper _ _ _ [6,40,96,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1353

theorem m2612_96 : Upper (D 10) (R 10) [6,48,96,129,96] 13 :=
  permutation_upper _ _ _ [6,40,96,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1356

theorem m2612_136 : Upper (D 10) (R 10) [6,48,96,129,136] 13 :=
  permutation_upper _ _ _ [6,40,96,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1367

theorem m2612_160 : Upper (D 10) (R 10) [6,48,96,129,160] 13 :=
  permutation_upper _ _ _ [6,40,96,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1374

theorem m2612_192 : Upper (D 10) (R 10) [6,48,96,129,192] 13 :=
  permutation_upper _ _ _ [6,40,96,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1380

theorem m2612_264 : Upper (D 10) (R 10) [6,48,96,129,264] 13 :=
  permutation_upper _ _ _ [6,40,96,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1370

theorem m2612_288 : Upper (D 10) (R 10) [6,48,96,129,288] 13 :=
  permutation_upper _ _ _ [6,40,96,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1376

theorem m2612_320 : Upper (D 10) (R 10) [6,48,96,129,320] 13 :=
  permutation_upper _ _ _ [6,40,96,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1382

theorem m2612_384 : Upper (D 10) (R 10) [6,48,96,129,384] 13 :=
  permutation_upper _ _ _ [6,40,96,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1388

def r2612 : Route 9 := (fun mask => (mask,id))

def c2612 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2612 : Upper (D 10) (R 10) [6,48,96,129] 13 := by
  apply FastRouting.sound _ _ [6,48,96,129] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2612 c2612
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2612_40
  · exact m2612_72
  · exact m2612_96
  · exact m2612_136
  · exact m2612_160
  · exact m2612_192
  · exact m2612_264
  · exact m2612_288
  · exact m2612_320
  · exact m2612_384

theorem m2613_9 : Upper (D 10) (R 10) [6,48,96,160,9] 13 :=
  permutation_upper _ _ _ [6,24,96,33,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1168

theorem m2613_65 : Upper (D 10) (R 10) [6,48,96,160,65] 13 :=
  permutation_upper _ _ _ [6,40,96,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1350

theorem m2613_72 : Upper (D 10) (R 10) [6,48,96,160,72] 13 :=
  permutation_upper _ _ _ [6,40,96,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1354

theorem m2613_129 : Upper (D 10) (R 10) [6,48,96,160,129] 13 :=
  permutation_upper _ _ _ [6,40,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1359

theorem m2613_136 : Upper (D 10) (R 10) [6,48,96,160,136] 13 :=
  permutation_upper _ _ _ [6,40,96,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1368

theorem m2613_192 : Upper (D 10) (R 10) [6,48,96,160,192] 13 :=
  permutation_upper _ _ _ [6,40,96,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1381

theorem m2613_257 : Upper (D 10) (R 10) [6,48,96,160,257] 13 :=
  permutation_upper _ _ _ [6,40,96,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1361

theorem m2613_264 : Upper (D 10) (R 10) [6,48,96,160,264] 13 :=
  permutation_upper _ _ _ [6,40,96,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1371

theorem m2613_320 : Upper (D 10) (R 10) [6,48,96,160,320] 13 :=
  permutation_upper _ _ _ [6,40,96,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1383

theorem m2613_384 : Upper (D 10) (R 10) [6,48,96,160,384] 13 :=
  permutation_upper _ _ _ [6,40,96,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1389

def r2613 : Route 9 := (fun mask => (mask,id))

def c2613 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u2613 : Upper (D 10) (R 10) [6,48,96,160] 13 := by
  apply FastRouting.sound _ _ [6,48,96,160] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r2613 c2613
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2613_9
  · exact m2613_65
  · exact m2613_72
  · exact m2613_129
  · exact m2613_136
  · exact m2613_192
  · exact m2613_257
  · exact m2613_264
  · exact m2613_320
  · exact m2613_384

theorem m2614_9 : Upper (D 10) (R 10) [6,48,96,192,9] 13 :=
  permutation_upper _ _ _ [6,24,192,33,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1188

theorem m2614_33 : Upper (D 10) (R 10) [6,48,96,192,33] 13 :=
  permutation_upper _ _ _ [6,40,96,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1345

theorem m2614_40 : Upper (D 10) (R 10) [6,48,96,192,40] 13 :=
  permutation_upper _ _ _ [6,40,96,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1348

theorem m2614_129 : Upper (D 10) (R 10) [6,48,96,192,129] 13 :=
  permutation_upper _ _ _ [6,40,96,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1360

theorem m2614_136 : Upper (D 10) (R 10) [6,48,96,192,136] 13 :=
  permutation_upper _ _ _ [6,40,96,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1369

theorem m2614_160 : Upper (D 10) (R 10) [6,48,96,192,160] 13 :=
  permutation_upper _ _ _ [6,40,96,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1375

theorem m2614_257 : Upper (D 10) (R 10) [6,48,96,192,257] 13 :=
  permutation_upper _ _ _ [6,40,96,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1362

theorem m2614_264 : Upper (D 10) (R 10) [6,48,96,192,264] 13 :=
  permutation_upper _ _ _ [6,40,96,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1372

theorem m2614_288 : Upper (D 10) (R 10) [6,48,96,192,288] 13 :=
  permutation_upper _ _ _ [6,40,96,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1377

theorem m2614_384 : Upper (D 10) (R 10) [6,48,96,192,384] 13 :=
  permutation_upper _ _ _ [6,40,96,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1390

def r2614 : Route 9 := (fun mask => (mask,id))

def c2614 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2614 : Upper (D 10) (R 10) [6,48,96,192] 13 := by
  apply FastRouting.sound _ _ [6,48,96,192] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r2614 c2614
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2614_9
  · exact m2614_33
  · exact m2614_40
  · exact m2614_129
  · exact m2614_136
  · exact m2614_160
  · exact m2614_257
  · exact m2614_264
  · exact m2614_288
  · exact m2614_384

theorem m2615_9 : Upper (D 10) (R 10) [6,48,96,384,9] 13 :=
  permutation_upper _ _ _ [6,24,192,33,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1190

theorem m2615_33 : Upper (D 10) (R 10) [6,48,96,384,33] 13 :=
  permutation_upper _ _ _ [6,40,96,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1346

theorem m2615_40 : Upper (D 10) (R 10) [6,48,96,384,40] 13 :=
  permutation_upper _ _ _ [6,40,96,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1349

theorem m2615_65 : Upper (D 10) (R 10) [6,48,96,384,65] 13 :=
  permutation_upper _ _ _ [6,40,96,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1351

theorem m2615_72 : Upper (D 10) (R 10) [6,48,96,384,72] 13 :=
  permutation_upper _ _ _ [6,40,96,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1355

theorem m2615_96 : Upper (D 10) (R 10) [6,48,96,384,96] 13 :=
  permutation_upper _ _ _ [6,40,96,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1357

theorem m2615_129 : Upper (D 10) (R 10) [6,48,96,384,129] 13 :=
  permutation_upper _ _ _ [6,40,96,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1363

theorem m2615_136 : Upper (D 10) (R 10) [6,48,96,384,136] 13 :=
  permutation_upper _ _ _ [6,40,96,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1373

theorem m2615_160 : Upper (D 10) (R 10) [6,48,96,384,160] 13 :=
  permutation_upper _ _ _ [6,40,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1378

theorem m2615_192 : Upper (D 10) (R 10) [6,48,96,384,192] 13 :=
  permutation_upper _ _ _ [6,40,96,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1384

theorem m2615_384 : Upper (D 10) (R 10) [6,48,96,384,384] 13 :=
  permutation_upper _ _ _ [6,40,96,384,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1391

def r2615 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2615 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2615 : Upper (D 10) (R 10) [6,48,96,384] 13 := by
  apply FastRouting.sound _ _ [6,48,96,384] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,384] r2615 c2615
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2615_9
  · exact m2615_33
  · exact m2615_40
  · exact m2615_65
  · exact m2615_72
  · exact m2615_96
  · exact m2615_129
  · exact m2615_136
  · exact m2615_160
  · exact m2615_192
  · exact m2615_384

theorem m2616_40 : Upper (D 10) (R 10) [6,48,192,33,40] 13 :=
  permutation_upper _ _ _ [6,40,192,48,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1395

theorem m2616_72 : Upper (D 10) (R 10) [6,48,192,33,72] 13 :=
  permutation_upper _ _ _ [6,40,192,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1403

theorem m2616_96 : Upper (D 10) (R 10) [6,48,192,33,96] 13 :=
  permutation_upper _ _ _ [6,40,192,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1409

theorem m2616_192 : Upper (D 10) (R 10) [6,48,192,33,192] 13 :=
  permutation_upper _ _ _ [6,40,192,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1414

theorem m2616_264 : Upper (D 10) (R 10) [6,48,192,33,264] 13 :=
  permutation_upper _ _ _ [6,40,192,272,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1421

theorem m2616_288 : Upper (D 10) (R 10) [6,48,192,33,288] 13 :=
  permutation_upper _ _ _ [6,40,192,288,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1428

theorem m2616_320 : Upper (D 10) (R 10) [6,48,192,33,320] 13 :=
  permutation_upper _ _ _ [6,40,192,320,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1433

def r2616 : Route 9 := (fun mask => match mask with | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2616 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2616 : Upper (D 10) (R 10) [6,48,192,33] 13 := by
  apply FastRouting.sound _ _ [6,48,192,33] 13 (by decide) (choices 2) [40,72,96,192,264,288,320] r2616 c2616
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2616_40
  · exact m2616_72
  · exact m2616_96
  · exact m2616_192
  · exact m2616_264
  · exact m2616_288
  · exact m2616_320

def b2617 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 50 196 73 440 424 488 424 424), lower := (rows 7 50 196 73 16 32 64 128 256), losses := [] }

theorem u2617 : Upper (D 10) (R 10) [6,48,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2617 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2618_9 : Upper (D 10) (R 10) [6,48,192,96,9] 13 :=
  permutation_upper _ _ _ [6,24,96,33,192] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1169

theorem m2618_33 : Upper (D 10) (R 10) [6,48,192,96,33] 13 :=
  permutation_upper _ _ _ [6,40,192,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1392

theorem m2618_40 : Upper (D 10) (R 10) [6,48,192,96,40] 13 :=
  permutation_upper _ _ _ [6,40,192,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1396

theorem m2618_129 : Upper (D 10) (R 10) [6,48,192,96,129] 13 :=
  permutation_upper _ _ _ [6,40,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1400

theorem m2618_136 : Upper (D 10) (R 10) [6,48,192,96,136] 13 :=
  permutation_upper _ _ _ [6,40,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1405

theorem m2618_160 : Upper (D 10) (R 10) [6,48,192,96,160] 13 :=
  permutation_upper _ _ _ [6,40,192,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1410

theorem m2618_257 : Upper (D 10) (R 10) [6,48,192,96,257] 13 :=
  permutation_upper _ _ _ [6,40,192,257,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1417

theorem m2618_264 : Upper (D 10) (R 10) [6,48,192,96,264] 13 :=
  permutation_upper _ _ _ [6,40,192,272,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1423

theorem m2618_288 : Upper (D 10) (R 10) [6,48,192,96,288] 13 :=
  permutation_upper _ _ _ [6,40,192,288,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1429

theorem m2618_384 : Upper (D 10) (R 10) [6,48,192,96,384] 13 :=
  permutation_upper _ _ _ [6,40,192,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1435

def r2618 : Route 9 := (fun mask => (mask,id))

def c2618 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2618 : Upper (D 10) (R 10) [6,48,192,96] 13 := by
  apply FastRouting.sound _ _ [6,48,192,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r2618 c2618
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2618_9
  · exact m2618_33
  · exact m2618_40
  · exact m2618_129
  · exact m2618_136
  · exact m2618_160
  · exact m2618_257
  · exact m2618_264
  · exact m2618_288
  · exact m2618_384

def b2619 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 8, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 7 50 196 200 313 297 361 425 297), lower := (rows 7 50 196 200 16 32 64 128 256), losses := [] }

theorem u2619 : Upper (D 10) (R 10) [6,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2619 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2620_40 : Upper (D 10) (R 10) [6,48,192,257,40] 13 :=
  permutation_upper _ _ _ [6,40,192,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1397

theorem m2620_72 : Upper (D 10) (R 10) [6,48,192,257,72] 13 :=
  permutation_upper _ _ _ [6,40,192,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1406

theorem m2620_96 : Upper (D 10) (R 10) [6,48,192,257,96] 13 :=
  permutation_upper _ _ _ [6,40,192,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1411

theorem m2620_192 : Upper (D 10) (R 10) [6,48,192,257,192] 13 :=
  permutation_upper _ _ _ [6,40,192,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1415

theorem m2620_264 : Upper (D 10) (R 10) [6,48,192,257,264] 13 :=
  permutation_upper _ _ _ [6,40,192,272,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1425

theorem m2620_288 : Upper (D 10) (R 10) [6,48,192,257,288] 13 :=
  permutation_upper _ _ _ [6,40,192,288,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1430

theorem m2620_320 : Upper (D 10) (R 10) [6,48,192,257,320] 13 :=
  permutation_upper _ _ _ [6,40,192,320,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1436

def r2620 : Route 9 := (fun mask => match mask with | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2620 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2620 : Upper (D 10) (R 10) [6,48,192,257] 13 := by
  apply FastRouting.sound _ _ [6,48,192,257] 13 (by decide) (choices 2) [40,72,96,192,264,288,320] r2620 c2620
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2620_40
  · exact m2620_72
  · exact m2620_96
  · exact m2620_192
  · exact m2620_264
  · exact m2620_288
  · exact m2620_320

theorem m2621_9 : Upper (D 10) (R 10) [6,48,192,288,9] 13 :=
  permutation_upper _ _ _ [6,24,96,33,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1170

theorem m2621_33 : Upper (D 10) (R 10) [6,48,192,288,33] 13 :=
  permutation_upper _ _ _ [6,40,192,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1393

theorem m2621_40 : Upper (D 10) (R 10) [6,48,192,288,40] 13 :=
  permutation_upper _ _ _ [6,40,192,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1398

theorem m2621_65 : Upper (D 10) (R 10) [6,48,192,288,65] 13 :=
  permutation_upper _ _ _ [6,40,192,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1401

theorem m2621_72 : Upper (D 10) (R 10) [6,48,192,288,72] 13 :=
  permutation_upper _ _ _ [6,40,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1407

theorem m2621_96 : Upper (D 10) (R 10) [6,48,192,288,96] 13 :=
  permutation_upper _ _ _ [6,40,192,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1412

theorem m2621_192 : Upper (D 10) (R 10) [6,48,192,288,192] 13 :=
  permutation_upper _ _ _ [6,40,192,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1416

theorem m2621_257 : Upper (D 10) (R 10) [6,48,192,288,257] 13 :=
  permutation_upper _ _ _ [6,40,192,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1419

theorem m2621_264 : Upper (D 10) (R 10) [6,48,192,288,264] 13 :=
  permutation_upper _ _ _ [6,40,192,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1426

theorem m2621_288 : Upper (D 10) (R 10) [6,48,192,288,288] 13 :=
  permutation_upper _ _ _ [6,40,192,288,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1431

theorem m2621_320 : Upper (D 10) (R 10) [6,48,192,288,320] 13 :=
  permutation_upper _ _ _ [6,40,192,320,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1437

def r2621 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2621 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2621 : Upper (D 10) (R 10) [6,48,192,288] 13 := by
  apply FastRouting.sound _ _ [6,48,192,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,192,257,264,288,320] r2621 c2621
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2621_9
  · exact m2621_33
  · exact m2621_40
  · exact m2621_65
  · exact m2621_72
  · exact m2621_96
  · exact m2621_192
  · exact m2621_257
  · exact m2621_264
  · exact m2621_288
  · exact m2621_320

theorem m2622_9 : Upper (D 10) (R 10) [6,48,192,320,9] 13 :=
  permutation_upper _ _ _ [6,24,192,33,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1191

theorem m2622_33 : Upper (D 10) (R 10) [6,48,192,320,33] 13 :=
  permutation_upper _ _ _ [6,40,192,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1394

theorem m2622_40 : Upper (D 10) (R 10) [6,48,192,320,40] 13 :=
  permutation_upper _ _ _ [6,40,192,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1399

theorem m2622_129 : Upper (D 10) (R 10) [6,48,192,320,129] 13 :=
  permutation_upper _ _ _ [6,40,192,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1402

theorem m2622_136 : Upper (D 10) (R 10) [6,48,192,320,136] 13 :=
  permutation_upper _ _ _ [6,40,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1408

theorem m2622_160 : Upper (D 10) (R 10) [6,48,192,320,160] 13 :=
  permutation_upper _ _ _ [6,40,192,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1413

theorem m2622_257 : Upper (D 10) (R 10) [6,48,192,320,257] 13 :=
  permutation_upper _ _ _ [6,40,192,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1420

theorem m2622_264 : Upper (D 10) (R 10) [6,48,192,320,264] 13 :=
  permutation_upper _ _ _ [6,40,192,272,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1427

theorem m2622_288 : Upper (D 10) (R 10) [6,48,192,320,288] 13 :=
  permutation_upper _ _ _ [6,40,192,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1432

theorem m2622_384 : Upper (D 10) (R 10) [6,48,192,320,384] 13 :=
  permutation_upper _ _ _ [6,40,192,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1438

def r2622 : Route 9 := (fun mask => (mask,id))

def c2622 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2622 : Upper (D 10) (R 10) [6,48,192,320] 13 := by
  apply FastRouting.sound _ _ [6,48,192,320] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r2622 c2622
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2622_9
  · exact m2622_33
  · exact m2622_40
  · exact m2622_129
  · exact m2622_136
  · exact m2622_160
  · exact m2622_257
  · exact m2622_264
  · exact m2622_288
  · exact m2622_384

def b2623 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 76 168 432 432 496 432 432), lower := (rows 7 67 76 168 16 32 64 128 256), losses := [] }

theorem u2623 : Upper (D 10) (R 10) [6,65,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2623 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2624 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 76 392 432 432 496 432 432), lower := (rows 7 67 76 392 16 32 64 128 256), losses := [] }

theorem u2624 : Upper (D 10) (R 10) [6,65,72,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2624 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2625 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 84 168 440 424 488 424 424), lower := (rows 7 67 84 168 16 32 64 128 256), losses := [] }

theorem u2625 : Upper (D 10) (R 10) [6,65,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2625 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2626 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 84 392 440 424 488 424 424), lower := (rows 7 67 84 392 16 32 64 128 256), losses := [] }

theorem u2626 : Upper (D 10) (R 10) [6,65,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2626 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2627 : PairBound 9 := { available := 440, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 100 168 440 440 504 440 440), lower := (rows 7 67 100 168 16 32 64 128 256), losses := [] }

theorem u2627 : Upper (D 10) (R 10) [6,65,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2627 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2628 : PairBound 9 := { available := 440, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 100 392 440 440 504 440 440), lower := (rows 7 67 100 392 16 32 64 128 256), losses := [] }

theorem u2628 : Upper (D 10) (R 10) [6,65,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2628 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2629 : Route 9 := (fun mask => (mask,id))

def c2629 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2629 : Upper (D 10) (R 10) [6,65,136,48] 13 := by
  apply FastRouting.sound _ _ [6,65,136,48] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2629 c2629
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1450
  · exact u1451
  · exact u1452
  · exact u1453
  · exact u1454
  · exact u1455

def b2630 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 140 88 432 416 480 416 416), lower := (rows 7 67 140 88 16 32 64 128 256), losses := [] }

theorem u2630 : Upper (D 10) (R 10) [6,65,136,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2630 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2631 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 140 104 432 432 496 432 432), lower := (rows 7 67 140 104 16 32 64 128 256), losses := [] }

theorem u2631 : Upper (D 10) (R 10) [6,65,136,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2631 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2632 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 67 140 152 368 352 352 480 352), lower := (rows 7 67 140 152 16 32 64 128 256), losses := [] }

theorem u2632 : Upper (D 10) (R 10) [6,65,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2632 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2633 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 67 140 168 368 368 368 496 368), lower := (rows 7 67 140 168 16 32 64 128 256), losses := [] }

theorem u2633 : Upper (D 10) (R 10) [6,65,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2633 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2634 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 7, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 67 140 200 304 304 368 432 304), lower := (rows 7 67 140 200 16 32 64 128 256), losses := [] }

theorem u2634 : Upper (D 10) (R 10) [6,65,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2634 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2635 : Route 9 := (fun mask => (mask,id))

def c2635 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2635 : Upper (D 10) (R 10) [6,65,136,272] 13 := by
  apply FastRouting.sound _ _ [6,65,136,272] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2635 c2635
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1465
  · exact u1466
  · exact u1467
  · exact u1468
  · exact u1469
  · exact u1470

def r2636 : Route 9 := (fun mask => (mask,id))

def c2636 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2636 : Upper (D 10) (R 10) [6,65,136,288] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2636 c2636
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1471
  · exact u1472
  · exact u1473
  · exact u1474
  · exact u1475
  · exact u1476

def b2637 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 140 328 432 432 496 432 432), lower := (rows 7 67 140 328 16 32 64 128 256), losses := [] }

theorem u2637 : Upper (D 10) (R 10) [6,65,136,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2637 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2638 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 67 140 392 368 368 368 496 368), lower := (rows 7 67 140 392 16 32 64 128 256), losses := [] }

theorem u2638 : Upper (D 10) (R 10) [6,65,136,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2638 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2639 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 148 104 440 424 488 424 424), lower := (rows 7 67 148 104 16 32 64 128 256), losses := [] }

theorem u2639 : Upper (D 10) (R 10) [6,65,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2639 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u2639
end Delivery.IrregularNine14.P10
