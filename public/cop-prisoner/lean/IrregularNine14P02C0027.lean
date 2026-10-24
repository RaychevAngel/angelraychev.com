import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0020
import IrregularNine14P02C0021
import IrregularNine14P02C0022
import IrregularNine14P02C0023
import IrregularNine14P02C0024

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1620 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4),(3,4)], upper := (rows 23 50 100 457 473 489 457 457 457), lower := (rows 23 50 100 8 16 32 64 128 256), losses := [] }

theorem u1620 : Upper (D 2) (R 2) [22,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1620
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1621 : PairBound 9 := { available := 489, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4),(3,4)], upper := (rows 23 50 196 489 505 489 489 489 489), lower := (rows 23 50 196 8 16 32 64 128 256), losses := [] }

theorem u1621 : Upper (D 2) (R 2) [22,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1621
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1622 : PairBound 9 := { available := 409, camps := [{ cop := 1, region := 4, targets := 144 }], pairs := [(2,4),(2,7)], upper := (rows 23 98 100 409 409 441 473 409 409), lower := (rows 23 98 100 8 16 32 64 128 256), losses := [] }

theorem u1622 : Upper (D 2) (R 2) [22,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1622
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1623_129 : Upper (D 2) (R 2) [22,96,160,129] 13 :=
  permutation_upper _ _ _ [22,96,160,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1258

theorem m1623_144 : Upper (D 2) (R 2) [22,96,160,144] 13 :=
  permutation_upper _ _ _ [22,96,160,80] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1259

theorem m1623_384 : Upper (D 2) (R 2) [22,96,160,384] 13 :=
  permutation_upper _ _ _ [22,96,160,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1263

def r1623 : Route 9 := (fun mask => (mask,id))

def c1623 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u1623 : Upper (D 2) (R 2) [22,96,160] 13 := by
  apply FastRouting.sound _ _ [22,96,160] 13 (by decide) (choices 2) [17,65,80,129,144,192,257,272,320,384] r1623 c1623
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1257
  · exact u1258
  · exact u1259
  · exact m1623_129
  · exact m1623_144
  · exact u1260
  · exact u1261
  · exact u1262
  · exact u1263
  · exact m1623_384

theorem m1624_129 : Upper (D 2) (R 2) [22,96,384,129] 13 :=
  permutation_upper _ _ _ [22,96,384,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1265

theorem m1624_144 : Upper (D 2) (R 2) [22,96,384,144] 13 :=
  permutation_upper _ _ _ [22,96,384,48] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1266

theorem m1624_384 : Upper (D 2) (R 2) [22,96,384,384] 13 :=
  permutation_upper _ _ _ [22,96,384,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1267

def r1624 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1624 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1624 : Upper (D 2) (R 2) [22,96,384] 13 := by
  apply FastRouting.sound _ _ [22,96,384] 13 (by decide) (choices 2) [17,33,48,96,129,144,160,384] r1624 c1624
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1264
  · exact u1265
  · exact u1266
  · exact u1267
  · exact m1624_129
  · exact m1624_144
  · exact u1268
  · exact m1624_384

def r1625 : Route 9 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c1625 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1625 : Upper (D 2) (R 2) [50,5,24] 13 := by
  apply FastRouting.sound _ _ [50,5,24] 13 (by decide) (choices 2) [96,192] r1625 c1625
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1269
  · exact u1270

def b1626 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 51 7 52 456 472 488 456 456 456), lower := (rows 51 7 52 8 16 32 64 128 256), losses := [] }

theorem u1626 : Upper (D 2) (R 2) [50,5,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1626
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1627 : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1627 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1627 : Upper (D 2) (R 2) [50,5,72] 13 := by
  apply FastRouting.sound _ _ [50,5,72] 13 (by decide) (choices 2) [48,80,144,192,384] r1627 c1627
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1271
  · exact u1272
  · exact u1273
  · exact u1274
  · exact u1275

def r1628 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1628 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1628 : Upper (D 2) (R 2) [50,5,80] 13 := by
  apply FastRouting.sound _ _ [50,5,80] 13 (by decide) (choices 2) [96,160,192,384] r1628 c1628
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1276
  · exact u1277
  · exact u1278
  · exact u1279

def r1629 : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1629 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1629 : Upper (D 2) (R 2) [50,5,192] 13 := by
  apply FastRouting.sound _ _ [50,5,192] 13 (by decide) (choices 2) [48,80,192,272,320] r1629 c1629
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1280
  · exact u1281
  · exact u1282
  · exact u1283
  · exact u1284

def b1630 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 14 21 488 496 480 480 480 480), lower := (rows 51 14 21 8 16 32 64 128 256), losses := [] }

theorem u1630 : Upper (D 2) (R 2) [50,12,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1630
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1631 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 14 52 457 465 481 449 449 449), lower := (rows 51 14 52 8 16 32 64 128 256), losses := [] }

theorem u1631 : Upper (D 2) (R 2) [50,12,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1631
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1632_48 : Upper (D 2) (R 2) [50,12,65,48] 13 :=
  permutation_upper _ _ _ [50,12,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1287

def r1632 : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1632 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1632 : Upper (D 2) (R 2) [50,12,65] 13 := by
  apply FastRouting.sound _ _ [50,12,65] 13 (by decide) (choices 2) [48,80,144,192,384] r1632 c1632
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact m1632_48
  · exact u1289
  · exact u1290
  · exact u1291
  · exact u1292

theorem m1633_33 : Upper (D 2) (R 2) [50,12,80,33] 13 :=
  permutation_upper _ _ _ [50,12,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1285

theorem m1633_65 : Upper (D 2) (R 2) [50,12,80,65] 13 :=
  permutation_upper _ _ _ [50,12,65,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1289

theorem m1633_129 : Upper (D 2) (R 2) [50,12,80,129] 13 :=
  permutation_upper _ _ _ [50,12,65,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1290

def r1633 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1633 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1633 : Upper (D 2) (R 2) [50,12,80] 13 := by
  apply FastRouting.sound _ _ [50,12,80] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r1633 c1633
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1633_33
  · exact m1633_65
  · exact u1293
  · exact m1633_129
  · exact u1294
  · exact u1295
  · exact u1296

theorem m1634_17 : Upper (D 2) (R 2) [50,12,192,17] 13 :=
  permutation_upper _ _ _ [50,12,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1286

theorem m1634_48 : Upper (D 2) (R 2) [50,12,192,48] 13 :=
  permutation_upper _ _ _ [50,12,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1288

theorem m1634_65 : Upper (D 2) (R 2) [50,12,192,65] 13 :=
  permutation_upper _ _ _ [50,12,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1291

theorem m1634_80 : Upper (D 2) (R 2) [50,12,192,80] 13 :=
  permutation_upper _ _ _ [50,12,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1295

theorem m1634_257 : Upper (D 2) (R 2) [50,12,192,257] 13 :=
  permutation_upper _ _ _ [50,12,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1292

theorem m1634_272 : Upper (D 2) (R 2) [50,12,192,272] 13 :=
  permutation_upper _ _ _ [50,12,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1296

def r1634 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1634 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1634 : Upper (D 2) (R 2) [50,12,192] 13 := by
  apply FastRouting.sound _ _ [50,12,192] 13 (by decide) (choices 2) [17,48,65,80,192,257,272,320] r1634 c1634
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1634_17
  · exact m1634_48
  · exact m1634_65
  · exact m1634_80
  · exact u1297
  · exact m1634_257
  · exact m1634_272
  · exact u1298

def r1635 : Route 9 := (fun mask => match mask with | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1635 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1635 : Upper (D 2) (R 2) [50,65,24] 13 := by
  apply FastRouting.sound _ _ [50,65,24] 13 (by decide) (choices 2) [36,68,96,132,160,192,384] r1635 c1635
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1299
  · exact u1300
  · exact u1301
  · exact u1302
  · exact u1303
  · exact u1304
  · exact u1305

def b1636 : PairBound 9 := { available := 460, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 67 52 460 476 492 460 460 460), lower := (rows 51 67 52 8 16 32 64 128 256), losses := [] }

theorem u1636 : Upper (D 2) (R 2) [50,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1636
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1637_20 : Upper (D 2) (R 2) [50,65,72,20] 13 :=
  permutation_upper _ _ _ [50,65,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1300

theorem m1637_48 : Upper (D 2) (R 2) [50,65,72,48] 13 :=
  permutation_upper _ _ _ [50,65,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1306

def r1637 : Route 9 := (fun mask => match mask with | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1637 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u1637 : Upper (D 2) (R 2) [50,65,72] 13 := by
  apply FastRouting.sound _ _ [50,65,72] 13 (by decide) (choices 2) [20,48,132,144,384] r1637 c1637
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact m1637_20
  · exact m1637_48
  · exact u1310
  · exact u1311
  · exact u1312

def b1638 : PairBound 9 := { available := 428, camps := [{ cop := 2, region := 424, targets := 16 },{ cop := 2, region := 424, targets := 64 }], pairs := [(3,4),(3,6)], upper := (rows 51 67 84 428 444 428 492 428 428), lower := (rows 51 67 84 8 16 32 64 128 256), losses := [] }

theorem u1638 : Upper (D 2) (R 2) [50,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1638
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1639_20 : Upper (D 2) (R 2) [50,65,136,20] 13 :=
  permutation_upper _ _ _ [50,65,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1302

theorem m1639_48 : Upper (D 2) (R 2) [50,65,136,48] 13 :=
  permutation_upper _ _ _ [50,65,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1307

theorem m1639_68 : Upper (D 2) (R 2) [50,65,136,68] 13 :=
  permutation_upper _ _ _ [50,65,72,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1310

theorem m1639_80 : Upper (D 2) (R 2) [50,65,136,80] 13 :=
  permutation_upper _ _ _ [50,65,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1313

def r1639 : Route 9 := (fun mask => match mask with | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c1639 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u1639 : Upper (D 2) (R 2) [50,65,136] 13 := by
  apply FastRouting.sound _ _ [50,65,136] 13 (by decide) (choices 2) [20,48,68,80,132,144,192,260,272,320,384] r1639 c1639
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1639_20
  · exact m1639_48
  · exact m1639_68
  · exact m1639_80
  · exact u1316
  · exact u1317
  · exact u1318
  · exact u1319
  · exact u1320
  · exact u1321
  · exact u1322

theorem m1640_36 : Upper (D 2) (R 2) [50,65,144,36] 13 :=
  permutation_upper _ _ _ [50,65,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1303

theorem m1640_68 : Upper (D 2) (R 2) [50,65,144,68] 13 :=
  permutation_upper _ _ _ [50,65,72,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1311

theorem m1640_96 : Upper (D 2) (R 2) [50,65,144,96] 13 :=
  permutation_upper _ _ _ [50,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1314

theorem m1640_132 : Upper (D 2) (R 2) [50,65,144,132] 13 :=
  permutation_upper _ _ _ [50,65,136,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1317

theorem m1640_260 : Upper (D 2) (R 2) [50,65,144,260] 13 :=
  permutation_upper _ _ _ [50,65,136,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1320

def r1640 : Route 9 := (fun mask => (mask,id))

def c1640 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1640 : Upper (D 2) (R 2) [50,65,144] 13 := by
  apply FastRouting.sound _ _ [50,65,144] 13 (by decide) (choices 2) [36,68,96,132,160,192,260,288,320,384] r1640 c1640
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1640_36
  · exact m1640_68
  · exact m1640_96
  · exact m1640_132
  · exact u1323
  · exact u1324
  · exact m1640_260
  · exact u1325
  · exact u1326
  · exact u1327

theorem m1641_20 : Upper (D 2) (R 2) [50,65,192,20] 13 :=
  permutation_upper _ _ _ [50,65,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1304

theorem m1641_48 : Upper (D 2) (R 2) [50,65,192,48] 13 :=
  permutation_upper _ _ _ [50,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1308

theorem m1641_132 : Upper (D 2) (R 2) [50,65,192,132] 13 :=
  permutation_upper _ _ _ [50,65,136,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1318

theorem m1641_144 : Upper (D 2) (R 2) [50,65,192,144] 13 :=
  permutation_upper _ _ _ [50,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1324

theorem m1641_260 : Upper (D 2) (R 2) [50,65,192,260] 13 :=
  permutation_upper _ _ _ [50,65,136,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1321

theorem m1641_272 : Upper (D 2) (R 2) [50,65,192,272] 13 :=
  permutation_upper _ _ _ [50,65,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1326

def r1641 : Route 9 := (fun mask => match mask with | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c1641 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u1641 : Upper (D 2) (R 2) [50,65,192] 13 := by
  apply FastRouting.sound _ _ [50,65,192] 13 (by decide) (choices 2) [20,48,132,144,260,272,384] r1641 c1641
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1641_20
  · exact m1641_48
  · exact m1641_132
  · exact m1641_144
  · exact m1641_260
  · exact m1641_272
  · exact u1328

theorem m1642_20 : Upper (D 2) (R 2) [50,65,384,20] 13 :=
  permutation_upper _ _ _ [50,65,24,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1305

theorem m1642_48 : Upper (D 2) (R 2) [50,65,384,48] 13 :=
  permutation_upper _ _ _ [50,65,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1309

theorem m1642_68 : Upper (D 2) (R 2) [50,65,384,68] 13 :=
  permutation_upper _ _ _ [50,65,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1312

theorem m1642_80 : Upper (D 2) (R 2) [50,65,384,80] 13 :=
  permutation_upper _ _ _ [50,65,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1315

theorem m1642_132 : Upper (D 2) (R 2) [50,65,384,132] 13 :=
  permutation_upper _ _ _ [50,65,136,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1322

theorem m1642_144 : Upper (D 2) (R 2) [50,65,384,144] 13 :=
  permutation_upper _ _ _ [50,65,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1327

theorem m1642_192 : Upper (D 2) (R 2) [50,65,384,192] 13 :=
  permutation_upper _ _ _ [50,65,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1328

def r1642 : Route 9 := (fun mask => match mask with | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1642 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u1642 : Upper (D 2) (R 2) [50,65,384] 13 := by
  apply FastRouting.sound _ _ [50,65,384] 13 (by decide) (choices 2) [20,48,68,80,132,144,192,384] r1642 c1642
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1642_20
  · exact m1642_48
  · exact m1642_68
  · exact m1642_80
  · exact m1642_132
  · exact m1642_144
  · exact m1642_192
  · exact u1329

def r1643 : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1643 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1643 : Upper (D 2) (R 2) [50,68,9] 13 := by
  apply FastRouting.sound _ _ [50,68,9] 13 (by decide) (choices 2) [48,80,144,192,384] r1643 c1643
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1330
  · exact u1331
  · exact u1332
  · exact u1333
  · exact u1334

def b1644 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 70 21 488 504 488 488 488 488), lower := (rows 51 70 21 8 16 32 64 128 256), losses := [] }

theorem u1644 : Upper (D 2) (R 2) [50,68,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1644
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1645 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1645 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1645 : Upper (D 2) (R 2) [50,68,24] 13 := by
  apply FastRouting.sound _ _ [50,68,24] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r1645 c1645
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1335
  · exact u1336
  · exact u1337
  · exact u1338
  · exact u1339
  · exact u1340
  · exact u1341

def b1646 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 70 52 457 473 489 457 457 457), lower := (rows 51 70 52 8 16 32 64 128 256), losses := [] }

theorem u1646 : Upper (D 2) (R 2) [50,68,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1646
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1647 : PairBound 9 := { available := 440, camps := [{ cop := 2, region := 2, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 51 70 69 440 440 440 504 440 440), lower := (rows 51 70 69 8 16 32 64 128 256), losses := [] }

theorem u1647 : Upper (D 2) (R 2) [50,68,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1647
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1648 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 2, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 51 70 76 441 433 433 497 433 433), lower := (rows 51 70 76 8 16 32 64 128 256), losses := [] }

theorem u1648 : Upper (D 2) (R 2) [50,68,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1648
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1649 : PairBound 9 := { available := 425, camps := [{ cop := 2, region := 2, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 51 70 84 425 441 425 489 425 425), lower := (rows 51 70 84 8 16 32 64 128 256), losses := [] }

theorem u1649 : Upper (D 2) (R 2) [50,68,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1649
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1650 : Route 9 := (fun mask => match mask with | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c1650 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1650 : Upper (D 2) (R 2) [50,68,129] 13 := by
  apply FastRouting.sound _ _ [50,68,129] 13 (by decide) (choices 2) [48,80,144,192,272,320,384] r1650 c1650
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1342
  · exact u1343
  · exact u1344
  · exact u1345
  · exact u1346
  · exact u1347
  · exact u1348

def r1651 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c1651 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1651 : Upper (D 2) (R 2) [50,68,136] 13 := by
  apply FastRouting.sound _ _ [50,68,136] 13 (by decide) (choices 2) [17,48,65,80,129,144,192,257,272,320,384] r1651 c1651
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1349
  · exact u1350
  · exact u1351
  · exact u1352
  · exact u1353
  · exact u1354
  · exact u1355
  · exact u1356
  · exact u1357
  · exact u1358
  · exact u1359

def r1652 : Route 9 := (fun mask => (mask,id))

def c1652 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1652 : Upper (D 2) (R 2) [50,68,144] 13 := by
  apply FastRouting.sound _ _ [50,68,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r1652 c1652
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1360
  · exact u1361
  · exact u1362
  · exact u1363
  · exact u1364
  · exact u1365
  · exact u1366
  · exact u1367
  · exact u1368
  · exact u1369

def b1653 : PairBound 9 := { available := 441, camps := [{ cop := 2, region := 2, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 51 70 196 441 441 441 505 441 441), lower := (rows 51 70 196 8 16 32 64 128 256), losses := [] }

theorem u1653 : Upper (D 2) (R 2) [50,68,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1653
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1654 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1654 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1654 : Upper (D 2) (R 2) [50,68,384] 13 := by
  apply FastRouting.sound _ _ [50,68,384] 13 (by decide) (choices 2) [17,48,65,80,129,144,192,384] r1654 c1654
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1370
  · exact u1371
  · exact u1372
  · exact u1373
  · exact u1374
  · exact u1375
  · exact u1376
  · exact u1377

def r1655 : Route 9 := (fun mask => match mask with | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1655 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u1655 : Upper (D 2) (R 2) [50,192,9] 13 := by
  apply FastRouting.sound _ _ [50,192,9] 13 (by decide) (choices 2) [20,48,68,80,192,260,272,320] r1655 c1655
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1378
  · exact u1379
  · exact u1380
  · exact u1381
  · exact u1382
  · exact u1383
  · exact u1384
  · exact u1385

def b1656 : PairBound 9 := { available := 492, camps := [{ cop := 0, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 194 21 492 508 492 492 492 492), lower := (rows 51 194 21 8 16 32 64 128 256), losses := [] }

theorem u1656 : Upper (D 2) (R 2) [50,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1656
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1657_5 : Upper (D 2) (R 2) [50,192,24,5] 13 :=
  permutation_upper _ _ _ [50,192,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1378

theorem m1657_33 : Upper (D 2) (R 2) [50,192,24,33] 13 :=
  permutation_upper _ _ _ [50,192,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1386

def r1657 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1657 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1657 : Upper (D 2) (R 2) [50,192,24] 13 := by
  apply FastRouting.sound _ _ [50,192,24] 13 (by decide) (choices 2) [5,33,36,65,68,96,192,257,260,288,320] r1657 c1657
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1657_5
  · exact m1657_33
  · exact u1392
  · exact u1393
  · exact u1394
  · exact u1395
  · exact u1396
  · exact u1397
  · exact u1398
  · exact u1399
  · exact u1400

def b1658 : PairBound 9 := { available := 461, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 194 52 461 477 493 461 461 461), lower := (rows 51 194 52 8 16 32 64 128 256), losses := [] }

theorem u1658 : Upper (D 2) (R 2) [50,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1658
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1659_20 : Upper (D 2) (R 2) [50,192,65,20] 13 :=
  permutation_upper _ _ _ [50,192,24,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1393

theorem m1659_48 : Upper (D 2) (R 2) [50,192,65,48] 13 :=
  permutation_upper _ _ _ [50,192,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1401

def r1659 : Route 9 := (fun mask => match mask with | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c1659 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u1659 : Upper (D 2) (R 2) [50,192,65] 13 := by
  apply FastRouting.sound _ _ [50,192,65] 13 (by decide) (choices 2) [20,48,132,144,260,272,384] r1659 c1659
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1659_20
  · exact m1659_48
  · exact u1406
  · exact u1407
  · exact u1408
  · exact u1409
  · exact u1410

theorem m1660_5 : Upper (D 2) (R 2) [50,192,72,5] 13 :=
  permutation_upper _ _ _ [50,192,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1380

theorem m1660_17 : Upper (D 2) (R 2) [50,192,72,17] 13 :=
  permutation_upper _ _ _ [50,192,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1387

theorem m1660_20 : Upper (D 2) (R 2) [50,192,72,20] 13 :=
  permutation_upper _ _ _ [50,192,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1394

theorem m1660_48 : Upper (D 2) (R 2) [50,192,72,48] 13 :=
  permutation_upper _ _ _ [50,192,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1402

theorem m1660_129 : Upper (D 2) (R 2) [50,192,72,129] 13 :=
  permutation_upper _ _ _ [50,192,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1406

def r1660 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c1660 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u1660 : Upper (D 2) (R 2) [50,192,72] 13 := by
  apply FastRouting.sound _ _ [50,192,72] 13 (by decide) (choices 2) [5,17,20,48,129,132,144,257,260,272,384] r1660 c1660
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1660_5
  · exact m1660_17
  · exact m1660_20
  · exact m1660_48
  · exact m1660_129
  · exact u1411
  · exact u1412
  · exact u1413
  · exact u1414
  · exact u1415
  · exact u1416

theorem m1661_5 : Upper (D 2) (R 2) [50,192,80,5] 13 :=
  permutation_upper _ _ _ [50,192,9,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1381

theorem m1661_33 : Upper (D 2) (R 2) [50,192,80,33] 13 :=
  permutation_upper _ _ _ [50,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1388

theorem m1661_36 : Upper (D 2) (R 2) [50,192,80,36] 13 :=
  permutation_upper _ _ _ [50,192,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1395

theorem m1661_129 : Upper (D 2) (R 2) [50,192,80,129] 13 :=
  permutation_upper _ _ _ [50,192,65,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1407

theorem m1661_132 : Upper (D 2) (R 2) [50,192,80,132] 13 :=
  permutation_upper _ _ _ [50,192,72,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1412

def r1661 : Route 9 := (fun mask => (mask,id))

def c1661 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u1661 : Upper (D 2) (R 2) [50,192,80] 13 := by
  apply FastRouting.sound _ _ [50,192,80] 13 (by decide) (choices 2) [5,33,36,129,132,160,257,260,288,384] r1661 c1661
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1661_5
  · exact m1661_33
  · exact m1661_36
  · exact m1661_129
  · exact m1661_132
  · exact u1417
  · exact u1418
  · exact u1419
  · exact u1420
  · exact u1421

def b1662 : PairBound 9 := { available := 317, camps := [{ cop := 1, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 51 194 196 317 317 317 381 445 317), lower := (rows 51 194 196 8 16 32 64 128 256), losses := [] }

theorem u1662 : Upper (D 2) (R 2) [50,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1662
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1663_20 : Upper (D 2) (R 2) [50,192,257,20] 13 :=
  permutation_upper _ _ _ [50,192,24,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1397

theorem m1663_48 : Upper (D 2) (R 2) [50,192,257,48] 13 :=
  permutation_upper _ _ _ [50,192,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1403

theorem m1663_68 : Upper (D 2) (R 2) [50,192,257,68] 13 :=
  permutation_upper _ _ _ [50,192,72,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1413

theorem m1663_80 : Upper (D 2) (R 2) [50,192,257,80] 13 :=
  permutation_upper _ _ _ [50,192,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1418

theorem m1663_192 : Upper (D 2) (R 2) [50,192,257,192] 13 :=
  permutation_upper _ _ _ [50,192,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1422

def r1663 : Route 9 := (fun mask => match mask with | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1663 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u1663 : Upper (D 2) (R 2) [50,192,257] 13 := by
  apply FastRouting.sound _ _ [50,192,257] 13 (by decide) (choices 2) [20,48,68,80,192,260,272,320] r1663 c1663
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1663_20
  · exact m1663_48
  · exact m1663_68
  · exact m1663_80
  · exact m1663_192
  · exact u1425
  · exact u1426
  · exact u1427

theorem m1664_5 : Upper (D 2) (R 2) [50,192,264,5] 13 :=
  permutation_upper _ _ _ [50,192,9,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1383

theorem m1664_17 : Upper (D 2) (R 2) [50,192,264,17] 13 :=
  permutation_upper _ _ _ [50,192,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1389

theorem m1664_20 : Upper (D 2) (R 2) [50,192,264,20] 13 :=
  permutation_upper _ _ _ [50,192,24,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1398

theorem m1664_48 : Upper (D 2) (R 2) [50,192,264,48] 13 :=
  permutation_upper _ _ _ [50,192,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1404

theorem m1664_65 : Upper (D 2) (R 2) [50,192,264,65] 13 :=
  permutation_upper _ _ _ [50,192,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1408

theorem m1664_68 : Upper (D 2) (R 2) [50,192,264,68] 13 :=
  permutation_upper _ _ _ [50,192,72,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1414

theorem m1664_80 : Upper (D 2) (R 2) [50,192,264,80] 13 :=
  permutation_upper _ _ _ [50,192,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1419

theorem m1664_192 : Upper (D 2) (R 2) [50,192,264,192] 13 :=
  permutation_upper _ _ _ [50,192,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1423

theorem m1664_257 : Upper (D 2) (R 2) [50,192,264,257] 13 :=
  permutation_upper _ _ _ [50,192,257,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1425

def r1664 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1664 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u1664 : Upper (D 2) (R 2) [50,192,264] 13 := by
  apply FastRouting.sound _ _ [50,192,264] 13 (by decide) (choices 2) [5,17,20,48,65,68,80,192,257,260,272,320] r1664 c1664
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1664_5
  · exact m1664_17
  · exact m1664_20
  · exact m1664_48
  · exact m1664_65
  · exact m1664_68
  · exact m1664_80
  · exact m1664_192
  · exact m1664_257
  · exact u1428
  · exact u1429
  · exact u1430

theorem m1665_5 : Upper (D 2) (R 2) [50,192,272,5] 13 :=
  permutation_upper _ _ _ [50,192,9,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1384

theorem m1665_33 : Upper (D 2) (R 2) [50,192,272,33] 13 :=
  permutation_upper _ _ _ [50,192,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1390

theorem m1665_36 : Upper (D 2) (R 2) [50,192,272,36] 13 :=
  permutation_upper _ _ _ [50,192,24,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1399

theorem m1665_65 : Upper (D 2) (R 2) [50,192,272,65] 13 :=
  permutation_upper _ _ _ [50,192,65,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1409

theorem m1665_68 : Upper (D 2) (R 2) [50,192,272,68] 13 :=
  permutation_upper _ _ _ [50,192,72,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1415

theorem m1665_96 : Upper (D 2) (R 2) [50,192,272,96] 13 :=
  permutation_upper _ _ _ [50,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1420

theorem m1665_192 : Upper (D 2) (R 2) [50,192,272,192] 13 :=
  permutation_upper _ _ _ [50,192,192,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1424

theorem m1665_257 : Upper (D 2) (R 2) [50,192,272,257] 13 :=
  permutation_upper _ _ _ [50,192,257,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1426

theorem m1665_260 : Upper (D 2) (R 2) [50,192,272,260] 13 :=
  permutation_upper _ _ _ [50,192,264,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1429

def r1665 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1665 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1665 : Upper (D 2) (R 2) [50,192,272] 13 := by
  apply FastRouting.sound _ _ [50,192,272] 13 (by decide) (choices 2) [5,33,36,65,68,96,192,257,260,288,320] r1665 c1665
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1665_5
  · exact m1665_33
  · exact m1665_36
  · exact m1665_65
  · exact m1665_68
  · exact m1665_96
  · exact m1665_192
  · exact m1665_257
  · exact m1665_260
  · exact u1431
  · exact u1432

theorem m1666_5 : Upper (D 2) (R 2) [50,192,320,5] 13 :=
  permutation_upper _ _ _ [50,192,9,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1385

theorem m1666_17 : Upper (D 2) (R 2) [50,192,320,17] 13 :=
  permutation_upper _ _ _ [50,192,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1391

theorem m1666_20 : Upper (D 2) (R 2) [50,192,320,20] 13 :=
  permutation_upper _ _ _ [50,192,24,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1400

theorem m1666_48 : Upper (D 2) (R 2) [50,192,320,48] 13 :=
  permutation_upper _ _ _ [50,192,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1405

theorem m1666_129 : Upper (D 2) (R 2) [50,192,320,129] 13 :=
  permutation_upper _ _ _ [50,192,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1410

theorem m1666_132 : Upper (D 2) (R 2) [50,192,320,132] 13 :=
  permutation_upper _ _ _ [50,192,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1416

theorem m1666_144 : Upper (D 2) (R 2) [50,192,320,144] 13 :=
  permutation_upper _ _ _ [50,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1421

theorem m1666_257 : Upper (D 2) (R 2) [50,192,320,257] 13 :=
  permutation_upper _ _ _ [50,192,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1427

theorem m1666_260 : Upper (D 2) (R 2) [50,192,320,260] 13 :=
  permutation_upper _ _ _ [50,192,264,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1430

theorem m1666_272 : Upper (D 2) (R 2) [50,192,320,272] 13 :=
  permutation_upper _ _ _ [50,192,272,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1432

def r1666 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c1666 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u1666 : Upper (D 2) (R 2) [50,192,320] 13 := by
  apply FastRouting.sound _ _ [50,192,320] 13 (by decide) (choices 2) [5,17,20,48,129,132,144,257,260,272,384] r1666 c1666
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1666_5
  · exact m1666_17
  · exact m1666_20
  · exact m1666_48
  · exact m1666_129
  · exact m1666_132
  · exact m1666_144
  · exact m1666_257
  · exact m1666_260
  · exact m1666_272
  · exact u1433

def r1667 : Route 9 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1667 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1667 : Upper (D 2) (R 2) [112,5,10] 13 := by
  apply FastRouting.sound _ _ [112,5,10] 13 (by decide) (choices 2) [48,144,384] r1667 c1667
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1434
  · exact u1435
  · exact u1436

def b1668 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 6, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 7 22 488 504 488 488 488 488), lower := (rows 113 7 22 8 16 32 64 128 256), losses := [] }

theorem u1668 : Upper (D 2) (R 2) [112,5,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1668
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1669 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1669 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1669 : Upper (D 2) (R 2) [112,5,24] 13 := by
  apply FastRouting.sound _ _ [112,5,24] 13 (by decide) (choices 2) [34,96,130,160,384] r1669 c1669
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1439
  · exact u1440
  · exact u1441
  · exact u1442
  · exact u1443

def b1670 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 6, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 7 52 458 474 490 458 458 458), lower := (rows 113 7 52 8 16 32 64 128 256), losses := [] }

theorem u1670 : Upper (D 2) (R 2) [112,5,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1670
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1671 : Route 9 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c1671 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1671 : Upper (D 2) (R 2) [112,5,130] 13 := by
  apply FastRouting.sound _ _ [112,5,130] 13 (by decide) (choices 2) [48,144,272,384] r1671 c1671
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1448
  · exact u1449
  · exact u1450
  · exact u1451

def r1672 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c1672 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1672 : Upper (D 2) (R 2) [112,5,136] 13 := by
  apply FastRouting.sound _ _ [112,5,136] 13 (by decide) (choices 2) [18,48,130,144,258,272,384] r1672 c1672
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1452
  · exact u1453
  · exact u1454
  · exact u1455
  · exact u1456
  · exact u1457
  · exact u1458

def r1673 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1673 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1673 : Upper (D 2) (R 2) [112,5,144] 13 := by
  apply FastRouting.sound _ _ [112,5,144] 13 (by decide) (choices 2) [34,96,130,160,258,288,384] r1673 c1673
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1459
  · exact u1460
  · exact u1461
  · exact u1462
  · exact u1463
  · exact u1464
  · exact u1465

def r1674 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1674 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1674 : Upper (D 2) (R 2) [112,5,384] 13 := by
  apply FastRouting.sound _ _ [112,5,384] 13 (by decide) (choices 2) [18,48,130,144,384] r1674 c1674
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1466
  · exact u1467
  · exact u1468
  · exact u1469
  · exact u1470

theorem m1675_36 : Upper (D 2) (R 2) [112,9,18,36] 13 :=
  permutation_upper _ _ _ [112,5,24,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1439

theorem m1675_96 : Upper (D 2) (R 2) [112,9,18,96] 13 :=
  permutation_upper _ _ _ [112,5,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 6 | 6 => 4 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1444

theorem m1675_132 : Upper (D 2) (R 2) [112,9,18,132] 13 :=
  permutation_upper _ _ _ [112,5,136,18] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1452

theorem m1675_160 : Upper (D 2) (R 2) [112,9,18,160] 13 :=
  permutation_upper _ _ _ [112,5,144,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1459

theorem m1675_384 : Upper (D 2) (R 2) [112,9,18,384] 13 :=
  permutation_upper _ _ _ [112,5,384,18] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1466

def r1675 : Route 9 := (fun mask => match mask with | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1675 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1675 : Upper (D 2) (R 2) [112,9,18] 13 := by
  apply FastRouting.sound _ _ [112,9,18] 13 (by decide) (choices 2) [36,96,132,160,384] r1675 c1675
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact m1675_36
  · exact m1675_96
  · exact m1675_132
  · exact m1675_160
  · exact m1675_384

theorem m1676_20 : Upper (D 2) (R 2) [112,9,130,20] 13 :=
  permutation_upper _ _ _ [112,5,24,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1441

theorem m1676_48 : Upper (D 2) (R 2) [112,9,130,48] 13 :=
  permutation_upper _ _ _ [112,5,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1445

theorem m1676_132 : Upper (D 2) (R 2) [112,9,130,132] 13 :=
  permutation_upper _ _ _ [112,5,136,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1454

theorem m1676_144 : Upper (D 2) (R 2) [112,9,130,144] 13 :=
  permutation_upper _ _ _ [112,5,144,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1461

theorem m1676_260 : Upper (D 2) (R 2) [112,9,130,260] 13 :=
  permutation_upper _ _ _ [112,5,136,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1456

theorem m1676_272 : Upper (D 2) (R 2) [112,9,130,272] 13 :=
  permutation_upper _ _ _ [112,5,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1463

theorem m1676_384 : Upper (D 2) (R 2) [112,9,130,384] 13 :=
  permutation_upper _ _ _ [112,5,384,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1468

def r1676 : Route 9 := (fun mask => match mask with | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 68 => (20,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c1676 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u1676 : Upper (D 2) (R 2) [112,9,130] 13 := by
  apply FastRouting.sound _ _ [112,9,130] 13 (by decide) (choices 2) [20,48,132,144,260,272,384] r1676 c1676
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1676_20
  · exact m1676_48
  · exact m1676_132
  · exact m1676_144
  · exact m1676_260
  · exact m1676_272
  · exact m1676_384

theorem m1677_6 : Upper (D 2) (R 2) [112,9,144,6] 13 :=
  permutation_upper _ _ _ [112,5,10,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1435

theorem m1677_34 : Upper (D 2) (R 2) [112,9,144,34] 13 :=
  permutation_upper _ _ _ [112,5,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1437

theorem m1677_36 : Upper (D 2) (R 2) [112,9,144,36] 13 :=
  permutation_upper _ _ _ [112,5,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1442

theorem m1677_96 : Upper (D 2) (R 2) [112,9,144,96] 13 :=
  permutation_upper _ _ _ [112,5,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 6 | 6 => 4 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1446

theorem m1677_130 : Upper (D 2) (R 2) [112,9,144,130] 13 :=
  permutation_upper _ _ _ [112,5,130,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1449

theorem m1677_132 : Upper (D 2) (R 2) [112,9,144,132] 13 :=
  permutation_upper _ _ _ [112,5,136,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1455

theorem m1677_160 : Upper (D 2) (R 2) [112,9,144,160] 13 :=
  permutation_upper _ _ _ [112,5,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1462

theorem m1677_258 : Upper (D 2) (R 2) [112,9,144,258] 13 :=
  permutation_upper _ _ _ [112,5,130,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1450

theorem m1677_260 : Upper (D 2) (R 2) [112,9,144,260] 13 :=
  permutation_upper _ _ _ [112,5,136,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1457

theorem m1677_288 : Upper (D 2) (R 2) [112,9,144,288] 13 :=
  permutation_upper _ _ _ [112,5,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1464

theorem m1677_384 : Upper (D 2) (R 2) [112,9,144,384] 13 :=
  permutation_upper _ _ _ [112,5,384,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1469

def r1677 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1677 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1677 : Upper (D 2) (R 2) [112,9,144] 13 := by
  apply FastRouting.sound _ _ [112,9,144] 13 (by decide) (choices 2) [6,34,36,96,130,132,160,258,260,288,384] r1677 c1677
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1677_6
  · exact m1677_34
  · exact m1677_36
  · exact m1677_96
  · exact m1677_130
  · exact m1677_132
  · exact m1677_160
  · exact m1677_258
  · exact m1677_260
  · exact m1677_288
  · exact m1677_384

theorem m1678_6 : Upper (D 2) (R 2) [112,9,384,6] 13 :=
  permutation_upper _ _ _ [112,5,10,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1436

theorem m1678_18 : Upper (D 2) (R 2) [112,9,384,18] 13 :=
  permutation_upper _ _ _ [112,5,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1438

theorem m1678_20 : Upper (D 2) (R 2) [112,9,384,20] 13 :=
  permutation_upper _ _ _ [112,5,24,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1443

theorem m1678_48 : Upper (D 2) (R 2) [112,9,384,48] 13 :=
  permutation_upper _ _ _ [112,5,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1447

theorem m1678_130 : Upper (D 2) (R 2) [112,9,384,130] 13 :=
  permutation_upper _ _ _ [112,5,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1451

theorem m1678_132 : Upper (D 2) (R 2) [112,9,384,132] 13 :=
  permutation_upper _ _ _ [112,5,136,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1458

theorem m1678_144 : Upper (D 2) (R 2) [112,9,384,144] 13 :=
  permutation_upper _ _ _ [112,5,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1465

theorem m1678_384 : Upper (D 2) (R 2) [112,9,384,384] 13 :=
  permutation_upper _ _ _ [112,5,384,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1470

def r1678 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 68 => (20,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1678 : Nat → Fin 9 := (fun _ => 0)

theorem u1678 : Upper (D 2) (R 2) [112,9,384] 13 := by
  apply FastRouting.sound _ _ [112,9,384] 13 (by decide) (choices 2) [6,18,20,48,130,132,144,384] r1678 c1678
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1678_6
  · exact m1678_18
  · exact m1678_20
  · exact m1678_48
  · exact m1678_130
  · exact m1678_132
  · exact m1678_144
  · exact m1678_384

def b1679 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 113 14 21 490 498 482 482 482 482), lower := (rows 113 14 21 8 16 32 64 128 256), losses := [] }

theorem u1679 : Upper (D 2) (R 2) [112,12,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1679
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u1679
end Delivery.IrregularNine14.P02
