import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0018
import IrregularNine14P02C0019
import IrregularNine14P02C0020

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1560 : PairBound 9 := { available := 334, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 50 133 392 350 366 334 462 334), lower := (rows 113 50 133 392 16 32 64 128 256), losses := [] }

theorem u1560 : Upper (D 2) (R 2) [112,48,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1560
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1561 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 50 134 200 285 301 333 397 269), lower := (rows 113 50 134 200 16 32 64 128 256), losses := [] }

theorem u1561 : Upper (D 2) (R 2) [112,48,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1561
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1562 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 50 134 268 473 489 457 457 457), lower := (rows 113 50 134 268 16 32 64 128 256), losses := [] }

theorem u1562 : Upper (D 2) (R 2) [112,48,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1562
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1563 : PairBound 9 := { available := 397, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 50 134 328 413 429 461 397 397), lower := (rows 113 50 134 328 16 32 64 128 256), losses := [] }

theorem u1563 : Upper (D 2) (R 2) [112,48,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1563
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1564 : PairBound 9 := { available := 333, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 50 134 392 349 365 333 461 333), lower := (rows 113 50 134 392 16 32 64 128 256), losses := [] }

theorem u1564 : Upper (D 2) (R 2) [112,48,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1564
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1565 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 50 140 268 467 483 451 451 451), lower := (rows 113 50 140 268 16 32 64 128 256), losses := [] }

theorem u1565 : Upper (D 2) (R 2) [112,48,136,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1565
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1566 : PairBound 9 := { available := 391, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 50 140 328 407 423 455 391 391), lower := (rows 113 50 140 328 16 32 64 128 256), losses := [] }

theorem u1566 : Upper (D 2) (R 2) [112,48,136,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1566
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1567 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 50 196 392 287 303 335 399 271), lower := (rows 113 50 196 392 16 32 64 128 256), losses := [] }

theorem u1567 : Upper (D 2) (R 2) [112,48,192,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1567
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1568 : PairBound 9 := { available := 376, camps := [{ cop := 1, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 113 131 134 268 376 376 376 504 376), lower := (rows 113 131 134 268 16 32 64 128 256), losses := [] }

theorem u1568 : Upper (D 2) (R 2) [112,129,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1568
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1569 : PairBound 9 := { available := 364, camps := [{ cop := 1, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 113 131 134 280 380 364 364 492 364), lower := (rows 113 131 134 280 16 32 64 128 256), losses := [] }

theorem u1569 : Upper (D 2) (R 2) [112,129,130,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1569
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1570 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1570 : Upper (D 2) (R 2) [112,129,136,258] 13 := by
  apply FastRouting.sound _ _ [112,129,136,258] 13 (by decide) (choices 1) [4,32,256] r1570 c1570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1134
  · exact u1135
  · exact u1136

def r1571 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1571 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1571 : Upper (D 2) (R 2) [112,129,136,260] 13 := by
  apply FastRouting.sound _ _ [112,129,136,260] 13 (by decide) (choices 1) [2,32,256] r1571 c1571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1137
  · exact u1138
  · exact u1139

def r1572 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1572 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | _ => 0)

theorem u1572 : Upper (D 2) (R 2) [112,129,136,272] 13 := by
  apply FastRouting.sound _ _ [112,129,136,272] 13 (by decide) (choices 1) [2,4,32,256] r1572 c1572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1140
  · exact u1141
  · exact u1142
  · exact u1143

def r1573 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | _ => 0)

theorem u1573 : Upper (D 2) (R 2) [112,129,144,258] 13 := by
  apply FastRouting.sound _ _ [112,129,144,258] 13 (by decide) (choices 1) [4,8,32,256] r1573 c1573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1144
  · exact u1145
  · exact u1146
  · exact u1147

def r1574 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1574 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | _ => 0)

theorem u1574 : Upper (D 2) (R 2) [112,129,144,260] 13 := by
  apply FastRouting.sound _ _ [112,129,144,260] 13 (by decide) (choices 1) [2,8,32,256] r1574 c1574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1148
  · exact u1149
  · exact u1150
  · exact u1151

def r1575 : Route 9 := (fun mask => (mask,id))

def c1575 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | _ => 0)

theorem u1575 : Upper (D 2) (R 2) [112,129,144,288] 13 := by
  apply FastRouting.sound _ _ [112,129,144,288] 13 (by decide) (choices 1) [2,4,8,64,256] r1575 c1575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1152
  · exact u1153
  · exact u1154
  · exact u1155
  · exact u1156

def b1576 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 8, targets := 48 }], pairs := [(3,4),(3,5)], upper := (rows 113 131 262 268 248 248 248 248 504), lower := (rows 113 131 262 268 16 32 64 128 256), losses := [] }

theorem u1576 : Upper (D 2) (R 2) [112,129,258,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1576
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1577 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1577 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 256 => 8 | _ => 0)

theorem u1577 : Upper (D 2) (R 2) [112,129,258,272] 13 := by
  apply FastRouting.sound _ _ [112,129,258,272] 13 (by decide) (choices 1) [4,8,32,128] r1577 c1577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1157
  · exact u1158
  · exact u1159
  · exact u1160

def r1578 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1578 : Upper (D 2) (R 2) [112,129,258,384] 13 := by
  apply FastRouting.sound _ _ [112,129,258,384] 13 (by decide) (choices 1) [4,8,32] r1578 c1578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1161
  · exact u1162
  · exact u1163

def b1579 : PairBound 9 := { available := 242, camps := [{ cop := 8, region := 12, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 113 131 268 268 242 242 242 242 498), lower := (rows 113 131 268 268 16 32 64 128 256), losses := [] }

theorem u1579 : Upper (D 2) (R 2) [112,129,264,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1579
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1580 : PairBound 9 := { available := 230, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 113 131 268 280 246 230 230 230 486), lower := (rows 113 131 268 280 16 32 64 128 256), losses := [] }

theorem u1580 : Upper (D 2) (R 2) [112,129,264,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1580
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1581 : PairBound 9 := { available := 118, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 113 131 268 392 118 118 118 246 374), lower := (rows 113 131 268 392 16 32 64 128 256), losses := [] }

theorem u1581 : Upper (D 2) (R 2) [112,129,264,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1581
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1582 : Route 9 := (fun mask => (mask,id))

def c1582 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 256 => 8 | _ => 0)

theorem u1582 : Upper (D 2) (R 2) [112,129,272,288] 13 := by
  apply FastRouting.sound _ _ [112,129,272,288] 13 (by decide) (choices 1) [2,4,8,64,128] r1582 c1582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1164
  · exact u1165
  · exact u1166
  · exact u1167
  · exact u1168

def r1583 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1583 : Nat → Fin 9 := (fun mask => match mask with | 128 => 7 | 256 => 8 | _ => 0)

theorem u1583 : Upper (D 2) (R 2) [112,129,272,384] 13 := by
  apply FastRouting.sound _ _ [112,129,272,384] 13 (by decide) (choices 1) [2,4,8,32] r1583 c1583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1169
  · exact u1170
  · exact u1171
  · exact u1172

def b1584 : PairBound 9 := { available := 361, camps := [{ cop := 7, region := 6, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 113 134 134 280 377 361 361 489 361), lower := (rows 113 134 134 280 16 32 64 128 256), losses := [] }

theorem u1584 : Upper (D 2) (R 2) [112,132,130,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1584
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1585 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 2, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 113 134 140 266 369 369 369 497 369), lower := (rows 113 134 140 266 16 32 64 128 256), losses := [] }

theorem u1585 : Upper (D 2) (R 2) [112,132,136,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1585
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1586 : PairBound 9 := { available := 355, camps := [{ cop := 2, region := 2, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 113 134 140 280 371 355 355 483 355), lower := (rows 113 134 140 280 16 32 64 128 256), losses := [] }

theorem u1586 : Upper (D 2) (R 2) [112,132,136,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1586
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1587 : PairBound 9 := { available := 361, camps := [{ cop := 2, region := 2, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 113 134 148 266 377 361 361 489 361), lower := (rows 113 134 148 266 16 32 64 128 256), losses := [] }

theorem u1587 : Upper (D 2) (R 2) [112,132,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1587
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1588 : PairBound 9 := { available := 331, camps := [{ cop := 2, region := 2, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 113 134 148 296 347 363 331 459 331), lower := (rows 113 134 148 296 16 32 64 128 256), losses := [] }

theorem u1588 : Upper (D 2) (R 2) [112,132,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1588
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1589 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u1589 : Upper (D 2) (R 2) [112,132,258,144] 13 := by
  apply FastRouting.sound _ _ [112,132,258,144] 13 (by decide) (choices 1) [1,8,32,256] r1589 c1589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1173
  · exact u1174
  · exact u1175
  · exact u1176

def b1590 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 6, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 113 134 262 392 121 121 121 249 377), lower := (rows 113 134 262 392 16 32 64 128 256), losses := [] }

theorem u1590 : Upper (D 2) (R 2) [112,132,258,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1590
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1591 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1591 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1591 : Upper (D 2) (R 2) [112,132,264,144] 13 := by
  apply FastRouting.sound _ _ [112,132,264,144] 13 (by decide) (choices 1) [1,2,32,256] r1591 c1591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1177
  · exact u1178
  · exact u1179
  · exact u1180

def b1592 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 6, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 113 134 268 392 115 115 115 243 371), lower := (rows 113 134 268 392 16 32 64 128 256), losses := [] }

theorem u1592 : Upper (D 2) (R 2) [112,132,264,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1592
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1593 : Route 9 := (fun mask => (mask,id))

def c1593 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u1593 : Upper (D 2) (R 2) [112,132,272,160] 13 := by
  apply FastRouting.sound _ _ [112,132,272,160] 13 (by decide) (choices 1) [1,2,8,64,256] r1593 c1593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1181
  · exact u1182
  · exact u1183
  · exact u1184
  · exact u1185

def r1594 : Route 9 := (fun mask => (mask,id))

def c1594 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1594 : Upper (D 2) (R 2) [112,132,272,288] 13 := by
  apply FastRouting.sound _ _ [112,132,272,288] 13 (by decide) (choices 1) [1,2,8,64,128] r1594 c1594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1186
  · exact u1187
  · exact u1188
  · exact u1189
  · exact u1190

def r1595 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1595 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1595 : Upper (D 2) (R 2) [112,132,272,384] 13 := by
  apply FastRouting.sound _ _ [112,132,272,384] 13 (by decide) (choices 1) [1,2,8,32] r1595 c1595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1191
  · exact u1192
  · exact u1193
  · exact u1194

def b1596 : PairBound 9 := { available := 107, camps := [{ cop := 2, region := 2, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 113 134 388 280 123 107 107 235 363), lower := (rows 113 134 388 280 16 32 64 128 256), losses := [] }

theorem u1596 : Upper (D 2) (R 2) [112,132,384,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1596
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1597 : Route 9 := (fun mask => (mask,id))

def c1597 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1597 : Upper (D 2) (R 2) [112,144,160,320] 13 := by
  apply FastRouting.sound _ _ [112,144,160,320] 13 (by decide) (choices 1) [1,2,4,8,256] r1597 c1597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1195
  · exact u1196
  · exact u1197
  · exact u1198
  · exact u1199

def r1598 : Route 9 := (fun mask => (mask,id))

def c1598 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1598 : Upper (D 2) (R 2) [112,144,288,384] 13 := by
  apply FastRouting.sound _ _ [112,144,288,384] 13 (by decide) (choices 1) [1,2,4,8,64] r1598 c1598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1200
  · exact u1201
  · exact u1202
  · exact u1203
  · exact u1204

def r1599 : Route 9 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c1599 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1599 : Upper (D 2) (R 2) [14,17,48] 13 := by
  apply FastRouting.sound _ _ [14,17,48] 13 (by decide) (choices 2) [96,192] r1599 c1599
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1205
  · exact u1206

theorem m1600_48 : Upper (D 2) (R 2) [14,17,96,48] 13 :=
  permutation_upper _ _ _ [14,17,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1205

theorem m1600_144 : Upper (D 2) (R 2) [14,17,96,144] 13 :=
  permutation_upper _ _ _ [14,17,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1206

def r1600 : Route 9 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1600 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1600 : Upper (D 2) (R 2) [14,17,96] 13 := by
  apply FastRouting.sound _ _ [14,17,96] 13 (by decide) (choices 2) [48,96,144,160,384] r1600 c1600
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact m1600_48
  · exact u1207
  · exact m1600_144
  · exact u1208
  · exact u1209

def b1601 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 15 50 52 457 465 481 449 449 449), lower := (rows 15 50 52 8 16 32 64 128 256), losses := [] }

theorem u1601 : Upper (D 2) (R 2) [14,48,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1601
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1602_33 : Upper (D 2) (R 2) [14,48,80,33] 13 :=
  permutation_upper _ _ _ [14,17,48,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1205

theorem m1602_65 : Upper (D 2) (R 2) [14,48,80,65] 13 :=
  permutation_upper _ _ _ [14,17,48,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 6 | 5 => 4 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 5 | 5 => 6 | 6 => 4 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1205

theorem m1602_129 : Upper (D 2) (R 2) [14,48,80,129] 13 :=
  permutation_upper _ _ _ [14,17,96,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 7 | 5 => 4 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 6 | 6 => 7 | 7 => 4 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1208

theorem m1602_192 : Upper (D 2) (R 2) [14,48,80,192] 13 :=
  permutation_upper _ _ _ [14,48,80,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1212

def r1602 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1602 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u1602 : Upper (D 2) (R 2) [14,48,80] 13 := by
  apply FastRouting.sound _ _ [14,48,80] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r1602 c1602
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1602_33
  · exact m1602_65
  · exact u1211
  · exact m1602_129
  · exact u1212
  · exact m1602_192
  · exact u1213

theorem m1603_17 : Upper (D 2) (R 2) [14,48,192,17] 13 :=
  permutation_upper _ _ _ [14,17,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1206

theorem m1603_48 : Upper (D 2) (R 2) [14,48,192,48] 13 :=
  permutation_upper _ _ _ [14,48,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1210

theorem m1603_65 : Upper (D 2) (R 2) [14,48,192,65] 13 :=
  permutation_upper _ _ _ [14,17,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1206

theorem m1603_80 : Upper (D 2) (R 2) [14,48,192,80] 13 :=
  permutation_upper _ _ _ [14,48,80,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1212

theorem m1603_192 : Upper (D 2) (R 2) [14,48,192,192] 13 :=
  permutation_upper _ _ _ [14,48,48,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1210

theorem m1603_257 : Upper (D 2) (R 2) [14,48,192,257] 13 :=
  permutation_upper _ _ _ [14,17,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 8 | 5 => 4 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 4) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1209

theorem m1603_272 : Upper (D 2) (R 2) [14,48,192,272] 13 :=
  permutation_upper _ _ _ [14,48,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1213

theorem m1603_320 : Upper (D 2) (R 2) [14,48,192,320] 13 :=
  permutation_upper _ _ _ [14,48,80,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 6 | 5 => 7 | 6 => 8 | 7 => 4 | _ => 5) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 7 | 5 => 8 | 6 => 4 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1213

def r1603 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1603 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1603 : Upper (D 2) (R 2) [14,48,192] 13 := by
  apply FastRouting.sound _ _ [14,48,192] 13 (by decide) (choices 2) [17,48,65,80,192,257,272,320] r1603 c1603
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m1603_17
  · exact m1603_48
  · exact m1603_65
  · exact m1603_80
  · exact m1603_192
  · exact m1603_257
  · exact m1603_272
  · exact m1603_320

def b1604 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4),(3,4)], upper := (rows 23 11 52 488 496 480 480 480 480), lower := (rows 23 11 52 8 16 32 64 128 256), losses := [] }

theorem u1604 : Upper (D 2) (R 2) [22,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1604
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1605 : Route 9 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1605 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1605 : Upper (D 2) (R 2) [22,9,96] 13 := by
  apply FastRouting.sound _ _ [22,9,96] 13 (by decide) (choices 2) [48,96,144,160,384] r1605 c1605
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1214
  · exact u1215
  · exact u1216
  · exact u1217
  · exact u1218

def b1606 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 2, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 23 19 44 488 496 480 480 480 480), lower := (rows 23 19 44 8 16 32 64 128 256), losses := [] }

theorem u1606 : Upper (D 2) (R 2) [22,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1606
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1607 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 2, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 23 19 100 488 504 488 488 488 488), lower := (rows 23 19 100 8 16 32 64 128 256), losses := [] }

theorem u1607 : Upper (D 2) (R 2) [22,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1607
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1608 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4),(3,4)], upper := (rows 23 26 37 488 496 480 480 480 480), lower := (rows 23 26 37 8 16 32 64 128 256), losses := [] }

theorem u1608 : Upper (D 2) (R 2) [22,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1608
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1609 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4),(3,4)], upper := (rows 23 26 100 489 497 481 481 481 481), lower := (rows 23 26 100 8 16 32 64 128 256), losses := [] }

theorem u1609 : Upper (D 2) (R 2) [22,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1609
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1610 : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c1610 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u1610 : Upper (D 2) (R 2) [22,33,40] 13 := by
  apply FastRouting.sound _ _ [22,33,40] 13 (by decide) (choices 2) [80,192] r1610 c1610
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1219
  · exact u1220

def b1611 : PairBound 9 := { available := 456, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 23 35 52 456 472 488 456 456 456), lower := (rows 23 35 52 8 16 32 64 128 256), losses := [] }

theorem u1611 : Upper (D 2) (R 2) [22,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1611
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1612 : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1612 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1612 : Upper (D 2) (R 2) [22,33,72] 13 := by
  apply FastRouting.sound _ _ [22,33,72] 13 (by decide) (choices 2) [48,80,96,144,160,192,384] r1612 c1612
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1221
  · exact u1222
  · exact u1223
  · exact u1224
  · exact u1225
  · exact u1226
  · exact u1227

def b1613 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4),(3,4)], upper := (rows 23 35 84 488 504 488 488 488 488), lower := (rows 23 35 84 8 16 32 64 128 256), losses := [] }

theorem u1613 : Upper (D 2) (R 2) [22,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1613
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1614 : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1614 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u1614 : Upper (D 2) (R 2) [22,33,96] 13 := by
  apply FastRouting.sound _ _ [22,33,96] 13 (by decide) (choices 2) [80,144,192,384] r1614 c1614
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1228
  · exact u1229
  · exact u1230
  · exact u1231

def r1615 : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1615 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1615 : Upper (D 2) (R 2) [22,33,192] 13 := by
  apply FastRouting.sound _ _ [22,33,192] 13 (by decide) (choices 2) [48,80,96,192,272,288,320] r1615 c1615
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1232
  · exact u1233
  · exact u1234
  · exact u1235
  · exact u1236
  · exact u1237
  · exact u1238

def b1616 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4),(3,4)], upper := (rows 23 42 52 457 465 481 449 449 449), lower := (rows 23 42 52 8 16 32 64 128 256), losses := [] }

theorem u1616 : Upper (D 2) (R 2) [22,40,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1616
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1617 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4),(3,4)], upper := (rows 23 42 84 489 497 481 481 481 481), lower := (rows 23 42 84 8 16 32 64 128 256), losses := [] }

theorem u1617 : Upper (D 2) (R 2) [22,40,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1617
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1618 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1618 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u1618 : Upper (D 2) (R 2) [22,40,96] 13 := by
  apply FastRouting.sound _ _ [22,40,96] 13 (by decide) (choices 2) [17,65,80,129,144,192,384] r1618 c1618
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1239
  · exact u1240
  · exact u1241
  · exact u1242
  · exact u1243
  · exact u1244
  · exact u1245

def r1619 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1619 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u1619 : Upper (D 2) (R 2) [22,40,192] 13 := by
  apply FastRouting.sound _ _ [22,40,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,257,272,288,320] r1619 c1619
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1246
  · exact u1247
  · exact u1248
  · exact u1249
  · exact u1250
  · exact u1251
  · exact u1252
  · exact u1253
  · exact u1254
  · exact u1255
  · exact u1256

#print axioms u1619
end Delivery.IrregularNine14.P02
