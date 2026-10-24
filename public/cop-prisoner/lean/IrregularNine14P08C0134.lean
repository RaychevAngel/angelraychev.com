import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0025
import IrregularNine14P08C0026

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8040 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 292 25 81 168 232 168 424), lower := (rows 7 98 292 25 81 32 64 128 256), losses := [] }

theorem u8040 : Upper (D 8) (R 8) [6,96,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8040 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8041 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 292 25 88 161 225 161 417), lower := (rows 7 98 292 25 88 32 64 128 256), losses := [] }

theorem u8041 : Upper (D 8) (R 8) [6,96,288,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8042 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 292 25 112 169 201 137 393), lower := (rows 7 98 292 25 112 32 64 128 256), losses := [] }

theorem u8042 : Upper (D 8) (R 8) [6,96,288,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8043 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 292 25 145 232 232 232 488), lower := (rows 7 98 292 25 145 32 64 128 256), losses := [] }

theorem u8043 : Upper (D 8) (R 8) [6,96,288,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8044 : Route 9 := (fun mask => (mask,id))

def c8044 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8044 : Upper (D 8) (R 8) [6,96,288,17,136] 13 := by
  apply FastRouting.sound _ _ [6,96,288,17,136] 13 (by decide) (choices 1) [1,64,128] r8044 c8044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1545
  · exact u1546
  · exact u1547

def r8045 : Route 9 := (fun mask => (mask,id))

def c8045 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8045 : Upper (D 8) (R 8) [6,96,288,17,160] 13 := by
  apply FastRouting.sound _ _ [6,96,288,17,160] 13 (by decide) (choices 1) [1,8,64,128] r8045 c8045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1548
  · exact u1549
  · exact u1550
  · exact u1551

def b8046 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 292 25 208 169 233 169 425), lower := (rows 7 98 292 25 208 32 64 128 256), losses := [] }

theorem u8046 : Upper (D 8) (R 8) [6,96,288,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8047 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 292 41 88 177 209 145 401), lower := (rows 7 98 292 41 88 32 64 128 256), losses := [] }

theorem u8047 : Upper (D 8) (R 8) [6,96,288,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8048 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 292 41 145 248 216 216 472), lower := (rows 7 98 292 41 145 32 64 128 256), losses := [] }

theorem u8048 : Upper (D 8) (R 8) [6,96,288,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8049 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 292 41 152 241 209 209 465), lower := (rows 7 98 292 41 152 32 64 128 256), losses := [] }

theorem u8049 : Upper (D 8) (R 8) [6,96,288,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8050 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 292 41 208 185 217 153 409), lower := (rows 7 98 292 41 208 32 64 128 256), losses := [] }

theorem u8050 : Upper (D 8) (R 8) [6,96,288,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8051 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 292 56 81 169 201 137 393), lower := (rows 7 98 292 56 81 32 64 128 256), losses := [] }

theorem u8051 : Upper (D 8) (R 8) [6,96,288,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8052 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 292 56 88 161 193 129 385), lower := (rows 7 98 292 56 88 32 64 128 256), losses := [] }

theorem u8052 : Upper (D 8) (R 8) [6,96,288,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8053 : Route 9 := (fun mask => (mask,id))

def c8053 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8053 : Upper (D 8) (R 8) [6,96,288,48,129] 13 := by
  apply FastRouting.sound _ _ [6,96,288,48,129] 13 (by decide) (choices 1) [1,8,64,128] r8053 c8053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1552
  · exact u1553
  · exact u1554
  · exact u1555

def r8054 : Route 9 := (fun mask => (mask,id))

def c8054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8054 : Upper (D 8) (R 8) [6,96,288,48,136] 13 := by
  apply FastRouting.sound _ _ [6,96,288,48,136] 13 (by decide) (choices 1) [1,64,128] r8054 c8054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1556
  · exact u1557
  · exact u1558

def r8055 : Route 9 := (fun mask => (mask,id))

def c8055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8055 : Upper (D 8) (R 8) [6,96,288,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,288,48,192] 13 (by decide) (choices 1) [1,8,128] r8055 c8055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1559
  · exact u1560
  · exact u1561

def b8056 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 292 73 145 184 248 184 440), lower := (rows 7 98 292 73 145 32 64 128 256), losses := [] }

theorem u8056 : Upper (D 8) (R 8) [6,96,288,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8056 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8057 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 292 73 152 177 241 177 433), lower := (rows 7 98 292 73 152 32 64 128 256), losses := [] }

theorem u8057 : Upper (D 8) (R 8) [6,96,288,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8058 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 292 73 176 185 217 153 409), lower := (rows 7 98 292 73 176 32 64 128 256), losses := [] }

theorem u8058 : Upper (D 8) (R 8) [6,96,288,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8059 : Route 9 := (fun mask => (mask,id))

def c8059 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8059 : Upper (D 8) (R 8) [6,96,288,80,129] 13 := by
  apply FastRouting.sound _ _ [6,96,288,80,129] 13 (by decide) (choices 1) [1,8,128] r8059 c8059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1562
  · exact u1563
  · exact u1564

def b8060 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 292 88 152 161 225 161 417), lower := (rows 7 98 292 88 152 32 64 128 256), losses := [] }

theorem u8060 : Upper (D 8) (R 8) [6,96,288,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8061 : Route 9 := (fun mask => (mask,id))

def c8061 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8061 : Upper (D 8) (R 8) [6,96,288,80,160] 13 := by
  apply FastRouting.sound _ _ [6,96,288,80,160] 13 (by decide) (choices 1) [1,8,128] r8061 c8061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1565
  · exact u1566
  · exact u1567

def b8062 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 292 104 145 185 217 153 409), lower := (rows 7 98 292 104 145 32 64 128 256), losses := [] }

theorem u8062 : Upper (D 8) (R 8) [6,96,288,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8063 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 292 104 152 177 209 145 401), lower := (rows 7 98 292 104 152 32 64 128 256), losses := [] }

theorem u8063 : Upper (D 8) (R 8) [6,96,288,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8064 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 292 137 145 120 120 248 376), lower := (rows 7 98 292 137 145 32 64 128 256), losses := [] }

theorem u8064 : Upper (D 8) (R 8) [6,96,288,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8065 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 292 137 152 113 113 241 369), lower := (rows 7 98 292 137 152 32 64 128 256), losses := [] }

theorem u8065 : Upper (D 8) (R 8) [6,96,288,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8065 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8066 : Route 9 := (fun mask => (mask,id))

def c8066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8066 : Upper (D 8) (R 8) [6,96,288,129,160] 13 := by
  apply FastRouting.sound _ _ [6,96,288,129,160] 13 (by decide) (choices 1) [1,8,16,64] r8066 c8066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1568
  · exact u1569
  · exact u1570
  · exact u1571

def r8067 : Route 9 := (fun mask => (mask,id))

def c8067 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8067 : Upper (D 8) (R 8) [6,96,288,129,192] 13 := by
  apply FastRouting.sound _ _ [6,96,288,129,192] 13 (by decide) (choices 1) [1,8,16] r8067 c8067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1572
  · exact u1573
  · exact u1574

def b8068 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 292 152 152 97 97 225 353), lower := (rows 7 98 292 152 152 32 64 128 256), losses := [] }

theorem u8068 : Upper (D 8) (R 8) [6,96,288,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8069 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 292 152 176 105 73 201 329), lower := (rows 7 98 292 152 176 32 64 128 256), losses := [] }

theorem u8069 : Upper (D 8) (R 8) [6,96,288,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8070 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 292 152 208 41 105 169 297), lower := (rows 7 98 292 152 208 32 64 128 256), losses := [] }

theorem u8070 : Upper (D 8) (R 8) [6,96,288,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8071 : Route 9 := (fun mask => (mask,id))

def c8071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8071 : Upper (D 8) (R 8) [6,96,288,160,192] 13 := by
  apply FastRouting.sound _ _ [6,96,288,160,192] 13 (by decide) (choices 1) [1,8,16] r8071 c8071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1575
  · exact u1576
  · exact u1577

def b8072 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 388 25 25 224 224 224 480), lower := (rows 7 98 388 25 25 32 64 128 256), losses := [] }

theorem u8072 : Upper (D 8) (R 8) [6,96,384,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8072 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8073 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 388 25 49 232 232 232 488), lower := (rows 7 98 388 25 49 32 64 128 256), losses := [] }

theorem u8073 : Upper (D 8) (R 8) [6,96,384,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8074 : Route 9 := (fun mask => (mask,id))

def c8074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8074 : Upper (D 8) (R 8) [6,96,384,17,40] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17,40] 13 (by decide) (choices 1) [1,64,128] r8074 c8074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1578
  · exact u1579
  · exact u1580

def b8075 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 388 25 81 168 232 168 424), lower := (rows 7 98 388 25 81 32 64 128 256), losses := [] }

theorem u8075 : Upper (D 8) (R 8) [6,96,384,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8076 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 388 25 88 161 225 161 417), lower := (rows 7 98 388 25 88 32 64 128 256), losses := [] }

theorem u8076 : Upper (D 8) (R 8) [6,96,384,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8076 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8077 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 388 25 112 169 233 169 425), lower := (rows 7 98 388 25 112 32 64 128 256), losses := [] }

theorem u8077 : Upper (D 8) (R 8) [6,96,384,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8078 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 388 25 145 104 104 232 360), lower := (rows 7 98 388 25 145 32 64 128 256), losses := [] }

theorem u8078 : Upper (D 8) (R 8) [6,96,384,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8078 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8079 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 388 25 152 97 97 225 353), lower := (rows 7 98 388 25 152 32 64 128 256), losses := [] }

theorem u8079 : Upper (D 8) (R 8) [6,96,384,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8080 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 388 25 176 105 105 233 361), lower := (rows 7 98 388 25 176 32 64 128 256), losses := [] }

theorem u8080 : Upper (D 8) (R 8) [6,96,384,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8081 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 388 25 208 41 105 169 297), lower := (rows 7 98 388 25 208 32 64 128 256), losses := [] }

theorem u8081 : Upper (D 8) (R 8) [6,96,384,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8082 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 98 388 41 49 248 216 216 472), lower := (rows 7 98 388 41 49 32 64 128 256), losses := [] }

theorem u8082 : Upper (D 8) (R 8) [6,96,384,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8082 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8083 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 388 41 56 241 209 209 465), lower := (rows 7 98 388 41 56 32 64 128 256), losses := [] }

theorem u8083 : Upper (D 8) (R 8) [6,96,384,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8084 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 388 41 81 184 248 184 440), lower := (rows 7 98 388 41 81 32 64 128 256), losses := [] }

theorem u8084 : Upper (D 8) (R 8) [6,96,384,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8084 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8085 : Route 9 := (fun mask => (mask,id))

def c8085 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8085 : Upper (D 8) (R 8) [6,96,384,33,72] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,72] 13 (by decide) (choices 1) [1,16,128] r8085 c8085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1581
  · exact u1582
  · exact u1583

def b8086 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 388 41 112 185 217 153 409), lower := (rows 7 98 388 41 112 32 64 128 256), losses := [] }

theorem u8086 : Upper (D 8) (R 8) [6,96,384,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8087 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 388 41 145 120 120 248 376), lower := (rows 7 98 388 41 145 32 64 128 256), losses := [] }

theorem u8087 : Upper (D 8) (R 8) [6,96,384,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8088 : Route 9 := (fun mask => (mask,id))

def c8088 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8088 : Upper (D 8) (R 8) [6,96,384,33,136] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,136] 13 (by decide) (choices 1) [1,16,64] r8088 c8088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1584
  · exact u1585
  · exact u1586

def r8089 : Route 9 := (fun mask => (mask,id))

def c8089 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8089 : Upper (D 8) (R 8) [6,96,384,33,160] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,160] 13 (by decide) (choices 1) [1,8,16,64] r8089 c8089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1587
  · exact u1588
  · exact u1589
  · exact u1590

def r8090 : Route 9 := (fun mask => (mask,id))

def c8090 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8090 : Upper (D 8) (R 8) [6,96,384,33,192] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,192] 13 (by decide) (choices 1) [1,8,16] r8090 c8090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1591
  · exact u1592
  · exact u1593

def b8091 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 388 56 56 225 193 193 449), lower := (rows 7 98 388 56 56 32 64 128 256), losses := [] }

theorem u8091 : Upper (D 8) (R 8) [6,96,384,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8091 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8092 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 388 56 81 169 233 169 425), lower := (rows 7 98 388 56 81 32 64 128 256), losses := [] }

theorem u8092 : Upper (D 8) (R 8) [6,96,384,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8092 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8093 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 388 56 88 161 225 161 417), lower := (rows 7 98 388 56 88 32 64 128 256), losses := [] }

theorem u8093 : Upper (D 8) (R 8) [6,96,384,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8093 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8094 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 388 56 112 169 201 137 393), lower := (rows 7 98 388 56 112 32 64 128 256), losses := [] }

theorem u8094 : Upper (D 8) (R 8) [6,96,384,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8094 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8095 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 388 56 145 105 105 233 361), lower := (rows 7 98 388 56 145 32 64 128 256), losses := [] }

theorem u8095 : Upper (D 8) (R 8) [6,96,384,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8095 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8096 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 388 56 152 97 97 225 353), lower := (rows 7 98 388 56 152 32 64 128 256), losses := [] }

theorem u8096 : Upper (D 8) (R 8) [6,96,384,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8097 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 388 56 176 105 73 201 329), lower := (rows 7 98 388 56 176 32 64 128 256), losses := [] }

theorem u8097 : Upper (D 8) (R 8) [6,96,384,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8098 : Route 9 := (fun mask => (mask,id))

def c8098 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8098 : Upper (D 8) (R 8) [6,96,384,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,192] 13 (by decide) (choices 1) [1,8] r8098 c8098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1594
  · exact u1595

def b8099 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 388 73 152 49 113 177 305), lower := (rows 7 98 388 73 152 32 64 128 256), losses := [] }

theorem u8099 : Upper (D 8) (R 8) [6,96,384,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8099 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u8099
end Delivery.IrregularNine14.P08
