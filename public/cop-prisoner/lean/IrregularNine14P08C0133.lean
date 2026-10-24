import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0025

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7980 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 261 56 88 161 225 161 417), lower := (rows 7 98 261 56 88 32 64 128 256), losses := [] }

theorem u7980 : Upper (D 8) (R 8) [6,96,257,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7981 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 261 56 112 169 201 137 393), lower := (rows 7 98 261 56 112 32 64 128 256), losses := [] }

theorem u7981 : Upper (D 8) (R 8) [6,96,257,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7982 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 56 145 232 232 232 488), lower := (rows 7 98 261 56 145 32 64 128 256), losses := [] }

theorem u7982 : Upper (D 8) (R 8) [6,96,257,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7982 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7983 : Route 9 := (fun mask => (mask,id))

def c7983 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7983 : Upper (D 8) (R 8) [6,96,257,48,136] 13 := by
  apply FastRouting.sound _ _ [6,96,257,48,136] 13 (by decide) (choices 1) [1,64,128] r7983 c7983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1501
  · exact u1502
  · exact u1503

def b7984 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 261 56 176 233 201 201 457), lower := (rows 7 98 261 56 176 32 64 128 256), losses := [] }

theorem u7984 : Upper (D 8) (R 8) [6,96,257,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7985 : Route 9 := (fun mask => (mask,id))

def c7985 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7985 : Upper (D 8) (R 8) [6,96,257,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,257,48,192] 13 (by decide) (choices 1) [1,8,128] r7985 c7985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1504
  · exact u1505
  · exact u1506

def b7986 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 73 152 176 240 176 432), lower := (rows 7 98 261 73 152 32 64 128 256), losses := [] }

theorem u7986 : Upper (D 8) (R 8) [6,96,257,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7987 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 73 176 184 248 184 440), lower := (rows 7 98 261 73 176 32 64 128 256), losses := [] }

theorem u7987 : Upper (D 8) (R 8) [6,96,257,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7988 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 88 145 168 232 168 424), lower := (rows 7 98 261 88 145 32 64 128 256), losses := [] }

theorem u7988 : Upper (D 8) (R 8) [6,96,257,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7989 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 261 88 152 161 225 161 417), lower := (rows 7 98 261 88 152 32 64 128 256), losses := [] }

theorem u7989 : Upper (D 8) (R 8) [6,96,257,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7990 : Route 9 := (fun mask => (mask,id))

def c7990 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7990 : Upper (D 8) (R 8) [6,96,257,80,160] 13 := by
  apply FastRouting.sound _ _ [6,96,257,80,160] 13 (by decide) (choices 1) [1,8,128] r7990 c7990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1507
  · exact u1508
  · exact u1509

def b7991 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 261 104 152 177 241 177 433), lower := (rows 7 98 261 104 152 32 64 128 256), losses := [] }

theorem u7991 : Upper (D 8) (R 8) [6,96,257,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7992 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 261 104 176 185 217 153 409), lower := (rows 7 98 261 104 176 32 64 128 256), losses := [] }

theorem u7992 : Upper (D 8) (R 8) [6,96,257,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7993 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 261 137 152 112 112 240 368), lower := (rows 7 98 261 137 152 32 64 128 256), losses := [] }

theorem u7993 : Upper (D 8) (R 8) [6,96,257,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7994 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 114, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 137 176 120 120 248 376), lower := (rows 7 98 261 137 176 32 64 128 256), losses := [] }

theorem u7994 : Upper (D 8) (R 8) [6,96,257,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7994 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7995 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 114, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 137 208 56 120 184 312), lower := (rows 7 98 261 137 208 32 64 128 256), losses := [] }

theorem u7995 : Upper (D 8) (R 8) [6,96,257,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7996 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 261 152 152 97 97 225 353), lower := (rows 7 98 261 152 152 32 64 128 256), losses := [] }

theorem u7996 : Upper (D 8) (R 8) [6,96,257,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7996 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7997 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 261 152 176 105 105 233 361), lower := (rows 7 98 261 152 176 32 64 128 256), losses := [] }

theorem u7997 : Upper (D 8) (R 8) [6,96,257,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7998 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 261 152 208 41 105 169 297), lower := (rows 7 98 261 152 208 32 64 128 256), losses := [] }

theorem u7998 : Upper (D 8) (R 8) [6,96,257,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7999 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 261 168 176 121 89 217 345), lower := (rows 7 98 261 168 176 32 64 128 256), losses := [] }

theorem u7999 : Upper (D 8) (R 8) [6,96,257,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8000 : Route 9 := (fun mask => (mask,id))

def c8000 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8000 : Upper (D 8) (R 8) [6,96,257,160,192] 13 := by
  apply FastRouting.sound _ _ [6,96,257,160,192] 13 (by decide) (choices 1) [1,8,16] r8000 c8000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1510
  · exact u1511
  · exact u1512

def b8001 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 268 25 49 224 224 224 480), lower := (rows 7 98 268 25 49 32 64 128 256), losses := [] }

theorem u8001 : Upper (D 8) (R 8) [6,96,264,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8001 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8002 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 268 25 81 160 224 160 416), lower := (rows 7 98 268 25 81 32 64 128 256), losses := [] }

theorem u8002 : Upper (D 8) (R 8) [6,96,264,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8002 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8003 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 268 25 112 161 225 161 417), lower := (rows 7 98 268 25 112 32 64 128 256), losses := [] }

theorem u8003 : Upper (D 8) (R 8) [6,96,264,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8004 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 268 25 145 224 224 224 480), lower := (rows 7 98 268 25 145 32 64 128 256), losses := [] }

theorem u8004 : Upper (D 8) (R 8) [6,96,264,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8004 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8005 : Route 9 := (fun mask => (mask,id))

def c8005 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8005 : Upper (D 8) (R 8) [6,96,264,17,160] 13 := by
  apply FastRouting.sound _ _ [6,96,264,17,160] 13 (by decide) (choices 1) [1,64,128] r8005 c8005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1513
  · exact u1514
  · exact u1515

def b8006 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 268 25 208 161 225 161 417), lower := (rows 7 98 268 25 208 32 64 128 256), losses := [] }

theorem u8006 : Upper (D 8) (R 8) [6,96,264,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8007 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 98 268 41 49 240 208 208 464), lower := (rows 7 98 268 41 49 32 64 128 256), losses := [] }

theorem u8007 : Upper (D 8) (R 8) [6,96,264,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8007 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8008 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 268 41 81 176 240 176 432), lower := (rows 7 98 268 41 81 32 64 128 256), losses := [] }

theorem u8008 : Upper (D 8) (R 8) [6,96,264,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8008 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8009 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 268 41 112 177 209 145 401), lower := (rows 7 98 268 41 112 32 64 128 256), losses := [] }

theorem u8009 : Upper (D 8) (R 8) [6,96,264,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8010 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 268 41 145 240 240 240 496), lower := (rows 7 98 268 41 145 32 64 128 256), losses := [] }

theorem u8010 : Upper (D 8) (R 8) [6,96,264,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8010 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8011 : Route 9 := (fun mask => (mask,id))

def c8011 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8011 : Upper (D 8) (R 8) [6,96,264,33,160] 13 := by
  apply FastRouting.sound _ _ [6,96,264,33,160] 13 (by decide) (choices 1) [1,16,64,128] r8011 c8011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1516
  · exact u1517
  · exact u1518
  · exact u1519

def r8012 : Route 9 := (fun mask => (mask,id))

def c8012 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8012 : Upper (D 8) (R 8) [6,96,264,33,192] 13 := by
  apply FastRouting.sound _ _ [6,96,264,33,192] 13 (by decide) (choices 1) [1,16,128] r8012 c8012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1520
  · exact u1521
  · exact u1522

def b8013 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 268 56 49 225 193 193 449), lower := (rows 7 98 268 56 49 32 64 128 256), losses := [] }

theorem u8013 : Upper (D 8) (R 8) [6,96,264,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8013 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8014 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 268 56 81 161 225 161 417), lower := (rows 7 98 268 56 81 32 64 128 256), losses := [] }

theorem u8014 : Upper (D 8) (R 8) [6,96,264,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8014 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8015 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 268 56 112 161 193 129 385), lower := (rows 7 98 268 56 112 32 64 128 256), losses := [] }

theorem u8015 : Upper (D 8) (R 8) [6,96,264,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8015 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8016 : Route 9 := (fun mask => (mask,id))

def c8016 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8016 : Upper (D 8) (R 8) [6,96,264,48,129] 13 := by
  apply FastRouting.sound _ _ [6,96,264,48,129] 13 (by decide) (choices 1) [1,64,128] r8016 c8016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1523
  · exact u1524
  · exact u1525

def b8017 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 268 56 176 225 193 193 449), lower := (rows 7 98 268 56 176 32 64 128 256), losses := [] }

theorem u8017 : Upper (D 8) (R 8) [6,96,264,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8018 : Route 9 := (fun mask => (mask,id))

def c8018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8018 : Upper (D 8) (R 8) [6,96,264,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,264,48,192] 13 (by decide) (choices 1) [1,128] r8018 c8018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1526
  · exact u1527

def b8019 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 268 137 49 240 240 240 496), lower := (rows 7 98 268 137 49 32 64 128 256), losses := [] }

theorem u8019 : Upper (D 8) (R 8) [6,96,264,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8019 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8020 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 268 137 81 176 240 176 432), lower := (rows 7 98 268 137 81 32 64 128 256), losses := [] }

theorem u8020 : Upper (D 8) (R 8) [6,96,264,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8020 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8021 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 268 137 112 177 241 177 433), lower := (rows 7 98 268 137 112 32 64 128 256), losses := [] }

theorem u8021 : Upper (D 8) (R 8) [6,96,264,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8022 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 268 137 145 112 112 240 368), lower := (rows 7 98 268 137 145 32 64 128 256), losses := [] }

theorem u8022 : Upper (D 8) (R 8) [6,96,264,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8022 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8023 : Route 9 := (fun mask => (mask,id))

def c8023 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8023 : Upper (D 8) (R 8) [6,96,264,129,160] 13 := by
  apply FastRouting.sound _ _ [6,96,264,129,160] 13 (by decide) (choices 1) [1,16,64] r8023 c8023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1528
  · exact u1529
  · exact u1530

def r8024 : Route 9 := (fun mask => (mask,id))

def c8024 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8024 : Upper (D 8) (R 8) [6,96,264,129,192] 13 := by
  apply FastRouting.sound _ _ [6,96,264,129,192] 13 (by decide) (choices 1) [1,16] r8024 c8024
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1531
  · exact u1532

def r8025 : Route 9 := (fun mask => (mask,id))

def c8025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8025 : Upper (D 8) (R 8) [6,96,264,144,33] 13 := by
  apply FastRouting.sound _ _ [6,96,264,144,33] 13 (by decide) (choices 1) [1,64,128] r8025 c8025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1533
  · exact u1534
  · exact u1535

def b8026 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 268 152 81 161 225 161 417), lower := (rows 7 98 268 152 81 32 64 128 256), losses := [] }

theorem u8026 : Upper (D 8) (R 8) [6,96,264,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8026 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8027 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 268 152 112 161 225 161 417), lower := (rows 7 98 268 152 112 32 64 128 256), losses := [] }

theorem u8027 : Upper (D 8) (R 8) [6,96,264,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8028 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 268 152 145 97 97 225 353), lower := (rows 7 98 268 152 145 32 64 128 256), losses := [] }

theorem u8028 : Upper (D 8) (R 8) [6,96,264,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8028 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8029 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 268 152 176 97 97 225 353), lower := (rows 7 98 268 152 176 32 64 128 256), losses := [] }

theorem u8029 : Upper (D 8) (R 8) [6,96,264,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8029 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8030 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 268 152 208 33 97 161 289), lower := (rows 7 98 268 152 208 32 64 128 256), losses := [] }

theorem u8030 : Upper (D 8) (R 8) [6,96,264,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8031 : Route 9 := (fun mask => (mask,id))

def c8031 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8031 : Upper (D 8) (R 8) [6,96,264,160,33] 13 := by
  apply FastRouting.sound _ _ [6,96,264,160,33] 13 (by decide) (choices 1) [1,16,64,128] r8031 c8031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1536
  · exact u1537
  · exact u1538
  · exact u1539

def b8032 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 268 168 81 177 241 177 433), lower := (rows 7 98 268 168 81 32 64 128 256), losses := [] }

theorem u8032 : Upper (D 8) (R 8) [6,96,264,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8033 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 268 168 112 177 209 145 401), lower := (rows 7 98 268 168 112 32 64 128 256), losses := [] }

theorem u8033 : Upper (D 8) (R 8) [6,96,264,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8033 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8034 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 268 168 145 113 113 241 369), lower := (rows 7 98 268 168 145 32 64 128 256), losses := [] }

theorem u8034 : Upper (D 8) (R 8) [6,96,264,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8035 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 268 168 176 113 81 209 337), lower := (rows 7 98 268 168 176 32 64 128 256), losses := [] }

theorem u8035 : Upper (D 8) (R 8) [6,96,264,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8036 : Route 9 := (fun mask => (mask,id))

def c8036 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8036 : Upper (D 8) (R 8) [6,96,264,160,192] 13 := by
  apply FastRouting.sound _ _ [6,96,264,160,192] 13 (by decide) (choices 1) [1,16] r8036 c8036
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1540
  · exact u1541

def b8037 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 292 25 25 224 224 224 480), lower := (rows 7 98 292 25 25 32 64 128 256), losses := [] }

theorem u8037 : Upper (D 8) (R 8) [6,96,288,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8038 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 292 25 49 232 200 200 456), lower := (rows 7 98 292 25 49 32 64 128 256), losses := [] }

theorem u8038 : Upper (D 8) (R 8) [6,96,288,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8038 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8039 : Route 9 := (fun mask => (mask,id))

def c8039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8039 : Upper (D 8) (R 8) [6,96,288,17,40] 13 := by
  apply FastRouting.sound _ _ [6,96,288,17,40] 13 (by decide) (choices 1) [1,64,128] r8039 c8039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1542
  · exact u1543
  · exact u1544

#print axioms u8039
end Delivery.IrregularNine14.P08
