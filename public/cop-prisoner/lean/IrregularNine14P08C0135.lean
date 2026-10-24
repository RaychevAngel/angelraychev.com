import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0026

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8100 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 388 73 176 57 121 185 313), lower := (rows 7 98 388 73 176 32 64 128 256), losses := [] }

theorem u8100 : Upper (D 8) (R 8) [6,96,384,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8101 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 388 88 145 41 105 169 297), lower := (rows 7 98 388 88 145 32 64 128 256), losses := [] }

theorem u8101 : Upper (D 8) (R 8) [6,96,384,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8102 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 388 88 152 33 97 161 289), lower := (rows 7 98 388 88 152 32 64 128 256), losses := [] }

theorem u8102 : Upper (D 8) (R 8) [6,96,384,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8103 : Route 9 := (fun mask => (mask,id))

def c8103 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8103 : Upper (D 8) (R 8) [6,96,384,80,160] 13 := by
  apply FastRouting.sound _ _ [6,96,384,80,160] 13 (by decide) (choices 1) [1,8] r8103 c8103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1596
  · exact u1597

def b8104 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 388 104 152 49 113 177 305), lower := (rows 7 98 388 104 152 32 64 128 256), losses := [] }

theorem u8104 : Upper (D 8) (R 8) [6,96,384,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8104 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8105 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 388 104 176 57 89 153 281), lower := (rows 7 98 388 104 176 32 64 128 256), losses := [] }

theorem u8105 : Upper (D 8) (R 8) [6,96,384,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8105 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8106 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 261 25 56 224 224 224 480), lower := (rows 7 194 261 25 56 32 64 128 256), losses := [] }

theorem u8106 : Upper (D 8) (R 8) [6,192,257,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8106 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8107 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6)], upper := (rows 7 194 261 25 88 160 224 160 416), lower := (rows 7 194 261 25 88 32 64 128 256), losses := [] }

theorem u8107 : Upper (D 8) (R 8) [6,192,257,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8107 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8108 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 261 25 112 168 232 168 424), lower := (rows 7 194 261 25 112 32 64 128 256), losses := [] }

theorem u8108 : Upper (D 8) (R 8) [6,192,257,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8109 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 261 41 56 240 240 240 496), lower := (rows 7 194 261 41 56 32 64 128 256), losses := [] }

theorem u8109 : Upper (D 8) (R 8) [6,192,257,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8110 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 261 41 88 176 240 176 432), lower := (rows 7 194 261 41 88 32 64 128 256), losses := [] }

theorem u8110 : Upper (D 8) (R 8) [6,192,257,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8110 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8111 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 261 41 112 184 248 184 440), lower := (rows 7 194 261 41 112 32 64 128 256), losses := [] }

theorem u8111 : Upper (D 8) (R 8) [6,192,257,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8112 : PairBound 9 := { available := 225, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 194 261 56 56 225 225 225 481), lower := (rows 7 194 261 56 56 32 64 128 256), losses := [] }

theorem u8112 : Upper (D 8) (R 8) [6,192,257,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8113 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 170, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 261 56 81 168 232 168 424), lower := (rows 7 194 261 56 81 32 64 128 256), losses := [] }

theorem u8113 : Upper (D 8) (R 8) [6,192,257,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8114 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6)], upper := (rows 7 194 261 56 88 161 225 161 417), lower := (rows 7 194 261 56 88 32 64 128 256), losses := [] }

theorem u8114 : Upper (D 8) (R 8) [6,192,257,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8114 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8115 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 194 261 56 112 169 233 169 425), lower := (rows 7 194 261 56 112 32 64 128 256), losses := [] }

theorem u8115 : Upper (D 8) (R 8) [6,192,257,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8116 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 194 261 56 208 41 105 169 297), lower := (rows 7 194 261 56 208 32 64 128 256), losses := [] }

theorem u8116 : Upper (D 8) (R 8) [6,192,257,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8117 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 261 73 152 48 112 176 304), lower := (rows 7 194 261 73 152 32 64 128 256), losses := [] }

theorem u8117 : Upper (D 8) (R 8) [6,192,257,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8118 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 261 73 176 56 120 184 312), lower := (rows 7 194 261 73 176 32 64 128 256), losses := [] }

theorem u8118 : Upper (D 8) (R 8) [6,192,257,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8119 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 194 261 88 152 33 97 161 289), lower := (rows 7 194 261 88 152 32 64 128 256), losses := [] }

theorem u8119 : Upper (D 8) (R 8) [6,192,257,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8120 : Route 9 := (fun mask => (mask,id))

def c8120 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8120 : Upper (D 8) (R 8) [6,192,257,80,160] 13 := by
  apply FastRouting.sound _ _ [6,192,257,80,160] 13 (by decide) (choices 1) [1,8] r8120 c8120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1598
  · exact u1599

theorem m8121_16 : Upper (D 8) (R 8) [6,192,257,96,160,16] 13 :=
  permutation_upper _ _ _ [6,192,257,96,160,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1601

def r8121 : Route 9 := (fun mask => (mask,id))

def c8121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8121 : Upper (D 8) (R 8) [6,192,257,96,160] 13 := by
  apply FastRouting.sound _ _ [6,192,257,96,160] 13 (by decide) (choices 1) [1,8,16] r8121 c8121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1600
  · exact u1601
  · exact m8121_16

def b8122 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 194 268 25 49 224 224 224 480), lower := (rows 7 194 268 25 49 32 64 128 256), losses := [] }

theorem u8122 : Upper (D 8) (R 8) [6,192,264,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8123 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 268 25 81 160 224 160 416), lower := (rows 7 194 268 25 81 32 64 128 256), losses := [] }

theorem u8123 : Upper (D 8) (R 8) [6,192,264,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8124 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 194 268 25 112 161 225 161 417), lower := (rows 7 194 268 25 112 32 64 128 256), losses := [] }

theorem u8124 : Upper (D 8) (R 8) [6,192,264,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8124 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8125 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 194 268 25 208 33 97 161 289), lower := (rows 7 194 268 25 208 32 64 128 256), losses := [] }

theorem u8125 : Upper (D 8) (R 8) [6,192,264,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8126 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 194 268 41 49 240 240 240 496), lower := (rows 7 194 268 41 49 32 64 128 256), losses := [] }

theorem u8126 : Upper (D 8) (R 8) [6,192,264,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8126 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8127 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 7 194 268 41 81 176 240 176 432), lower := (rows 7 194 268 41 81 32 64 128 256), losses := [] }

theorem u8127 : Upper (D 8) (R 8) [6,192,264,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8127 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8128 : Route 9 := (fun mask => (mask,id))

def c8128 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8128 : Upper (D 8) (R 8) [6,192,264,33,96] 13 := by
  apply FastRouting.sound _ _ [6,192,264,33,96] 13 (by decide) (choices 1) [1,16,128] r8128 c8128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1602
  · exact u1603
  · exact u1604

def b8129 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 194 268 41 208 49 113 177 305), lower := (rows 7 194 268 41 208 32 64 128 256), losses := [] }

theorem u8129 : Upper (D 8) (R 8) [6,192,264,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8130 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 194 268 56 49 225 225 225 481), lower := (rows 7 194 268 56 49 32 64 128 256), losses := [] }

theorem u8130 : Upper (D 8) (R 8) [6,192,264,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8130 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8131 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 7 194 268 56 81 161 225 161 417), lower := (rows 7 194 268 56 81 32 64 128 256), losses := [] }

theorem u8131 : Upper (D 8) (R 8) [6,192,264,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8132 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 194 268 56 112 161 225 161 417), lower := (rows 7 194 268 56 112 32 64 128 256), losses := [] }

theorem u8132 : Upper (D 8) (R 8) [6,192,264,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8133 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 194 268 56 208 33 97 161 289), lower := (rows 7 194 268 56 208 32 64 128 256), losses := [] }

theorem u8133 : Upper (D 8) (R 8) [6,192,264,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8134 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 7 194 292 25 25 224 224 224 480), lower := (rows 7 194 292 25 25 32 64 128 256), losses := [] }

theorem u8134 : Upper (D 8) (R 8) [6,192,288,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8135 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 194 292 25 49 232 232 232 488), lower := (rows 7 194 292 25 49 32 64 128 256), losses := [] }

theorem u8135 : Upper (D 8) (R 8) [6,192,288,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8135 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8136 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8136 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8136 : Upper (D 8) (R 8) [6,192,288,17,40] 13 := by
  apply FastRouting.sound _ _ [6,192,288,17,40] 13 (by decide) (choices 1) [1,64] r8136 c8136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1605
  · exact u1606

def b8137 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 292 25 81 168 232 168 424), lower := (rows 7 194 292 25 81 32 64 128 256), losses := [] }

theorem u8137 : Upper (D 8) (R 8) [6,192,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8138 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6)], upper := (rows 7 194 292 25 88 161 225 161 417), lower := (rows 7 194 292 25 88 32 64 128 256), losses := [] }

theorem u8138 : Upper (D 8) (R 8) [6,192,288,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8139 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 194 292 25 112 169 233 169 425), lower := (rows 7 194 292 25 112 32 64 128 256), losses := [] }

theorem u8139 : Upper (D 8) (R 8) [6,192,288,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8139 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8140 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 194 292 25 208 41 105 169 297), lower := (rows 7 194 292 25 208 32 64 128 256), losses := [] }

theorem u8140 : Upper (D 8) (R 8) [6,192,288,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8141 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 194 292 41 49 248 216 216 472), lower := (rows 7 194 292 41 49 32 64 128 256), losses := [] }

theorem u8141 : Upper (D 8) (R 8) [6,192,288,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8142 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 194 292 41 56 241 209 209 465), lower := (rows 7 194 292 41 56 32 64 128 256), losses := [] }

theorem u8142 : Upper (D 8) (R 8) [6,192,288,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8142 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8143 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 7 194 292 41 81 184 248 184 440), lower := (rows 7 194 292 41 81 32 64 128 256), losses := [] }

theorem u8143 : Upper (D 8) (R 8) [6,192,288,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8144 : Route 9 := (fun mask => (mask,id))

def c8144 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8144 : Upper (D 8) (R 8) [6,192,288,33,72] 13 := by
  apply FastRouting.sound _ _ [6,192,288,33,72] 13 (by decide) (choices 1) [1,16,128] r8144 c8144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1607
  · exact u1608
  · exact u1609

def r8145 : Route 9 := (fun mask => (mask,id))

def c8145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8145 : Upper (D 8) (R 8) [6,192,288,33,96] 13 := by
  apply FastRouting.sound _ _ [6,192,288,33,96] 13 (by decide) (choices 1) [1,8,16,128] r8145 c8145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1610
  · exact u1611
  · exact u1612
  · exact u1613

def b8146 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 194 292 41 208 57 121 185 313), lower := (rows 7 194 292 41 208 32 64 128 256), losses := [] }

theorem u8146 : Upper (D 8) (R 8) [6,192,288,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8146 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8147 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 194 292 56 56 225 193 193 449), lower := (rows 7 194 292 56 56 32 64 128 256), losses := [] }

theorem u8147 : Upper (D 8) (R 8) [6,192,288,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8148 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 7 194 292 56 81 169 233 169 425), lower := (rows 7 194 292 56 81 32 64 128 256), losses := [] }

theorem u8148 : Upper (D 8) (R 8) [6,192,288,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8148 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8149 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6)], upper := (rows 7 194 292 56 88 161 225 161 417), lower := (rows 7 194 292 56 88 32 64 128 256), losses := [] }

theorem u8149 : Upper (D 8) (R 8) [6,192,288,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8150 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 194 292 56 112 169 201 137 393), lower := (rows 7 194 292 56 112 32 64 128 256), losses := [] }

theorem u8150 : Upper (D 8) (R 8) [6,192,288,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8151 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 194 292 56 208 41 105 169 297), lower := (rows 7 194 292 56 208 32 64 128 256), losses := [] }

theorem u8151 : Upper (D 8) (R 8) [6,192,288,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8152 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 194 292 73 152 49 113 177 305), lower := (rows 7 194 292 73 152 32 64 128 256), losses := [] }

theorem u8152 : Upper (D 8) (R 8) [6,192,288,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8153 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 7 194 292 73 176 57 121 185 313), lower := (rows 7 194 292 73 176 32 64 128 256), losses := [] }

theorem u8153 : Upper (D 8) (R 8) [6,192,288,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8154 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 194 292 88 152 33 97 161 289), lower := (rows 7 194 292 88 152 32 64 128 256), losses := [] }

theorem u8154 : Upper (D 8) (R 8) [6,192,288,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8155 : Route 9 := (fun mask => (mask,id))

def c8155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8155 : Upper (D 8) (R 8) [6,192,288,80,160] 13 := by
  apply FastRouting.sound _ _ [6,192,288,80,160] 13 (by decide) (choices 1) [1,8] r8155 c8155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1614
  · exact u1615

theorem m8156_16 : Upper (D 8) (R 8) [6,192,288,96,160,16] 13 :=
  permutation_upper _ _ _ [6,192,288,96,160,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1617

def r8156 : Route 9 := (fun mask => (mask,id))

def c8156 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8156 : Upper (D 8) (R 8) [6,192,288,96,160] 13 := by
  apply FastRouting.sound _ _ [6,192,288,96,160] 13 (by decide) (choices 1) [1,8,16] r8156 c8156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1616
  · exact u1617
  · exact m8156_16

def b8157 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 15, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 41 112 480 448 448 448), lower := (rows 35 7 28 41 112 32 64 128 256), losses := [] }

theorem u8157 : Upper (D 8) (R 8) [34,5,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8158 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 28 41 208 480 480 480 480), lower := (rows 35 7 28 41 208 32 64 128 256), losses := [] }

theorem u8158 : Upper (D 8) (R 8) [34,5,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8159 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 15, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 41 304 224 192 192 448), lower := (rows 35 7 28 41 304 32 64 128 256), losses := [] }

theorem u8159 : Upper (D 8) (R 8) [34,5,24,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8159 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u8159
end Delivery.IrregularNine14.P08
