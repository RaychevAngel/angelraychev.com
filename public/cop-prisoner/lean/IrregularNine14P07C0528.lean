import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0240
import IrregularNine14P07C0241
import IrregularNine14P07C0242

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r31680 : Route 9 := (fun mask => (mask,id))

def c31680 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31680 : Upper (D 7) (R 7) [6,96,264,129,33] 13 := by
  apply FastRouting.sound _ _ [6,96,264,129,33] 13 (by decide) (choices 1) [2,16,64,128] r31680 c31680
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14448
  · exact u14449
  · exact u14450
  · exact u14451

def b31681 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 98 268 137 50 241 209 209 465), lower := (rows 7 98 268 137 50 32 64 128 256), losses := [] }

theorem u31681 : Upper (D 7) (R 7) [6,96,264,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31682 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 268 137 112 179 211 147 403), lower := (rows 7 98 268 137 112 32 64 128 256), losses := [] }

theorem u31682 : Upper (D 7) (R 7) [6,96,264,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31683 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 7 98 268 137 145 114 114 242 370), lower := (rows 7 98 268 137 145 32 64 128 256), losses := [] }

theorem u31683 : Upper (D 7) (R 7) [6,96,264,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31684 : Route 9 := (fun mask => (mask,id))

def c31684 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31684 : Upper (D 7) (R 7) [6,96,264,129,130] 13 := by
  apply FastRouting.sound _ _ [6,96,264,129,130] 13 (by decide) (choices 1) [1,16,64] r31684 c31684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14452
  · exact u14453
  · exact u14454

def r31685 : Route 9 := (fun mask => (mask,id))

def c31685 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31685 : Upper (D 7) (R 7) [6,96,264,129,160] 13 := by
  apply FastRouting.sound _ _ [6,96,264,129,160] 13 (by decide) (choices 1) [1,2,16,64] r31685 c31685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14455
  · exact u14456
  · exact u14457
  · exact u14458

def r31686 : Route 9 := (fun mask => (mask,id))

def c31686 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31686 : Upper (D 7) (R 7) [6,96,264,130,33] 13 := by
  apply FastRouting.sound _ _ [6,96,264,130,33] 13 (by decide) (choices 1) [1,16,64,128] r31686 c31686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14459
  · exact u14460
  · exact u14461
  · exact u14462

def b31687 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 268 138 112 177 209 145 401), lower := (rows 7 98 268 138 112 32 64 128 256), losses := [] }

theorem u31687 : Upper (D 7) (R 7) [6,96,264,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31688 : Route 9 := (fun mask => (mask,id))

def c31688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31688 : Upper (D 7) (R 7) [6,96,264,130,129] 13 := by
  apply FastRouting.sound _ _ [6,96,264,130,129] 13 (by decide) (choices 1) [1,16,64] r31688 c31688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14463
  · exact u14464
  · exact u14465

def r31689 : Route 9 := (fun mask => (mask,id))

def c31689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31689 : Upper (D 7) (R 7) [6,96,264,130,160] 13 := by
  apply FastRouting.sound _ _ [6,96,264,130,160] 13 (by decide) (choices 1) [1,16,64] r31689 c31689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14466
  · exact u14467
  · exact u14468

def b31690 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 7 98 268 152 19 225 225 225 481), lower := (rows 7 98 268 152 19 32 64 128 256), losses := [] }

theorem u31690 : Upper (D 7) (R 7) [6,96,264,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31691 : Route 9 := (fun mask => (mask,id))

def c31691 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31691 : Upper (D 7) (R 7) [6,96,264,144,33] 13 := by
  apply FastRouting.sound _ _ [6,96,264,144,33] 13 (by decide) (choices 1) [1,2,64,128] r31691 c31691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14469
  · exact u14470
  · exact u14471
  · exact u14472

def b31692 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 98 268 152 50 225 193 193 449), lower := (rows 7 98 268 152 50 32 64 128 256), losses := [] }

theorem u31692 : Upper (D 7) (R 7) [6,96,264,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31693 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 268 152 112 163 195 131 387), lower := (rows 7 98 268 152 112 32 64 128 256), losses := [] }

theorem u31693 : Upper (D 7) (R 7) [6,96,264,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31694 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 98 268 152 145 99 99 227 355), lower := (rows 7 98 268 152 145 32 64 128 256), losses := [] }

theorem u31694 : Upper (D 7) (R 7) [6,96,264,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31695 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 98 268 152 146 97 97 225 353), lower := (rows 7 98 268 152 146 32 64 128 256), losses := [] }

theorem u31695 : Upper (D 7) (R 7) [6,96,264,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31696 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 98 268 152 176 99 67 195 323), lower := (rows 7 98 268 152 176 32 64 128 256), losses := [] }

theorem u31696 : Upper (D 7) (R 7) [6,96,264,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31697 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 492, targets := 2 }], pairs := [(2,1),(3,1),(4,6),(4,7)], upper := (rows 7 98 268 168 19 241 209 209 465), lower := (rows 7 98 268 168 19 32 64 128 256), losses := [] }

theorem u31697 : Upper (D 7) (R 7) [6,96,264,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31698 : Route 9 := (fun mask => (mask,id))

def c31698 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31698 : Upper (D 7) (R 7) [6,96,264,160,65] 13 := by
  apply FastRouting.sound _ _ [6,96,264,160,65] 13 (by decide) (choices 1) [1,2,16,128] r31698 c31698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14473
  · exact u14474
  · exact u14475
  · exact u14476

def b31699 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 268 168 82 177 209 145 401), lower := (rows 7 98 268 168 82 32 64 128 256), losses := [] }

theorem u31699 : Upper (D 7) (R 7) [6,96,264,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31700 : Route 9 := (fun mask => (mask,id))

def c31700 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31700 : Upper (D 7) (R 7) [6,96,264,160,129] 13 := by
  apply FastRouting.sound _ _ [6,96,264,160,129] 13 (by decide) (choices 1) [1,2,16,64] r31700 c31700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14477
  · exact u14478
  · exact u14479
  · exact u14480

def r31701 : Route 9 := (fun mask => (mask,id))

def c31701 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31701 : Upper (D 7) (R 7) [6,96,264,160,130] 13 := by
  apply FastRouting.sound _ _ [6,96,264,160,130] 13 (by decide) (choices 1) [1,16,64] r31701 c31701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14481
  · exact u14482
  · exact u14483

def r31702 : Route 9 := (fun mask => (mask,id))

def c31702 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31702 : Upper (D 7) (R 7) [6,96,264,160,192] 13 := by
  apply FastRouting.sound _ _ [6,96,264,160,192] 13 (by decide) (choices 1) [1,2,16] r31702 c31702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14484
  · exact u14485
  · exact u14486

def b31703 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 98 292 11 25 240 208 208 464), lower := (rows 7 98 292 11 25 32 64 128 256), losses := [] }

theorem u31703 : Upper (D 7) (R 7) [6,96,288,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31704 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 292 11 81 184 216 152 408), lower := (rows 7 98 292 11 81 32 64 128 256), losses := [] }

theorem u31704 : Upper (D 7) (R 7) [6,96,288,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31705 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 292 11 88 177 209 145 401), lower := (rows 7 98 292 11 88 32 64 128 256), losses := [] }

theorem u31705 : Upper (D 7) (R 7) [6,96,288,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31706 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 292 11 145 248 216 216 472), lower := (rows 7 98 292 11 145 32 64 128 256), losses := [] }

theorem u31706 : Upper (D 7) (R 7) [6,96,288,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31707 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 292 11 152 241 209 209 465), lower := (rows 7 98 292 11 152 32 64 128 256), losses := [] }

theorem u31707 : Upper (D 7) (R 7) [6,96,288,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31708 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 292 11 208 185 217 153 409), lower := (rows 7 98 292 11 208 32 64 128 256), losses := [] }

theorem u31708 : Upper (D 7) (R 7) [6,96,288,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31709 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 7 98 292 25 25 226 194 194 450), lower := (rows 7 98 292 25 25 32 64 128 256), losses := [] }

theorem u31709 : Upper (D 7) (R 7) [6,96,288,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31710 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 98 292 25 26 225 193 193 449), lower := (rows 7 98 292 25 26 32 64 128 256), losses := [] }

theorem u31710 : Upper (D 7) (R 7) [6,96,288,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31711 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 292 25 81 170 202 138 394), lower := (rows 7 98 292 25 81 32 64 128 256), losses := [] }

theorem u31711 : Upper (D 7) (R 7) [6,96,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31712 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 292 25 82 169 201 137 393), lower := (rows 7 98 292 25 82 32 64 128 256), losses := [] }

theorem u31712 : Upper (D 7) (R 7) [6,96,288,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31713 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 292 25 88 163 195 131 387), lower := (rows 7 98 292 25 88 32 64 128 256), losses := [] }

theorem u31713 : Upper (D 7) (R 7) [6,96,288,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31714 : PairBound 9 := { available := 202, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 292 25 145 234 202 202 458), lower := (rows 7 98 292 25 145 32 64 128 256), losses := [] }

theorem u31714 : Upper (D 7) (R 7) [6,96,288,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31715 : Route 9 := (fun mask => (mask,id))

def c31715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31715 : Upper (D 7) (R 7) [6,96,288,17,130] 13 := by
  apply FastRouting.sound _ _ [6,96,288,17,130] 13 (by decide) (choices 1) [1,8,64,128] r31715 c31715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14487
  · exact u14488
  · exact u14489
  · exact u14490

def r31716 : Route 9 := (fun mask => (mask,id))

def c31716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31716 : Upper (D 7) (R 7) [6,96,288,17,136] 13 := by
  apply FastRouting.sound _ _ [6,96,288,17,136] 13 (by decide) (choices 1) [1,2,64,128] r31716 c31716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14491
  · exact u14492
  · exact u14493
  · exact u14494

def r31717 : Route 9 := (fun mask => (mask,id))

def c31717 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31717 : Upper (D 7) (R 7) [6,96,288,17,192] 13 := by
  apply FastRouting.sound _ _ [6,96,288,17,192] 13 (by decide) (choices 1) [1,2,8,128] r31717 c31717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14495
  · exact u14496
  · exact u14497
  · exact u14498

def b31718 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 292 26 81 169 201 137 393), lower := (rows 7 98 292 26 81 32 64 128 256), losses := [] }

theorem u31718 : Upper (D 7) (R 7) [6,96,288,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31719 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 7 98 292 26 88 161 193 129 385), lower := (rows 7 98 292 26 88 32 64 128 256), losses := [] }

theorem u31719 : Upper (D 7) (R 7) [6,96,288,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31719 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31720 : Route 9 := (fun mask => (mask,id))

def c31720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31720 : Upper (D 7) (R 7) [6,96,288,18,129] 13 := by
  apply FastRouting.sound _ _ [6,96,288,18,129] 13 (by decide) (choices 1) [1,8,64,128] r31720 c31720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14499
  · exact u14500
  · exact u14501
  · exact u14502

def r31721 : Route 9 := (fun mask => (mask,id))

def c31721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31721 : Upper (D 7) (R 7) [6,96,288,18,136] 13 := by
  apply FastRouting.sound _ _ [6,96,288,18,136] 13 (by decide) (choices 1) [1,64,128] r31721 c31721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14503
  · exact u14504
  · exact u14505

def b31722 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 292 26 208 169 201 137 393), lower := (rows 7 98 292 26 208 32 64 128 256), losses := [] }

theorem u31722 : Upper (D 7) (R 7) [6,96,288,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31723 : Route 9 := (fun mask => (mask,id))

def c31723 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31723 : Upper (D 7) (R 7) [6,96,288,65,129] 13 := by
  apply FastRouting.sound _ _ [6,96,288,65,129] 13 (by decide) (choices 1) [2,8,16,128] r31723 c31723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14506
  · exact u14507
  · exact u14508
  · exact u14509

def r31724 : Route 9 := (fun mask => (mask,id))

def c31724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31724 : Upper (D 7) (R 7) [6,96,288,65,130] 13 := by
  apply FastRouting.sound _ _ [6,96,288,65,130] 13 (by decide) (choices 1) [1,8,16,128] r31724 c31724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14510
  · exact u14511
  · exact u14512
  · exact u14513

def r31725 : Route 9 := (fun mask => (mask,id))

def c31725 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31725 : Upper (D 7) (R 7) [6,96,288,65,136] 13 := by
  apply FastRouting.sound _ _ [6,96,288,65,136] 13 (by decide) (choices 1) [1,2,16,128] r31725 c31725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14514
  · exact u14515
  · exact u14516
  · exact u14517

def b31726 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 7 98 292 74 145 185 217 153 409), lower := (rows 7 98 292 74 145 32 64 128 256), losses := [] }

theorem u31726 : Upper (D 7) (R 7) [6,96,288,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31727 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 7 98 292 74 152 177 209 145 401), lower := (rows 7 98 292 74 152 32 64 128 256), losses := [] }

theorem u31727 : Upper (D 7) (R 7) [6,96,288,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31728 : Route 9 := (fun mask => (mask,id))

def c31728 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31728 : Upper (D 7) (R 7) [6,96,288,80,129] 13 := by
  apply FastRouting.sound _ _ [6,96,288,80,129] 13 (by decide) (choices 1) [1,2,8,128] r31728 c31728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14518
  · exact u14519
  · exact u14520
  · exact u14521

def r31729 : Route 9 := (fun mask => (mask,id))

def c31729 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31729 : Upper (D 7) (R 7) [6,96,288,80,130] 13 := by
  apply FastRouting.sound _ _ [6,96,288,80,130] 13 (by decide) (choices 1) [1,8,128] r31729 c31729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14522
  · exact u14523
  · exact u14524

def b31730 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 7 98 292 88 152 163 195 131 387), lower := (rows 7 98 292 88 152 32 64 128 256), losses := [] }

theorem u31730 : Upper (D 7) (R 7) [6,96,288,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31731 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 7 98 292 137 145 122 90 218 346), lower := (rows 7 98 292 137 145 32 64 128 256), losses := [] }

theorem u31731 : Upper (D 7) (R 7) [6,96,288,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31732 : Route 9 := (fun mask => (mask,id))

def c31732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31732 : Upper (D 7) (R 7) [6,96,288,129,130] 13 := by
  apply FastRouting.sound _ _ [6,96,288,129,130] 13 (by decide) (choices 1) [1,8,16,64] r31732 c31732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14525
  · exact u14526
  · exact u14527
  · exact u14528

def b31733 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 7 98 292 137 152 115 83 211 339), lower := (rows 7 98 292 137 152 32 64 128 256), losses := [] }

theorem u31733 : Upper (D 7) (R 7) [6,96,288,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31734 : Route 9 := (fun mask => (mask,id))

def c31734 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31734 : Upper (D 7) (R 7) [6,96,288,129,192] 13 := by
  apply FastRouting.sound _ _ [6,96,288,129,192] 13 (by decide) (choices 1) [1,2,8,16] r31734 c31734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14529
  · exact u14530
  · exact u14531
  · exact u14532

def b31735 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 7 98 292 138 152 113 81 209 337), lower := (rows 7 98 292 138 152 32 64 128 256), losses := [] }

theorem u31735 : Upper (D 7) (R 7) [6,96,288,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31736 : Route 9 := (fun mask => (mask,id))

def c31736 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31736 : Upper (D 7) (R 7) [6,96,288,130,192] 13 := by
  apply FastRouting.sound _ _ [6,96,288,130,192] 13 (by decide) (choices 1) [1,8,16] r31736 c31736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14533
  · exact u14534
  · exact u14535

def b31737 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 98 292 152 152 99 67 195 323), lower := (rows 7 98 292 152 152 32 64 128 256), losses := [] }

theorem u31737 : Upper (D 7) (R 7) [6,96,288,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31738 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 98 292 152 208 43 75 139 267), lower := (rows 7 98 292 152 208 32 64 128 256), losses := [] }

theorem u31738 : Upper (D 7) (R 7) [6,96,288,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31739 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 7 98 388 11 25 240 240 240 496), lower := (rows 7 98 388 11 25 32 64 128 256), losses := [] }

theorem u31739 : Upper (D 7) (R 7) [6,96,384,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u31739
end Delivery.IrregularNine14.P07
