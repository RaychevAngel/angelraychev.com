import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0432
import IrregularNine14P07C0433
import IrregularNine14P07C0434

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b38580 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,5),(1,6),(4,5)], upper := (rows 37 259 76 56 82 163 195 131 387), lower := (rows 37 259 76 56 82 32 64 128 256), losses := [] }

theorem u38580 : Upper (D 7) (R 7) [36,257,72,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38581 : Route 9 := (fun mask => (mask,id))

def c38581 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38581 : Upper (D 7) (R 7) [36,257,72,48,129] 13 := by
  apply FastRouting.sound _ _ [36,257,72,48,129] 13 (by decide) (choices 1) [2,64,128] r38581 c38581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25973
  · exact u25974
  · exact u25975

def r38582 : Route 9 := (fun mask => (mask,id))

def c38582 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38582 : Upper (D 7) (R 7) [36,257,72,48,130] 13 := by
  apply FastRouting.sound _ _ [36,257,72,48,130] 13 (by decide) (choices 1) [1,2,64,128] r38582 c38582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25976
  · exact u25977
  · exact u25978
  · exact u25979

def b38583 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,5),(1,6),(4,5)], upper := (rows 37 259 76 56 208 163 195 131 387), lower := (rows 37 259 76 56 208 32 64 128 256), losses := [] }

theorem u38583 : Upper (D 7) (R 7) [36,257,72,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38584 : Route 9 := (fun mask => (mask,id))

def c38584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38584 : Upper (D 7) (R 7) [36,257,72,129,34] 13 := by
  apply FastRouting.sound _ _ [36,257,72,129,34] 13 (by decide) (choices 1) [2,16,64,128] r38584 c38584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25980
  · exact u25981
  · exact u25982
  · exact u25983

def r38585 : Route 9 := (fun mask => (mask,id))

def c38585 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38585 : Upper (D 7) (R 7) [36,257,72,129,66] 13 := by
  apply FastRouting.sound _ _ [36,257,72,129,66] 13 (by decide) (choices 1) [2,16,128] r38585 c38585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25984
  · exact u25985
  · exact u25986

def r38586 : Route 9 := (fun mask => (mask,id))

def c38586 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38586 : Upper (D 7) (R 7) [36,257,72,129,96] 13 := by
  apply FastRouting.sound _ _ [36,257,72,129,96] 13 (by decide) (choices 1) [2,16,128] r38586 c38586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25987
  · exact u25988
  · exact u25989

def r38587 : Route 9 := (fun mask => (mask,id))

def c38587 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38587 : Upper (D 7) (R 7) [36,257,72,129,130] 13 := by
  apply FastRouting.sound _ _ [36,257,72,129,130] 13 (by decide) (choices 1) [2,16,64] r38587 c38587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25990
  · exact u25991
  · exact u25992

def r38588 : Route 9 := (fun mask => (mask,id))

def c38588 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38588 : Upper (D 7) (R 7) [36,257,72,129,160] 13 := by
  apply FastRouting.sound _ _ [36,257,72,129,160] 13 (by decide) (choices 1) [2,16,64] r38588 c38588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u25993
  · exact u25994
  · exact u25995

def r38589 : Route 9 := (fun mask => (mask,id))

def c38589 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38589 : Upper (D 7) (R 7) [36,257,72,129,192] 13 := by
  apply FastRouting.sound _ _ [36,257,72,129,192] 13 (by decide) (choices 1) [2,16] r38589 c38589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u25996
  · exact u25997

def b38590 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 16, targets := 224 },{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0),(4,5),(4,6),(4,7)], upper := (rows 37 259 76 138 19 240 240 240 496), lower := (rows 37 259 76 138 19 32 64 128 256), losses := [] }

theorem u38590 : Upper (D 7) (R 7) [36,257,72,130,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38591 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 259 76 138 49 242 210 210 466), lower := (rows 37 259 76 138 49 32 64 128 256), losses := [] }

theorem u38591 : Upper (D 7) (R 7) [36,257,72,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38592 : Route 9 := (fun mask => (mask,id))

def c38592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38592 : Upper (D 7) (R 7) [36,257,72,130,34] 13 := by
  apply FastRouting.sound _ _ [36,257,72,130,34] 13 (by decide) (choices 1) [1,16,64,128] r38592 c38592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u25998
  · exact u25999
  · exact u26000
  · exact u26001

def r38593 : Route 9 := (fun mask => (mask,id))

def c38593 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38593 : Upper (D 7) (R 7) [36,257,72,130,65] 13 := by
  apply FastRouting.sound _ _ [36,257,72,130,65] 13 (by decide) (choices 1) [2,16,128] r38593 c38593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26002
  · exact u26003
  · exact u26004

def r38594 : Route 9 := (fun mask => (mask,id))

def c38594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38594 : Upper (D 7) (R 7) [36,257,72,130,66] 13 := by
  apply FastRouting.sound _ _ [36,257,72,130,66] 13 (by decide) (choices 1) [1,16,128] r38594 c38594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26005
  · exact u26006
  · exact u26007

def r38595 : Route 9 := (fun mask => (mask,id))

def c38595 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38595 : Upper (D 7) (R 7) [36,257,72,130,96] 13 := by
  apply FastRouting.sound _ _ [36,257,72,130,96] 13 (by decide) (choices 1) [1,2,16,128] r38595 c38595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26008
  · exact u26009
  · exact u26010
  · exact u26011

def r38596 : Route 9 := (fun mask => (mask,id))

def c38596 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38596 : Upper (D 7) (R 7) [36,257,72,130,129] 13 := by
  apply FastRouting.sound _ _ [36,257,72,130,129] 13 (by decide) (choices 1) [2,16,64] r38596 c38596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26012
  · exact u26013
  · exact u26014

def b38597 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 259 76 138 146 113 113 241 369), lower := (rows 37 259 76 138 146 32 64 128 256), losses := [] }

theorem u38597 : Upper (D 7) (R 7) [36,257,72,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38598 : Route 9 := (fun mask => (mask,id))

def c38598 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38598 : Upper (D 7) (R 7) [36,257,72,130,160] 13 := by
  apply FastRouting.sound _ _ [36,257,72,130,160] 13 (by decide) (choices 1) [1,2,16,64] r38598 c38598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26015
  · exact u26016
  · exact u26017
  · exact u26018

def r38599 : Route 9 := (fun mask => (mask,id))

def c38599 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38599 : Upper (D 7) (R 7) [36,257,72,130,192] 13 := by
  apply FastRouting.sound _ _ [36,257,72,130,192] 13 (by decide) (choices 1) [1,2,16] r38599 c38599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26019
  · exact u26020
  · exact u26021

def b38600 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 16, targets := 224 },{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0),(4,5),(4,6),(4,7)], upper := (rows 37 259 76 152 19 226 226 226 482), lower := (rows 37 259 76 152 19 32 64 128 256), losses := [] }

theorem u38600 : Upper (D 7) (R 7) [36,257,72,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38601 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 259 76 152 49 226 194 194 450), lower := (rows 37 259 76 152 49 32 64 128 256), losses := [] }

theorem u38601 : Upper (D 7) (R 7) [36,257,72,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38602 : Route 9 := (fun mask => (mask,id))

def c38602 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38602 : Upper (D 7) (R 7) [36,257,72,144,34] 13 := by
  apply FastRouting.sound _ _ [36,257,72,144,34] 13 (by decide) (choices 1) [1,2,64,128] r38602 c38602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26022
  · exact u26023
  · exact u26024
  · exact u26025

def r38603 : Route 9 := (fun mask => (mask,id))

def c38603 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38603 : Upper (D 7) (R 7) [36,257,72,144,65] 13 := by
  apply FastRouting.sound _ _ [36,257,72,144,65] 13 (by decide) (choices 1) [2,128] r38603 c38603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26026
  · exact u26027

def r38604 : Route 9 := (fun mask => (mask,id))

def c38604 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38604 : Upper (D 7) (R 7) [36,257,72,144,66] 13 := by
  apply FastRouting.sound _ _ [36,257,72,144,66] 13 (by decide) (choices 1) [1,2,128] r38604 c38604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26028
  · exact u26029
  · exact u26030

def r38605 : Route 9 := (fun mask => (mask,id))

def c38605 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38605 : Upper (D 7) (R 7) [36,257,72,144,96] 13 := by
  apply FastRouting.sound _ _ [36,257,72,144,96] 13 (by decide) (choices 1) [1,2,128] r38605 c38605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26031
  · exact u26032
  · exact u26033

def b38606 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 259 76 152 145 98 98 226 354), lower := (rows 37 259 76 152 145 32 64 128 256), losses := [] }

theorem u38606 : Upper (D 7) (R 7) [36,257,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38607 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 259 76 152 146 99 99 227 355), lower := (rows 37 259 76 152 146 32 64 128 256), losses := [] }

theorem u38607 : Upper (D 7) (R 7) [36,257,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38608 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 259 76 152 176 99 67 195 323), lower := (rows 37 259 76 152 176 32 64 128 256), losses := [] }

theorem u38608 : Upper (D 7) (R 7) [36,257,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38609 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5),(3,0)], upper := (rows 37 259 76 152 208 35 99 163 291), lower := (rows 37 259 76 152 208 32 64 128 256), losses := [] }

theorem u38609 : Upper (D 7) (R 7) [36,257,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38610 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 16, targets := 192 }], pairs := [(1,5),(4,5),(4,6),(4,7)], upper := (rows 37 259 76 168 19 242 210 210 466), lower := (rows 37 259 76 168 19 32 64 128 256), losses := [] }

theorem u38610 : Upper (D 7) (R 7) [36,257,72,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38611 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,5),(1,6),(3,6),(4,5)], upper := (rows 37 259 76 168 81 178 210 146 402), lower := (rows 37 259 76 168 81 32 64 128 256), losses := [] }

theorem u38611 : Upper (D 7) (R 7) [36,257,72,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38612 : Route 9 := (fun mask => (mask,id))

def c38612 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38612 : Upper (D 7) (R 7) [36,257,72,160,66] 13 := by
  apply FastRouting.sound _ _ [36,257,72,160,66] 13 (by decide) (choices 1) [1,2,16,128] r38612 c38612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26034
  · exact u26035
  · exact u26036
  · exact u26037

def r38613 : Route 9 := (fun mask => (mask,id))

def c38613 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38613 : Upper (D 7) (R 7) [36,257,72,160,129] 13 := by
  apply FastRouting.sound _ _ [36,257,72,160,129] 13 (by decide) (choices 1) [2,16,64] r38613 c38613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26038
  · exact u26039
  · exact u26040

def r38614 : Route 9 := (fun mask => (mask,id))

def c38614 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38614 : Upper (D 7) (R 7) [36,257,72,160,130] 13 := by
  apply FastRouting.sound _ _ [36,257,72,160,130] 13 (by decide) (choices 1) [1,2,16,64] r38614 c38614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26041
  · exact u26042
  · exact u26043
  · exact u26044

def r38615 : Route 9 := (fun mask => (mask,id))

def c38615 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38615 : Upper (D 7) (R 7) [36,257,72,160,192] 13 := by
  apply FastRouting.sound _ _ [36,257,72,160,192] 13 (by decide) (choices 1) [1,2,16] r38615 c38615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26045
  · exact u26046
  · exact u26047

def b38616 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 37 259 196 11 26 240 240 240 496), lower := (rows 37 259 196 11 26 32 64 128 256), losses := [] }

theorem u38616 : Upper (D 7) (R 7) [36,257,192,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38617 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 196 11 50 248 216 216 472), lower := (rows 37 259 196 11 50 32 64 128 256), losses := [] }

theorem u38617 : Upper (D 7) (R 7) [36,257,192,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38618 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 196 11 56 242 210 210 466), lower := (rows 37 259 196 11 56 32 64 128 256), losses := [] }

theorem u38618 : Upper (D 7) (R 7) [36,257,192,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38619 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 196 11 82 184 248 184 440), lower := (rows 37 259 196 11 82 32 64 128 256), losses := [] }

theorem u38619 : Upper (D 7) (R 7) [36,257,192,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38620 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 196 11 88 178 242 178 434), lower := (rows 37 259 196 11 88 32 64 128 256), losses := [] }

theorem u38620 : Upper (D 7) (R 7) [36,257,192,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38621 : PairBound 9 := { available := 154, camps := [{ cop := 1, region := 8, targets := 224 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 196 11 112 186 218 154 410), lower := (rows 37 259 196 11 112 32 64 128 256), losses := [] }

theorem u38621 : Upper (D 7) (R 7) [36,257,192,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38622 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 37 259 196 25 26 226 226 226 482), lower := (rows 37 259 196 25 26 32 64 128 256), losses := [] }

theorem u38622 : Upper (D 7) (R 7) [36,257,192,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38623 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38623 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38623 : Upper (D 7) (R 7) [36,257,192,17,34] 13 := by
  apply FastRouting.sound _ _ [36,257,192,17,34] 13 (by decide) (choices 1) [2,8,64] r38623 c38623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26048
  · exact u26049
  · exact u26050

def b38624 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 259 196 25 56 226 194 194 450), lower := (rows 37 259 196 25 56 32 64 128 256), losses := [] }

theorem u38624 : Upper (D 7) (R 7) [36,257,192,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38625 : Route 9 := (fun mask => (mask,id))

def c38625 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38625 : Upper (D 7) (R 7) [36,257,192,17,66] 13 := by
  apply FastRouting.sound _ _ [36,257,192,17,66] 13 (by decide) (choices 1) [2,8,128] r38625 c38625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26051
  · exact u26052
  · exact u26053

def r38626 : Route 9 := (fun mask => (mask,id))

def c38626 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38626 : Upper (D 7) (R 7) [36,257,192,17,72] 13 := by
  apply FastRouting.sound _ _ [36,257,192,17,72] 13 (by decide) (choices 1) [2,128] r38626 c38626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26054
  · exact u26055

def r38627 : Route 9 := (fun mask => (mask,id))

def c38627 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38627 : Upper (D 7) (R 7) [36,257,192,17,96] 13 := by
  apply FastRouting.sound _ _ [36,257,192,17,96] 13 (by decide) (choices 1) [2,8,128] r38627 c38627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26056
  · exact u26057
  · exact u26058

def b38628 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 37 259 196 25 208 42 106 170 298), lower := (rows 37 259 196 25 208 32 64 128 256), losses := [] }

theorem u38628 : Upper (D 7) (R 7) [36,257,192,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38629 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 196 26 26 225 225 225 481), lower := (rows 37 259 196 26 26 32 64 128 256), losses := [] }

theorem u38629 : Upper (D 7) (R 7) [36,257,192,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38629 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38630 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 259 196 26 49 234 202 202 458), lower := (rows 37 259 196 26 49 32 64 128 256), losses := [] }

theorem u38630 : Upper (D 7) (R 7) [36,257,192,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38631 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 196 26 50 233 201 201 457), lower := (rows 37 259 196 26 50 32 64 128 256), losses := [] }

theorem u38631 : Upper (D 7) (R 7) [36,257,192,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38632 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38632 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38632 : Upper (D 7) (R 7) [36,257,192,18,40] 13 := by
  apply FastRouting.sound _ _ [36,257,192,18,40] 13 (by decide) (choices 1) [1,2,64] r38632 c38632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26059
  · exact u26060
  · exact u26061

def r38633 : Route 9 := (fun mask => (mask,id))

def c38633 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38633 : Upper (D 7) (R 7) [36,257,192,18,65] 13 := by
  apply FastRouting.sound _ _ [36,257,192,18,65] 13 (by decide) (choices 1) [2,8,128] r38633 c38633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26062
  · exact u26063
  · exact u26064

def b38634 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 259 196 26 82 169 233 169 425), lower := (rows 37 259 196 26 82 32 64 128 256), losses := [] }

theorem u38634 : Upper (D 7) (R 7) [36,257,192,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38635 : Route 9 := (fun mask => (mask,id))

def c38635 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38635 : Upper (D 7) (R 7) [36,257,192,18,72] 13 := by
  apply FastRouting.sound _ _ [36,257,192,18,72] 13 (by decide) (choices 1) [1,2,128] r38635 c38635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26065
  · exact u26066
  · exact u26067

def r38636 : Route 9 := (fun mask => (mask,id))

def c38636 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38636 : Upper (D 7) (R 7) [36,257,192,18,96] 13 := by
  apply FastRouting.sound _ _ [36,257,192,18,96] 13 (by decide) (choices 1) [1,2,8,128] r38636 c38636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26068
  · exact u26069
  · exact u26070
  · exact u26071

def b38637 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 37 259 196 26 208 43 107 171 299), lower := (rows 37 259 196 26 208 32 64 128 256), losses := [] }

theorem u38637 : Upper (D 7) (R 7) [36,257,192,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38638 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 259 196 41 82 186 218 154 410), lower := (rows 37 259 196 41 82 32 64 128 256), losses := [] }

theorem u38638 : Upper (D 7) (R 7) [36,257,192,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38639 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 259 196 41 88 178 210 146 402), lower := (rows 37 259 196 41 88 32 64 128 256), losses := [] }

theorem u38639 : Upper (D 7) (R 7) [36,257,192,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u38639
end Delivery.IrregularNine14.P07
