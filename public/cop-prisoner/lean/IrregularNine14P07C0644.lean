import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0434
import IrregularNine14P07C0435
import IrregularNine14P07C0436

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38640 : Route 9 := (fun mask => (mask,id))

def c38640 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38640 : Upper (D 7) (R 7) [36,257,192,34,65] 13 := by
  apply FastRouting.sound _ _ [36,257,192,34,65] 13 (by decide) (choices 1) [2,8,16,128] r38640 c38640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26072
  · exact u26073
  · exact u26074
  · exact u26075

def r38641 : Route 9 := (fun mask => (mask,id))

def c38641 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38641 : Upper (D 7) (R 7) [36,257,192,34,66] 13 := by
  apply FastRouting.sound _ _ [36,257,192,34,66] 13 (by decide) (choices 1) [1,8,16,128] r38641 c38641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26076
  · exact u26077
  · exact u26078
  · exact u26079

def r38642 : Route 9 := (fun mask => (mask,id))

def c38642 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38642 : Upper (D 7) (R 7) [36,257,192,34,72] 13 := by
  apply FastRouting.sound _ _ [36,257,192,34,72] 13 (by decide) (choices 1) [1,2,16,128] r38642 c38642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26080
  · exact u26081
  · exact u26082
  · exact u26083

def b38643 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 37 259 196 42 208 59 91 155 283), lower := (rows 37 259 196 42 208 32 64 128 256), losses := [] }

theorem u38643 : Upper (D 7) (R 7) [36,257,192,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38644 : Route 9 := (fun mask => (mask,id))

def c38644 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38644 : Upper (D 7) (R 7) [36,257,192,48,65] 13 := by
  apply FastRouting.sound _ _ [36,257,192,48,65] 13 (by decide) (choices 1) [2,8,128] r38644 c38644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26084
  · exact u26085
  · exact u26086

def r38645 : Route 9 := (fun mask => (mask,id))

def c38645 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38645 : Upper (D 7) (R 7) [36,257,192,48,66] 13 := by
  apply FastRouting.sound _ _ [36,257,192,48,66] 13 (by decide) (choices 1) [1,2,8,128] r38645 c38645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26087
  · exact u26088
  · exact u26089
  · exact u26090

def b38646 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(1,5),(1,6),(2,5)], upper := (rows 37 259 196 56 88 163 195 131 387), lower := (rows 37 259 196 56 88 32 64 128 256), losses := [] }

theorem u38646 : Upper (D 7) (R 7) [36,257,192,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38647 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 37 259 196 56 208 43 75 139 267), lower := (rows 37 259 196 56 208 32 64 128 256), losses := [] }

theorem u38647 : Upper (D 7) (R 7) [36,257,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38648 : Route 9 := (fun mask => (mask,id))

def c38648 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38648 : Upper (D 7) (R 7) [36,257,192,65,130] 13 := by
  apply FastRouting.sound _ _ [36,257,192,65,130] 13 (by decide) (choices 1) [2,8,16] r38648 c38648
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26091
  · exact u26092
  · exact u26093

def r38649 : Route 9 := (fun mask => (mask,id))

def c38649 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38649 : Upper (D 7) (R 7) [36,257,192,65,136] 13 := by
  apply FastRouting.sound _ _ [36,257,192,65,136] 13 (by decide) (choices 1) [2,16] r38649 c38649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26094
  · exact u26095

def r38650 : Route 9 := (fun mask => (mask,id))

def c38650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38650 : Upper (D 7) (R 7) [36,257,192,65,160] 13 := by
  apply FastRouting.sound _ _ [36,257,192,65,160] 13 (by decide) (choices 1) [2,8,16] r38650 c38650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26096
  · exact u26097
  · exact u26098

theorem m38651_16 : Upper (D 7) (R 7) [36,257,192,66,130,16] 13 :=
  permutation_upper _ _ _ [36,257,192,66,130,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u26100

def r38651 : Route 9 := (fun mask => (mask,id))

def c38651 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38651 : Upper (D 7) (R 7) [36,257,192,66,130] 13 := by
  apply FastRouting.sound _ _ [36,257,192,66,130] 13 (by decide) (choices 1) [1,8,16] r38651 c38651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26099
  · exact u26100
  · exact m38651_16

def r38652 : Route 9 := (fun mask => (mask,id))

def c38652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38652 : Upper (D 7) (R 7) [36,257,192,66,136] 13 := by
  apply FastRouting.sound _ _ [36,257,192,66,136] 13 (by decide) (choices 1) [1,2,16] r38652 c38652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26101
  · exact u26102
  · exact u26103

def r38653 : Route 9 := (fun mask => (mask,id))

def c38653 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38653 : Upper (D 7) (R 7) [36,257,192,66,160] 13 := by
  apply FastRouting.sound _ _ [36,257,192,66,160] 13 (by decide) (choices 1) [1,2,8,16] r38653 c38653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26104
  · exact u26105
  · exact u26106
  · exact u26107

def b38654 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5),(4,0)], upper := (rows 37 259 196 88 152 35 99 163 291), lower := (rows 37 259 196 88 152 32 64 128 256), losses := [] }

theorem u38654 : Upper (D 7) (R 7) [36,257,192,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38655 : Route 9 := (fun mask => (mask,id))

def c38655 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38655 : Upper (D 7) (R 7) [36,257,192,80,160] 13 := by
  apply FastRouting.sound _ _ [36,257,192,80,160] 13 (by decide) (choices 1) [1,2,8] r38655 c38655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26108
  · exact u26109
  · exact u26110

def b38656 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 25 50 224 192 192 448), lower := (rows 37 266 7 25 50 32 64 128 256), losses := [] }

theorem u38656 : Upper (D 7) (R 7) [36,264,3,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38657 : Route 9 := (fun mask => (mask,id))

def c38657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38657 : Upper (D 7) (R 7) [36,264,3,17,66] 13 := by
  apply FastRouting.sound _ _ [36,264,3,17,66] 13 (by decide) (choices 1) [64,128] r38657 c38657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26111
  · exact u26112

def b38658 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 266 7 25 112 226 194 194 450), lower := (rows 37 266 7 25 112 32 64 128 256), losses := [] }

theorem u38658 : Upper (D 7) (R 7) [36,264,3,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38659 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38659 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38659 : Upper (D 7) (R 7) [36,264,3,17,192] 13 := by
  apply FastRouting.sound _ _ [36,264,3,17,192] 13 (by decide) (choices 1) [2,64] r38659 c38659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26113
  · exact u26114

def b38660 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 37 266 7 26 49 224 192 192 448), lower := (rows 37 266 7 26 49 32 64 128 256), losses := [] }

theorem u38660 : Upper (D 7) (R 7) [36,264,3,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38661 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 266 7 26 81 224 224 224 480), lower := (rows 37 266 7 26 81 32 64 128 256), losses := [] }

theorem u38661 : Upper (D 7) (R 7) [36,264,3,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38662 : Route 9 := (fun mask => (mask,id))

def c38662 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38662 : Upper (D 7) (R 7) [36,264,3,18,96] 13 := by
  apply FastRouting.sound _ _ [36,264,3,18,96] 13 (by decide) (choices 1) [1,64,128] r38662 c38662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26115
  · exact u26116
  · exact u26117

def r38663 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38663 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38663 : Upper (D 7) (R 7) [36,264,3,18,192] 13 := by
  apply FastRouting.sound _ _ [36,264,3,18,192] 13 (by decide) (choices 1) [1,64] r38663 c38663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26118
  · exact u26119

def b38664 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 16, targets := 192 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 37 266 7 56 19 224 192 192 448), lower := (rows 37 266 7 56 19 32 64 128 256), losses := [] }

theorem u38664 : Upper (D 7) (R 7) [36,264,3,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38665 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 2, region := 208, targets := 32 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(3,0),(4,5)], upper := (rows 37 266 7 56 81 226 194 194 450), lower := (rows 37 266 7 56 81 32 64 128 256), losses := [] }

theorem u38665 : Upper (D 7) (R 7) [36,264,3,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38666 : Route 9 := (fun mask => (mask,id))

def c38666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38666 : Upper (D 7) (R 7) [36,264,3,48,66] 13 := by
  apply FastRouting.sound _ _ [36,264,3,48,66] 13 (by decide) (choices 1) [1,64,128] r38666 c38666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26120
  · exact u26121
  · exact u26122

def r38667 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c38667 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38667 : Upper (D 7) (R 7) [36,264,3,48,192] 13 := by
  apply FastRouting.sound _ _ [36,264,3,48,192] 13 (by decide) (choices 1) [1,2,64] r38667 c38667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26123
  · exact u26124
  · exact u26125

def b38668 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 73 50 240 208 208 464), lower := (rows 37 266 7 73 50 32 64 128 256), losses := [] }

theorem u38668 : Upper (D 7) (R 7) [36,264,3,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38669 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 266 7 73 82 176 240 176 432), lower := (rows 37 266 7 73 82 32 64 128 256), losses := [] }

theorem u38669 : Upper (D 7) (R 7) [36,264,3,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38670 : Route 9 := (fun mask => (mask,id))

def c38670 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38670 : Upper (D 7) (R 7) [36,264,3,65,96] 13 := by
  apply FastRouting.sound _ _ [36,264,3,65,96] 13 (by decide) (choices 1) [2,16,128] r38670 c38670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26126
  · exact u26127
  · exact u26128

def r38671 : Route 9 := (fun mask => (mask,id))

def c38671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38671 : Upper (D 7) (R 7) [36,264,3,65,130] 13 := by
  apply FastRouting.sound _ _ [36,264,3,65,130] 13 (by decide) (choices 1) [16,64,128] r38671 c38671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26129
  · exact u26130
  · exact u26131

def r38672 : Route 9 := (fun mask => (mask,id))

def c38672 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38672 : Upper (D 7) (R 7) [36,264,3,65,160] 13 := by
  apply FastRouting.sound _ _ [36,264,3,65,160] 13 (by decide) (choices 1) [2,16,64,128] r38672 c38672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26132
  · exact u26133
  · exact u26134
  · exact u26135

def r38673 : Route 9 := (fun mask => (mask,id))

def c38673 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38673 : Upper (D 7) (R 7) [36,264,3,65,192] 13 := by
  apply FastRouting.sound _ _ [36,264,3,65,192] 13 (by decide) (choices 1) [2,16,128] r38673 c38673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26136
  · exact u26137
  · exact u26138

def b38674 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 37 266 7 74 49 240 208 208 464), lower := (rows 37 266 7 74 49 32 64 128 256), losses := [] }

theorem u38674 : Upper (D 7) (R 7) [36,264,3,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38675 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 266 7 74 81 176 240 176 432), lower := (rows 37 266 7 74 81 32 64 128 256), losses := [] }

theorem u38675 : Upper (D 7) (R 7) [36,264,3,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38676 : Route 9 := (fun mask => (mask,id))

def c38676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38676 : Upper (D 7) (R 7) [36,264,3,66,96] 13 := by
  apply FastRouting.sound _ _ [36,264,3,66,96] 13 (by decide) (choices 1) [1,16,128] r38676 c38676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26139
  · exact u26140
  · exact u26141

def b38677 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,1),(1,0),(3,0),(4,1)], upper := (rows 37 266 7 74 145 240 240 240 496), lower := (rows 37 266 7 74 145 32 64 128 256), losses := [] }

theorem u38677 : Upper (D 7) (R 7) [36,264,3,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38678 : Route 9 := (fun mask => (mask,id))

def c38678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38678 : Upper (D 7) (R 7) [36,264,3,66,160] 13 := by
  apply FastRouting.sound _ _ [36,264,3,66,160] 13 (by decide) (choices 1) [1,16,64,128] r38678 c38678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26142
  · exact u26143
  · exact u26144
  · exact u26145

def r38679 : Route 9 := (fun mask => (mask,id))

def c38679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38679 : Upper (D 7) (R 7) [36,264,3,66,192] 13 := by
  apply FastRouting.sound _ _ [36,264,3,66,192] 13 (by decide) (choices 1) [1,16,128] r38679 c38679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26146
  · exact u26147
  · exact u26148

def b38680 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 16, targets := 224 },{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 37 266 7 88 19 224 224 224 480), lower := (rows 37 266 7 88 19 32 64 128 256), losses := [] }

theorem u38680 : Upper (D 7) (R 7) [36,264,3,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38681 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 7 88 49 226 194 194 450), lower := (rows 37 266 7 88 49 32 64 128 256), losses := [] }

theorem u38681 : Upper (D 7) (R 7) [36,264,3,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38682 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 88 50 225 193 193 449), lower := (rows 37 266 7 88 50 32 64 128 256), losses := [] }

theorem u38682 : Upper (D 7) (R 7) [36,264,3,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38683 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 423, targets := 64 },{ cop := 4, region := 8, targets := 2 }], pairs := [(0,6),(1,6),(2,6),(3,1)], upper := (rows 37 266 7 88 81 162 226 162 418), lower := (rows 37 266 7 88 81 32 64 128 256), losses := [] }

theorem u38683 : Upper (D 7) (R 7) [36,264,3,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38684 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 37 266 7 88 82 161 225 161 417), lower := (rows 37 266 7 88 82 32 64 128 256), losses := [] }

theorem u38684 : Upper (D 7) (R 7) [36,264,3,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38685 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 37 266 7 88 112 163 195 131 387), lower := (rows 37 266 7 88 112 32 64 128 256), losses := [] }

theorem u38685 : Upper (D 7) (R 7) [36,264,3,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38686 : Route 9 := (fun mask => (mask,id))

def c38686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38686 : Upper (D 7) (R 7) [36,264,3,80,129] 13 := by
  apply FastRouting.sound _ _ [36,264,3,80,129] 13 (by decide) (choices 1) [2,64,128] r38686 c38686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26149
  · exact u26150
  · exact u26151

def r38687 : Route 9 := (fun mask => (mask,id))

def c38687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38687 : Upper (D 7) (R 7) [36,264,3,80,130] 13 := by
  apply FastRouting.sound _ _ [36,264,3,80,130] 13 (by decide) (choices 1) [1,64,128] r38687 c38687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26152
  · exact u26153
  · exact u26154

def r38688 : Route 9 := (fun mask => (mask,id))

def c38688 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u38688 : Upper (D 7) (R 7) [36,264,3,80,160] 13 := by
  apply FastRouting.sound _ _ [36,264,3,80,160] 13 (by decide) (choices 1) [1,2,64,128] r38688 c38688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26155
  · exact u26156
  · exact u26157
  · exact u26158

def b38689 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 37 266 7 88 208 163 227 163 419), lower := (rows 37 266 7 88 208 32 64 128 256), losses := [] }

theorem u38689 : Upper (D 7) (R 7) [36,264,3,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38690 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 16, targets := 192 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 37 266 7 104 19 240 208 208 464), lower := (rows 37 266 7 104 19 32 64 128 256), losses := [] }

theorem u38690 : Upper (D 7) (R 7) [36,264,3,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38691 : Route 9 := (fun mask => (mask,id))

def c38691 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38691 : Upper (D 7) (R 7) [36,264,3,96,65] 13 := by
  apply FastRouting.sound _ _ [36,264,3,96,65] 13 (by decide) (choices 1) [2,16,128] r38691 c38691
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26159
  · exact u26160
  · exact u26161

def r38692 : Route 9 := (fun mask => (mask,id))

def c38692 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38692 : Upper (D 7) (R 7) [36,264,3,96,66] 13 := by
  apply FastRouting.sound _ _ [36,264,3,96,66] 13 (by decide) (choices 1) [1,16,128] r38692 c38692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26162
  · exact u26163
  · exact u26164

def r38693 : Route 9 := (fun mask => (mask,id))

def c38693 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38693 : Upper (D 7) (R 7) [36,264,3,96,129] 13 := by
  apply FastRouting.sound _ _ [36,264,3,96,129] 13 (by decide) (choices 1) [2,16,64,128] r38693 c38693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26165
  · exact u26166
  · exact u26167
  · exact u26168

def r38694 : Route 9 := (fun mask => (mask,id))

def c38694 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u38694 : Upper (D 7) (R 7) [36,264,3,96,130] 13 := by
  apply FastRouting.sound _ _ [36,264,3,96,130] 13 (by decide) (choices 1) [1,16,64,128] r38694 c38694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26169
  · exact u26170
  · exact u26171
  · exact u26172

def r38695 : Route 9 := (fun mask => (mask,id))

def c38695 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38695 : Upper (D 7) (R 7) [36,264,3,96,192] 13 := by
  apply FastRouting.sound _ _ [36,264,3,96,192] 13 (by decide) (choices 1) [1,2,16,128] r38695 c38695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u26173
  · exact u26174
  · exact u26175
  · exact u26176

def b38696 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 16, targets := 224 },{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 37 266 7 200 19 240 240 240 496), lower := (rows 37 266 7 200 19 32 64 128 256), losses := [] }

theorem u38696 : Upper (D 7) (R 7) [36,264,3,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38697 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 266 7 200 49 242 210 210 466), lower := (rows 37 266 7 200 49 32 64 128 256), losses := [] }

theorem u38697 : Upper (D 7) (R 7) [36,264,3,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38698 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 266 7 200 50 241 209 209 465), lower := (rows 37 266 7 200 50 32 64 128 256), losses := [] }

theorem u38698 : Upper (D 7) (R 7) [36,264,3,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r38699 : Route 9 := (fun mask => (mask,id))

def c38699 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u38699 : Upper (D 7) (R 7) [36,264,3,192,65] 13 := by
  apply FastRouting.sound _ _ [36,264,3,192,65] 13 (by decide) (choices 1) [2,16,128] r38699 c38699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u26177
  · exact u26178
  · exact u26179

#print axioms u38699
end Delivery.IrregularNine14.P07
