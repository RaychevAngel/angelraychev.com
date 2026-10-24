import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0051
import IrregularNine14P05C0052

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6600 : Route 9 := (fun mask => (mask,id))

def c6600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6600 : Upper (D 5) (R 5) [6,65,384,36,10] 13 := by
  apply FastRouting.sound _ _ [6,65,384,36,10] 13 (by decide) (choices 1) [1,8,16] r6600 c6600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3113
  · exact u3114
  · exact u3115

def r6601 : Route 9 := (fun mask => (mask,id))

def c6601 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6601 : Upper (D 5) (R 5) [6,65,384,36,33] 13 := by
  apply FastRouting.sound _ _ [6,65,384,36,33] 13 (by decide) (choices 1) [2,8,16] r6601 c6601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3116
  · exact u3117
  · exact u3118

def r6602 : Route 9 := (fun mask => (mask,id))

def c6602 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6602 : Upper (D 5) (R 5) [6,65,384,36,34] 13 := by
  apply FastRouting.sound _ _ [6,65,384,36,34] 13 (by decide) (choices 1) [1,8,16] r6602 c6602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3119
  · exact u3120
  · exact u3121

def b6603 : PairBound 9 := { available := 27, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 388 44 56 59 91 155 283), lower := (rows 7 67 388 44 56 32 64 128 256), losses := [] }

theorem u6603 : Upper (D 5) (R 5) [6,65,384,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6603
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6604 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 388 56 19 44 108 172 300), lower := (rows 7 67 388 56 19 32 64 128 256), losses := [] }

theorem u6604 : Upper (D 5) (R 5) [6,65,384,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6604
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6605 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 388 56 21 42 106 170 298), lower := (rows 7 67 388 56 21 32 64 128 256), losses := [] }

theorem u6605 : Upper (D 5) (R 5) [6,65,384,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6605
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6606 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 67 388 56 22 41 105 169 297), lower := (rows 7 67 388 56 22 32 64 128 256), losses := [] }

theorem u6606 : Upper (D 5) (R 5) [6,65,384,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6606
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6607 : Route 9 := (fun mask => (mask,id))

def c6607 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6607 : Upper (D 5) (R 5) [6,65,384,48,9] 13 := by
  apply FastRouting.sound _ _ [6,65,384,48,9] 13 (by decide) (choices 1) [2,4,8] r6607 c6607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3122
  · exact u3123
  · exact u3124

def r6608 : Route 9 := (fun mask => (mask,id))

def c6608 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6608 : Upper (D 5) (R 5) [6,65,384,48,10] 13 := by
  apply FastRouting.sound _ _ [6,65,384,48,10] 13 (by decide) (choices 1) [1,4,8] r6608 c6608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3125
  · exact u3126
  · exact u3127

def r6609 : Route 9 := (fun mask => (mask,id))

def c6609 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6609 : Upper (D 5) (R 5) [6,65,384,48,12] 13 := by
  apply FastRouting.sound _ _ [6,65,384,48,12] 13 (by decide) (choices 1) [1,2,8] r6609 c6609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3128
  · exact u3129
  · exact u3130

def b6610 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 388 56 49 46 78 142 270), lower := (rows 7 67 388 56 49 32 64 128 256), losses := [] }

theorem u6610 : Upper (D 5) (R 5) [6,65,384,48,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6610
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6611 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 388 56 50 45 77 141 269), lower := (rows 7 67 388 56 50 32 64 128 256), losses := [] }

theorem u6611 : Upper (D 5) (R 5) [6,65,384,48,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6611
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6612 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 388 56 52 43 75 139 267), lower := (rows 7 67 388 56 52 32 64 128 256), losses := [] }

theorem u6612 : Upper (D 5) (R 5) [6,65,384,48,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6612
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6613 : PairBound 9 := { available := 15, camps := [{ cop := 5, region := 24, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 388 56 56 47 79 143 271), lower := (rows 7 67 388 56 56 32 64 128 256), losses := [] }

theorem u6613 : Upper (D 5) (R 5) [6,65,384,48,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6613
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6614 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 74 140 25 19 292 356 420 292), lower := (rows 7 74 140 25 19 32 64 128 256), losses := [] }

theorem u6614 : Upper (D 5) (R 5) [6,72,136,17,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6614
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6615 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 74 140 25 22 289 353 417 289), lower := (rows 7 74 140 25 22 32 64 128 256), losses := [] }

theorem u6615 : Upper (D 5) (R 5) [6,72,136,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6615
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6616 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 8, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 74 140 25 49 294 358 422 294), lower := (rows 7 74 140 25 49 32 64 128 256), losses := [] }

theorem u6616 : Upper (D 5) (R 5) [6,72,136,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6616
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6617 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 304, targets := 8 },{ cop := 3, region := 420, targets := 2 }], pairs := [(2,1),(4,3)], upper := (rows 7 74 140 25 50 293 357 421 293), lower := (rows 7 74 140 25 50 32 64 128 256), losses := [] }

theorem u6617 : Upper (D 5) (R 5) [6,72,136,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6617
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6618 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 74 140 25 273 38 102 166 294), lower := (rows 7 74 140 25 273 32 64 128 256), losses := [] }

theorem u6618 : Upper (D 5) (R 5) [6,72,136,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6618
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6619 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 304, targets := 8 },{ cop := 3, region := 164, targets := 2 }], pairs := [(2,1),(4,3)], upper := (rows 7 74 140 25 274 37 101 165 293), lower := (rows 7 74 140 25 274 32 64 128 256), losses := [] }

theorem u6619 : Upper (D 5) (R 5) [6,72,136,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6619
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m6620_4 : Upper (D 5) (R 5) [6,72,136,17,288,4] 13 :=
  permutation_upper _ _ _ [6,72,136,17,288,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3132

def r6620 : Route 9 := (fun mask => (mask,id))

def c6620 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6620 : Upper (D 5) (R 5) [6,72,136,17,288] 13 := by
  apply FastRouting.sound _ _ [6,72,136,17,288] 13 (by decide) (choices 1) [1,2,4] r6620 c6620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3131
  · exact u3132
  · exact m6620_4

def b6621 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 7 74 140 41 19 308 372 436 308), lower := (rows 7 74 140 41 19 32 64 128 256), losses := [] }

theorem u6621 : Upper (D 5) (R 5) [6,72,136,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6621
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6622 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 74 140 41 22 305 369 433 305), lower := (rows 7 74 140 41 22 32 64 128 256), losses := [] }

theorem u6622 : Upper (D 5) (R 5) [6,72,136,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6622
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6623 : PairBound 9 := { available := 278, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 140 41 49 310 342 406 278), lower := (rows 7 74 140 41 49 32 64 128 256), losses := [] }

theorem u6623 : Upper (D 5) (R 5) [6,72,136,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6623
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6624 : Route 9 := (fun mask => (mask,id))

def c6624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6624 : Upper (D 5) (R 5) [6,72,136,33,34] 13 := by
  apply FastRouting.sound _ _ [6,72,136,33,34] 13 (by decide) (choices 1) [1,4,16,256] r6624 c6624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3133
  · exact u3134
  · exact u3135
  · exact u3136

theorem m6625_4 : Upper (D 5) (R 5) [6,72,136,33,257,4] 13 :=
  permutation_upper _ _ _ [6,72,136,33,257,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3137

def r6625 : Route 9 := (fun mask => (mask,id))

def c6625 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6625 : Upper (D 5) (R 5) [6,72,136,33,257] 13 := by
  apply FastRouting.sound _ _ [6,72,136,33,257] 13 (by decide) (choices 1) [2,4,16] r6625 c6625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3137
  · exact m6625_4
  · exact u3138

def r6626 : Route 9 := (fun mask => (mask,id))

def c6626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6626 : Upper (D 5) (R 5) [6,72,136,33,258] 13 := by
  apply FastRouting.sound _ _ [6,72,136,33,258] 13 (by decide) (choices 1) [1,4,16] r6626 c6626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3139
  · exact u3140
  · exact u3141

theorem m6627_4 : Upper (D 5) (R 5) [6,72,136,33,288,4] 13 :=
  permutation_upper _ _ _ [6,72,136,33,288,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3143

def r6627 : Route 9 := (fun mask => (mask,id))

def c6627 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6627 : Upper (D 5) (R 5) [6,72,136,33,288] 13 := by
  apply FastRouting.sound _ _ [6,72,136,33,288] 13 (by decide) (choices 1) [1,2,4,16] r6627 c6627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3142
  · exact u3143
  · exact m6627_4
  · exact u3144

def b6628 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 7 74 140 56 19 293 357 421 293), lower := (rows 7 74 140 56 19 32 64 128 256), losses := [] }

theorem u6628 : Upper (D 5) (R 5) [6,72,136,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6628
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6629 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 74 140 56 22 289 353 417 289), lower := (rows 7 74 140 56 22 32 64 128 256), losses := [] }

theorem u6629 : Upper (D 5) (R 5) [6,72,136,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6629
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6630 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 140 56 49 295 327 391 263), lower := (rows 7 74 140 56 49 32 64 128 256), losses := [] }

theorem u6630 : Upper (D 5) (R 5) [6,72,136,48,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6630
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6631 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 140 56 50 293 325 389 261), lower := (rows 7 74 140 56 50 32 64 128 256), losses := [] }

theorem u6631 : Upper (D 5) (R 5) [6,72,136,48,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6631
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m6632_4 : Upper (D 5) (R 5) [6,72,136,48,257,4] 13 :=
  permutation_upper _ _ _ [6,72,136,48,257,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3146

def r6632 : Route 9 := (fun mask => (mask,id))

def c6632 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6632 : Upper (D 5) (R 5) [6,72,136,48,257] 13 := by
  apply FastRouting.sound _ _ [6,72,136,48,257] 13 (by decide) (choices 1) [1,2,4] r6632 c6632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3145
  · exact u3146
  · exact m6632_4

def r6633 : Route 9 := (fun mask => (mask,id))

def c6633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6633 : Upper (D 5) (R 5) [6,72,136,48,258] 13 := by
  apply FastRouting.sound _ _ [6,72,136,48,258] 13 (by decide) (choices 1) [1,4] r6633 c6633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3147
  · exact u3148

def b6634 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 199, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 140 56 304 39 71 135 263), lower := (rows 7 74 140 56 304 32 64 128 256), losses := [] }

theorem u6634 : Upper (D 5) (R 5) [6,72,136,48,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6634
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6635 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 7 74 140 265 19 52 116 180 308), lower := (rows 7 74 140 265 19 32 64 128 256), losses := [] }

theorem u6635 : Upper (D 5) (R 5) [6,72,136,257,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6635
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6636 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 74 140 265 22 49 113 177 305), lower := (rows 7 74 140 265 22 32 64 128 256), losses := [] }

theorem u6636 : Upper (D 5) (R 5) [6,72,136,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6636
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m6637_4 : Upper (D 5) (R 5) [6,72,136,257,33,4] 13 :=
  permutation_upper _ _ _ [6,72,136,257,33,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3149

def r6637 : Route 9 := (fun mask => (mask,id))

def c6637 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6637 : Upper (D 5) (R 5) [6,72,136,257,33] 13 := by
  apply FastRouting.sound _ _ [6,72,136,257,33] 13 (by decide) (choices 1) [2,4,16] r6637 c6637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3149
  · exact m6637_4
  · exact u3150

def r6638 : Route 9 := (fun mask => (mask,id))

def c6638 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6638 : Upper (D 5) (R 5) [6,72,136,257,34] 13 := by
  apply FastRouting.sound _ _ [6,72,136,257,34] 13 (by decide) (choices 1) [1,4,16] r6638 c6638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3151
  · exact u3152
  · exact u3153

def b6639 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 7 74 140 280 19 37 101 165 293), lower := (rows 7 74 140 280 19 32 64 128 256), losses := [] }

theorem u6639 : Upper (D 5) (R 5) [6,72,136,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6639
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6640 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 74 140 280 22 33 97 161 289), lower := (rows 7 74 140 280 22 32 64 128 256), losses := [] }

theorem u6640 : Upper (D 5) (R 5) [6,72,136,272,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6640
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m6641_4 : Upper (D 5) (R 5) [6,72,136,272,33,4] 13 :=
  permutation_upper _ _ _ [6,72,136,272,33,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3155

def r6641 : Route 9 := (fun mask => (mask,id))

def c6641 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6641 : Upper (D 5) (R 5) [6,72,136,272,33] 13 := by
  apply FastRouting.sound _ _ [6,72,136,272,33] 13 (by decide) (choices 1) [1,2,4] r6641 c6641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3154
  · exact u3155
  · exact m6641_4

def r6642 : Route 9 := (fun mask => (mask,id))

def c6642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6642 : Upper (D 5) (R 5) [6,72,136,272,34] 13 := by
  apply FastRouting.sound _ _ [6,72,136,272,34] 13 (by decide) (choices 1) [1,4] r6642 c6642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3156
  · exact u3157

def b6643 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 7 74 140 296 19 53 117 181 309), lower := (rows 7 74 140 296 19 32 64 128 256), losses := [] }

theorem u6643 : Upper (D 5) (R 5) [6,72,136,288,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6643
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6644 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 74 140 296 22 49 113 177 305), lower := (rows 7 74 140 296 22 32 64 128 256), losses := [] }

theorem u6644 : Upper (D 5) (R 5) [6,72,136,288,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6644
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m6645_4 : Upper (D 5) (R 5) [6,72,136,288,33,4] 13 :=
  permutation_upper _ _ _ [6,72,136,288,33,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3159

def r6645 : Route 9 := (fun mask => (mask,id))

def c6645 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6645 : Upper (D 5) (R 5) [6,72,136,288,33] 13 := by
  apply FastRouting.sound _ _ [6,72,136,288,33] 13 (by decide) (choices 1) [1,2,4,16] r6645 c6645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3158
  · exact u3159
  · exact m6645_4
  · exact u3160

def r6646 : Route 9 := (fun mask => (mask,id))

def c6646 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6646 : Upper (D 5) (R 5) [6,72,136,288,34] 13 := by
  apply FastRouting.sound _ _ [6,72,136,288,34] 13 (by decide) (choices 1) [1,4,16] r6646 c6646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3161
  · exact u3162
  · exact u3163

def b6647 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 74 148 41 19 300 364 428 300), lower := (rows 7 74 148 41 19 32 64 128 256), losses := [] }

theorem u6647 : Upper (D 5) (R 5) [6,72,144,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6647
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6648 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 74 148 41 21 298 362 426 298), lower := (rows 7 74 148 41 21 32 64 128 256), losses := [] }

theorem u6648 : Upper (D 5) (R 5) [6,72,144,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6648
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6649 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 74 148 41 22 297 361 425 297), lower := (rows 7 74 148 41 22 32 64 128 256), losses := [] }

theorem u6649 : Upper (D 5) (R 5) [6,72,144,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6649
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6650 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 148 41 25 294 358 422 294), lower := (rows 7 74 148 41 25 32 64 128 256), losses := [] }

theorem u6650 : Upper (D 5) (R 5) [6,72,144,33,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6650
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6651 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 74 148 41 26 293 357 421 293), lower := (rows 7 74 148 41 26 32 64 128 256), losses := [] }

theorem u6651 : Upper (D 5) (R 5) [6,72,144,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6651
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6652 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 74 148 41 28 291 355 419 291), lower := (rows 7 74 148 41 28 32 64 128 256), losses := [] }

theorem u6652 : Upper (D 5) (R 5) [6,72,144,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6652
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6653 : PairBound 9 := { available := 270, camps := [{ cop := 3, region := 16, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 74 148 41 49 302 334 398 270), lower := (rows 7 74 148 41 49 32 64 128 256), losses := [] }

theorem u6653 : Upper (D 5) (R 5) [6,72,144,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6653
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6654 : Route 9 := (fun mask => (mask,id))

def c6654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6654 : Upper (D 5) (R 5) [6,72,144,33,34] 13 := by
  apply FastRouting.sound _ _ [6,72,144,33,34] 13 (by decide) (choices 1) [1,4,8,256] r6654 c6654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3164
  · exact u3165
  · exact u3166
  · exact u3167

def b6655 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 74 148 41 52 299 331 395 267), lower := (rows 7 74 148 41 52 32 64 128 256), losses := [] }

theorem u6655 : Upper (D 5) (R 5) [6,72,144,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6655
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6656 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 74 148 41 56 295 327 391 263), lower := (rows 7 74 148 41 56 32 64 128 256), losses := [] }

theorem u6656 : Upper (D 5) (R 5) [6,72,144,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6656
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6657 : Route 9 := (fun mask => (mask,id))

def c6657 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6657 : Upper (D 5) (R 5) [6,72,144,33,257] 13 := by
  apply FastRouting.sound _ _ [6,72,144,33,257] 13 (by decide) (choices 1) [2,4,8] r6657 c6657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3168
  · exact u3169
  · exact u3170

def r6658 : Route 9 := (fun mask => (mask,id))

def c6658 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6658 : Upper (D 5) (R 5) [6,72,144,33,258] 13 := by
  apply FastRouting.sound _ _ [6,72,144,33,258] 13 (by decide) (choices 1) [1,4,8] r6658 c6658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3171
  · exact u3172
  · exact u3173

def b6659 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 106, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 74 148 41 276 43 107 171 299), lower := (rows 7 74 148 41 276 32 64 128 256), losses := [] }

theorem u6659 : Upper (D 5) (R 5) [6,72,144,33,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6659
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u6659
end Delivery.IrregularNine14.P05
