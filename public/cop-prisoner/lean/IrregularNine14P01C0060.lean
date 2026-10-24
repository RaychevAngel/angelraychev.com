import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0015

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3600 : Route 9 := (fun mask => (mask,id))

def c3600 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3600 : Upper (D 1) (R 1) [52,257,66,80,128] 13 := by
  apply FastRouting.sound _ _ [52,257,66,80,128] 13 (by decide) (choices 1) [2,8,128] r3600 c3600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u912
  · exact u913
  · exact u914

def b3601 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 53 259 70 138 24 240 240 240 496), lower := (rows 53 259 70 138 24 32 64 128 256), losses := [] }

theorem u3601 : Upper (D 1) (R 1) [52,257,66,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3601
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3602 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 259 70 138 48 248 216 216 472), lower := (rows 53 259 70 138 48 32 64 128 256), losses := [] }

theorem u3602 : Upper (D 1) (R 1) [52,257,66,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3602
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3603 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 259 70 138 80 184 248 184 440), lower := (rows 53 259 70 138 80 32 64 128 256), losses := [] }

theorem u3603 : Upper (D 1) (R 1) [52,257,66,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3603
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3604_8 : Upper (D 1) (R 1) [52,257,66,130,128,8] 13 :=
  permutation_upper _ _ _ [52,257,66,130,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u915

theorem m3604_16 : Upper (D 1) (R 1) [52,257,66,130,128,16] 13 :=
  permutation_upper _ _ _ [52,257,66,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u916

theorem m3604_64 : Upper (D 1) (R 1) [52,257,66,130,128,64] 13 :=
  permutation_upper _ _ _ [52,257,66,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u917

def r3604 : Route 9 := (fun mask => (mask,id))

def c3604 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3604 : Upper (D 1) (R 1) [52,257,66,130,128] 13 := by
  apply FastRouting.sound _ _ [52,257,66,130,128] 13 (by decide) (choices 1) [8,16,64] r3604 c3604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3604_8
  · exact m3604_16
  · exact m3604_64

def b3605 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 259 70 152 18 232 232 232 488), lower := (rows 53 259 70 152 18 32 64 128 256), losses := [] }

theorem u3605 : Upper (D 1) (R 1) [52,257,66,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3605
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3606 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 259 70 152 24 226 226 226 482), lower := (rows 53 259 70 152 24 32 64 128 256), losses := [] }

theorem u3606 : Upper (D 1) (R 1) [52,257,66,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3606
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3607 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 259 70 152 48 234 202 202 458), lower := (rows 53 259 70 152 48 32 64 128 256), losses := [] }

theorem u3607 : Upper (D 1) (R 1) [52,257,66,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3607
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3608 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 259 70 152 80 170 234 170 426), lower := (rows 53 259 70 152 80 32 64 128 256), losses := [] }

theorem u3608 : Upper (D 1) (R 1) [52,257,66,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3608
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3609 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 53 259 70 152 144 106 106 234 362), lower := (rows 53 259 70 152 144 32 64 128 256), losses := [] }

theorem u3609 : Upper (D 1) (R 1) [52,257,66,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3609
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3610 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 259 70 200 18 184 248 184 440), lower := (rows 53 259 70 200 18 32 64 128 256), losses := [] }

theorem u3610 : Upper (D 1) (R 1) [52,257,66,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3610
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3611 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 259 70 200 24 178 242 178 434), lower := (rows 53 259 70 200 24 32 64 128 256), losses := [] }

theorem u3611 : Upper (D 1) (R 1) [52,257,66,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3611
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3612 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 259 70 200 48 186 218 154 410), lower := (rows 53 259 70 200 48 32 64 128 256), losses := [] }

theorem u3612 : Upper (D 1) (R 1) [52,257,66,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3612
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3613_2 : Upper (D 1) (R 1) [52,257,66,192,128,2] 13 :=
  permutation_upper _ _ _ [52,257,66,192,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u918

theorem m3613_8 : Upper (D 1) (R 1) [52,257,66,192,128,8] 13 :=
  permutation_upper _ _ _ [52,257,66,192,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u919

theorem m3613_16 : Upper (D 1) (R 1) [52,257,66,192,128,16] 13 :=
  permutation_upper _ _ _ [52,257,66,192,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u920

def r3613 : Route 9 := (fun mask => (mask,id))

def c3613 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3613 : Upper (D 1) (R 1) [52,257,66,192,128] 13 := by
  apply FastRouting.sound _ _ [52,257,66,192,128] 13 (by decide) (choices 1) [2,8,16] r3613 c3613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3613_2
  · exact m3613_8
  · exact m3613_16

def r3614 : Route 9 := (fun mask => (mask,id))

def c3614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3614 : Upper (D 1) (R 1) [52,257,72,130,2] 13 := by
  apply FastRouting.sound _ _ [52,257,72,130,2] 13 (by decide) (choices 1) [16,64,128] r3614 c3614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u921
  · exact u922
  · exact u923

def b3615 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 259 76 138 48 242 210 210 466), lower := (rows 53 259 76 138 48 32 64 128 256), losses := [] }

theorem u3615 : Upper (D 1) (R 1) [52,257,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3615
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3616 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 386, targets := 64 }], pairs := [(1,6)], upper := (rows 53 259 76 138 80 178 242 178 434), lower := (rows 53 259 76 138 80 32 64 128 256), losses := [] }

theorem u3616 : Upper (D 1) (R 1) [52,257,72,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3616
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3617 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 259 76 138 144 114 114 242 370), lower := (rows 53 259 76 138 144 32 64 128 256), losses := [] }

theorem u3617 : Upper (D 1) (R 1) [52,257,72,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3617
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3618 : Route 9 := (fun mask => (mask,id))

def c3618 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3618 : Upper (D 1) (R 1) [52,257,192,66,2] 13 := by
  apply FastRouting.sound _ _ [52,257,192,66,2] 13 (by decide) (choices 1) [8,16,128] r3618 c3618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u924
  · exact u925
  · exact u926

def b3619 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 259 196 74 24 178 242 178 434), lower := (rows 53 259 196 74 24 32 64 128 256), losses := [] }

theorem u3619 : Upper (D 1) (R 1) [52,257,192,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3619
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3620 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 259 196 74 48 186 218 154 410), lower := (rows 53 259 196 74 48 32 64 128 256), losses := [] }

theorem u3620 : Upper (D 1) (R 1) [52,257,192,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3620
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3621 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 259 196 74 144 58 122 186 314), lower := (rows 53 259 196 74 144 32 64 128 256), losses := [] }

theorem u3621 : Upper (D 1) (R 1) [52,257,192,66,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3621
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3622 : Route 9 := (fun mask => (mask,id))

def c3622 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3622 : Upper (D 1) (R 1) [52,257,192,80,2] 13 := by
  apply FastRouting.sound _ _ [52,257,192,80,2] 13 (by decide) (choices 1) [2,8,128] r3622 c3622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u927
  · exact u928
  · exact u929

def b3623 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 259 196 88 24 162 226 162 418), lower := (rows 53 259 196 88 24 32 64 128 256), losses := [] }

theorem u3623 : Upper (D 1) (R 1) [52,257,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3623
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3624 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 259 196 88 48 170 202 138 394), lower := (rows 53 259 196 88 48 32 64 128 256), losses := [] }

theorem u3624 : Upper (D 1) (R 1) [52,257,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3624
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3625 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 259 196 88 144 42 106 170 298), lower := (rows 53 259 196 88 144 32 64 128 256), losses := [] }

theorem u3625 : Upper (D 1) (R 1) [52,257,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3625
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3626 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 266 7 200 18 240 240 240 496), lower := (rows 53 266 7 200 18 32 64 128 256), losses := [] }

theorem u3626 : Upper (D 1) (R 1) [52,264,3,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3626
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3627 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 266 7 200 48 242 210 210 466), lower := (rows 53 266 7 200 48 32 64 128 256), losses := [] }

theorem u3627 : Upper (D 1) (R 1) [52,264,3,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3627
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3628_2 : Upper (D 1) (R 1) [52,264,3,192,64,2] 13 :=
  permutation_upper _ _ _ [52,264,3,192,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u930

theorem m3628_16 : Upper (D 1) (R 1) [52,264,3,192,64,16] 13 :=
  permutation_upper _ _ _ [52,264,3,192,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u931

def r3628 : Route 9 := (fun mask => (mask,id))

def c3628 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3628 : Upper (D 1) (R 1) [52,264,3,192,64] 13 := by
  apply FastRouting.sound _ _ [52,264,3,192,64] 13 (by decide) (choices 1) [2,16,128] r3628 c3628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3628_2
  · exact m3628_16
  · exact u932

def b3629 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1)], upper := (rows 53 266 69 138 18 240 240 240 496), lower := (rows 53 266 69 138 18 32 64 128 256), losses := [] }

theorem u3629 : Upper (D 1) (R 1) [52,264,65,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3629
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3630 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 266 69 138 48 242 210 210 466), lower := (rows 53 266 69 138 48 32 64 128 256), losses := [] }

theorem u3630 : Upper (D 1) (R 1) [52,264,65,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3630
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3631 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 266 69 138 80 178 242 178 434), lower := (rows 53 266 69 138 80 32 64 128 256), losses := [] }

theorem u3631 : Upper (D 1) (R 1) [52,264,65,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3631
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3632_2 : Upper (D 1) (R 1) [52,264,65,130,128,2] 13 :=
  permutation_upper _ _ _ [52,264,65,130,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u933

theorem m3632_16 : Upper (D 1) (R 1) [52,264,65,130,128,16] 13 :=
  permutation_upper _ _ _ [52,264,65,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u934

theorem m3632_64 : Upper (D 1) (R 1) [52,264,65,130,128,64] 13 :=
  permutation_upper _ _ _ [52,264,65,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u935

def r3632 : Route 9 := (fun mask => (mask,id))

def c3632 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3632 : Upper (D 1) (R 1) [52,264,65,130,128] 13 := by
  apply FastRouting.sound _ _ [52,264,65,130,128] 13 (by decide) (choices 1) [2,16,64] r3632 c3632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3632_2
  · exact m3632_16
  · exact m3632_64

def b3633 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 266 70 137 18 240 240 240 496), lower := (rows 53 266 70 137 18 32 64 128 256), losses := [] }

theorem u3633 : Upper (D 1) (R 1) [52,264,66,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3633
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3634 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 266 70 137 48 242 210 210 466), lower := (rows 53 266 70 137 48 32 64 128 256), losses := [] }

theorem u3634 : Upper (D 1) (R 1) [52,264,66,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3634
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3635 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 266 70 137 80 178 242 178 434), lower := (rows 53 266 70 137 80 32 64 128 256), losses := [] }

theorem u3635 : Upper (D 1) (R 1) [52,264,66,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3635
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3636_2 : Upper (D 1) (R 1) [52,264,66,129,128,2] 13 :=
  permutation_upper _ _ _ [52,264,66,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u936

theorem m3636_16 : Upper (D 1) (R 1) [52,264,66,129,128,16] 13 :=
  permutation_upper _ _ _ [52,264,66,129,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u937

theorem m3636_64 : Upper (D 1) (R 1) [52,264,66,129,128,64] 13 :=
  permutation_upper _ _ _ [52,264,66,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u938

def r3636 : Route 9 := (fun mask => (mask,id))

def c3636 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3636 : Upper (D 1) (R 1) [52,264,66,129,128] 13 := by
  apply FastRouting.sound _ _ [52,264,66,129,128] 13 (by decide) (choices 1) [2,16,64] r3636 c3636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3636_2
  · exact m3636_16
  · exact m3636_64

def b3637 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 266 70 152 17 226 226 226 482), lower := (rows 53 266 70 152 17 32 64 128 256), losses := [] }

theorem u3637 : Upper (D 1) (R 1) [52,264,66,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3637
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3638 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 266 70 152 18 225 225 225 481), lower := (rows 53 266 70 152 18 32 64 128 256), losses := [] }

theorem u3638 : Upper (D 1) (R 1) [52,264,66,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3638
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3639 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 266 70 152 48 227 195 195 451), lower := (rows 53 266 70 152 48 32 64 128 256), losses := [] }

theorem u3639 : Upper (D 1) (R 1) [52,264,66,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3639
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3640 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 266 70 152 80 163 227 163 419), lower := (rows 53 266 70 152 80 32 64 128 256), losses := [] }

theorem u3640 : Upper (D 1) (R 1) [52,264,66,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3640
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3641 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 53 266 70 152 144 99 99 227 355), lower := (rows 53 266 70 152 144 32 64 128 256), losses := [] }

theorem u3641 : Upper (D 1) (R 1) [52,264,66,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3641
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3642 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1)], upper := (rows 53 266 196 11 18 240 240 240 496), lower := (rows 53 266 196 11 18 32 64 128 256), losses := [] }

theorem u3642 : Upper (D 1) (R 1) [52,264,192,3,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3642
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3643 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 266 196 11 48 242 210 210 466), lower := (rows 53 266 196 11 48 32 64 128 256), losses := [] }

theorem u3643 : Upper (D 1) (R 1) [52,264,192,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3643
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3644 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 266 196 11 80 178 242 178 434), lower := (rows 53 266 196 11 80 32 64 128 256), losses := [] }

theorem u3644 : Upper (D 1) (R 1) [52,264,192,3,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3644
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3645 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 266 196 26 17 226 226 226 482), lower := (rows 53 266 196 26 17 32 64 128 256), losses := [] }

theorem u3645 : Upper (D 1) (R 1) [52,264,192,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3645
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3646 : PairBound 9 := { available := 225, camps := [{ cop := 8, region := 26, targets := 32 }], pairs := [(1,5)], upper := (rows 53 266 196 26 18 225 225 225 481), lower := (rows 53 266 196 26 18 32 64 128 256), losses := [] }

theorem u3646 : Upper (D 1) (R 1) [52,264,192,18,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3646
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3647 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 266 196 26 48 227 195 195 451), lower := (rows 53 266 196 26 48 32 64 128 256), losses := [] }

theorem u3647 : Upper (D 1) (R 1) [52,264,192,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3647
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3648 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 266 196 26 80 163 227 163 419), lower := (rows 53 266 196 26 80 32 64 128 256), losses := [] }

theorem u3648 : Upper (D 1) (R 1) [52,264,192,18,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3648
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3649 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 266 196 74 17 178 242 178 434), lower := (rows 53 266 196 74 17 32 64 128 256), losses := [] }

theorem u3649 : Upper (D 1) (R 1) [52,264,192,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3649
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3650 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1)], upper := (rows 53 266 196 74 18 177 241 177 433), lower := (rows 53 266 196 74 18 32 64 128 256), losses := [] }

theorem u3650 : Upper (D 1) (R 1) [52,264,192,66,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3650
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3651 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 266 196 74 48 179 211 147 403), lower := (rows 53 266 196 74 48 32 64 128 256), losses := [] }

theorem u3651 : Upper (D 1) (R 1) [52,264,192,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3651
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3652 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 266 196 74 144 51 115 179 307), lower := (rows 53 266 196 74 144 32 64 128 256), losses := [] }

theorem u3652 : Upper (D 1) (R 1) [52,264,192,66,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3652
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3653 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 266 196 88 17 162 226 162 418), lower := (rows 53 266 196 88 17 32 64 128 256), losses := [] }

theorem u3653 : Upper (D 1) (R 1) [52,264,192,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3653
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3654 : Route 9 := (fun mask => (mask,id))

def c3654 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3654 : Upper (D 1) (R 1) [52,264,192,80,2] 13 := by
  apply FastRouting.sound _ _ [52,264,192,80,2] 13 (by decide) (choices 1) [1,2,128] r3654 c3654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u939
  · exact u940
  · exact u941

def b3655 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 266 196 88 48 163 195 131 387), lower := (rows 53 266 196 88 48 32 64 128 256), losses := [] }

theorem u3655 : Upper (D 1) (R 1) [52,264,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3655
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3656 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 266 196 88 144 35 99 163 291), lower := (rows 53 266 196 88 144 32 64 128 256), losses := [] }

theorem u3656 : Upper (D 1) (R 1) [52,264,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3656
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3657 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 274 14 200 17 226 226 226 482), lower := (rows 53 274 14 200 17 32 64 128 256), losses := [] }

theorem u3657 : Upper (D 1) (R 1) [52,272,10,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3657
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3658 : PairBound 9 := { available := 225, camps := [{ cop := 8, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 14 200 18 225 225 225 481), lower := (rows 53 274 14 200 18 32 64 128 256), losses := [] }

theorem u3658 : Upper (D 1) (R 1) [52,272,10,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3658
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3659 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 274 14 200 48 227 195 195 451), lower := (rows 53 274 14 200 48 32 64 128 256), losses := [] }

theorem u3659 : Upper (D 1) (R 1) [52,272,10,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3659
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u3659
end Delivery.IrregularNine14.P01
