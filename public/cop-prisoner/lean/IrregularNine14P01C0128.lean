import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0072
import IrregularNine14P01C0073

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7680 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 22 11 248 232 232 232 488), lower := (rows 113 262 22 11 16 32 64 128 256), losses := [] }

theorem u7680 : Upper (D 1) (R 1) [112,260,18,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7680
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7681 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 262 22 41 218 234 202 202 458), lower := (rows 113 262 22 41 16 32 64 128 256), losses := [] }

theorem u7681 : Upper (D 1) (R 1) [112,260,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7681
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7682 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 209, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 22 42 217 233 201 201 457), lower := (rows 113 262 22 42 16 32 64 128 256), losses := [] }

theorem u7682 : Upper (D 1) (R 1) [112,260,18,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7682
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7683 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 262 22 104 155 171 203 139 395), lower := (rows 113 262 22 104 16 32 64 128 256), losses := [] }

theorem u7683 : Upper (D 1) (R 1) [112,260,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7683
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7684 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7684 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7684 : Upper (D 1) (R 1) [112,260,18,129] 13 := by
  apply FastRouting.sound _ _ [112,260,18,129] 13 (by decide) (choices 1) [2,8,32,128] r7684 c7684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4344
  · exact u4345
  · exact u4346
  · exact u4347

def b7685 : PairBound 9 := { available := 233, camps := [{ cop := 3, region := 113, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 22 138 249 233 233 233 489), lower := (rows 113 262 22 138 16 32 64 128 256), losses := [] }

theorem u7685 : Upper (D 1) (R 1) [112,260,18,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7685
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7686 : Route 9 := (fun mask => (mask,id))

def c7686 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7686 : Upper (D 1) (R 1) [112,260,18,160] 13 := by
  apply FastRouting.sound _ _ [112,260,18,160] 13 (by decide) (choices 1) [1,2,8,64,128] r7686 c7686
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4348
  · exact u4349
  · exact u4350
  · exact u4351
  · exact u4352

def b7687 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 113 262 28 11 242 226 226 226 482), lower := (rows 113 262 28 11 16 32 64 128 256), losses := [] }

theorem u7687 : Upper (D 1) (R 1) [112,260,24,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7687
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7688 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 262 28 41 210 226 194 194 450), lower := (rows 113 262 28 41 16 32 64 128 256), losses := [] }

theorem u7688 : Upper (D 1) (R 1) [112,260,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7688
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7689 : Route 9 := (fun mask => (mask,id))

def c7689 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7689 : Upper (D 1) (R 1) [112,260,24,34] 13 := by
  apply FastRouting.sound _ _ [112,260,24,34] 13 (by decide) (choices 1) [1,2,64,128] r7689 c7689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4353
  · exact u4354
  · exact u4355
  · exact u4356

def b7690 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 262 28 104 147 163 195 131 387), lower := (rows 113 262 28 104 16 32 64 128 256), losses := [] }

theorem u7690 : Upper (D 1) (R 1) [112,260,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7690
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7691 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 113 262 28 137 242 226 226 226 482), lower := (rows 113 262 28 137 16 32 64 128 256), losses := [] }

theorem u7691 : Upper (D 1) (R 1) [112,260,24,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7691
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7692 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7692 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7692 : Upper (D 1) (R 1) [112,260,24,130] 13 := by
  apply FastRouting.sound _ _ [112,260,24,130] 13 (by decide) (choices 1) [1,2,32,128] r7692 c7692
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4357
  · exact u4358
  · exact u4359
  · exact u4360

def r7693 : Route 9 := (fun mask => (mask,id))

def c7693 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7693 : Upper (D 1) (R 1) [112,260,24,160] 13 := by
  apply FastRouting.sound _ _ [112,260,24,160] 13 (by decide) (choices 1) [1,2,64,128] r7693 c7693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4361
  · exact u4362
  · exact u4363
  · exact u4364

def r7694 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7694 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7694 : Upper (D 1) (R 1) [112,260,129,18] 13 := by
  apply FastRouting.sound _ _ [112,260,129,18] 13 (by decide) (choices 1) [2,8,32,128] r7694 c7694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4365
  · exact u4366
  · exact u4367
  · exact u4368

def b7695 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 262 133 56 218 234 202 202 458), lower := (rows 113 262 133 56 16 32 64 128 256), losses := [] }

theorem u7695 : Upper (D 1) (R 1) [112,260,129,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7695
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7696 : PairBound 9 := { available := 122, camps := [{ cop := 3, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 262 133 138 122 122 122 250 378), lower := (rows 113 262 133 138 16 32 64 128 256), losses := [] }

theorem u7696 : Upper (D 1) (R 1) [112,260,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7696
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7697 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7697 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7697 : Upper (D 1) (R 1) [112,260,129,144] 13 := by
  apply FastRouting.sound _ _ [112,260,129,144] 13 (by decide) (choices 1) [2,8,32] r7697 c7697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4369
  · exact u4370
  · exact u4371

def b7698 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 134 11 248 248 248 248 504), lower := (rows 113 262 134 11 16 32 64 128 256), losses := [] }

theorem u7698 : Upper (D 1) (R 1) [112,260,130,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7698
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7699 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 262 134 25 250 234 234 234 490), lower := (rows 113 262 134 25 16 32 64 128 256), losses := [] }

theorem u7699 : Upper (D 1) (R 1) [112,260,130,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7699
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7700 : PairBound 9 := { available := 233, camps := [{ cop := 3, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 134 26 249 233 233 233 489), lower := (rows 113 262 134 26 16 32 64 128 256), losses := [] }

theorem u7700 : Upper (D 1) (R 1) [112,260,130,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7700
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7701 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 262 134 56 219 235 203 203 459), lower := (rows 113 262 134 56 16 32 64 128 256), losses := [] }

theorem u7701 : Upper (D 1) (R 1) [112,260,130,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7701
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7702 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7702 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7702 : Upper (D 1) (R 1) [112,260,130,129] 13 := by
  apply FastRouting.sound _ _ [112,260,130,129] 13 (by decide) (choices 1) [2,8,32] r7702 c7702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4372
  · exact u4373
  · exact u4374

def b7703 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 262 134 138 121 121 121 249 377), lower := (rows 113 262 134 138 16 32 64 128 256), losses := [] }

theorem u7703 : Upper (D 1) (R 1) [112,260,130,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7703
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7704 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7704 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7704 : Upper (D 1) (R 1) [112,260,130,144] 13 := by
  apply FastRouting.sound _ _ [112,260,130,144] 13 (by decide) (choices 1) [1,2,8,32] r7704 c7704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4375
  · exact u4376
  · exact u4377
  · exact u4378

def r7705 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7705 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7705 : Upper (D 1) (R 1) [112,260,136,3] 13 := by
  apply FastRouting.sound _ _ [112,260,136,3] 13 (by decide) (choices 1) [2,32,128] r7705 c7705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4379
  · exact u4380
  · exact u4381

def b7706 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 262 140 25 242 226 226 226 482), lower := (rows 113 262 140 25 16 32 64 128 256), losses := [] }

theorem u7706 : Upper (D 1) (R 1) [112,260,136,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7706
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7707 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7707 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7707 : Upper (D 1) (R 1) [112,260,136,18] 13 := by
  apply FastRouting.sound _ _ [112,260,136,18] 13 (by decide) (choices 1) [1,2,32,128] r7707 c7707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4382
  · exact u4383
  · exact u4384
  · exact u4385

def b7708 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 262 140 56 211 227 195 195 451), lower := (rows 113 262 140 56 16 32 64 128 256), losses := [] }

theorem u7708 : Upper (D 1) (R 1) [112,260,136,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7708
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7709 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 262 140 137 114 114 114 242 370), lower := (rows 113 262 140 137 16 32 64 128 256), losses := [] }

theorem u7709 : Upper (D 1) (R 1) [112,260,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7709
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7710 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 262 140 138 115 115 115 243 371), lower := (rows 113 262 140 138 16 32 64 128 256), losses := [] }

theorem u7710 : Upper (D 1) (R 1) [112,260,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7710
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7711 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 262 140 152 115 99 99 227 355), lower := (rows 113 262 140 152 16 32 64 128 256), losses := [] }

theorem u7711 : Upper (D 1) (R 1) [112,260,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7711
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7712 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7712 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7712 : Upper (D 1) (R 1) [112,260,144,3] 13 := by
  apply FastRouting.sound _ _ [112,260,144,3] 13 (by decide) (choices 1) [2,8,32,128] r7712 c7712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4386
  · exact u4387
  · exact u4388
  · exact u4389

def b7713 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 262 148 41 218 234 202 202 458), lower := (rows 113 262 148 41 16 32 64 128 256), losses := [] }

theorem u7713 : Upper (D 1) (R 1) [112,260,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7713
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7714 : Route 9 := (fun mask => (mask,id))

def c7714 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7714 : Upper (D 1) (R 1) [112,260,144,34] 13 := by
  apply FastRouting.sound _ _ [112,260,144,34] 13 (by decide) (choices 1) [1,2,8,64,128] r7714 c7714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4390
  · exact u4391
  · exact u4392
  · exact u4393
  · exact u4394

def b7715 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 262 148 104 155 171 203 139 395), lower := (rows 113 262 148 104 16 32 64 128 256), losses := [] }

theorem u7715 : Upper (D 1) (R 1) [112,260,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7715
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7716 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7716 : Upper (D 1) (R 1) [112,260,144,129] 13 := by
  apply FastRouting.sound _ _ [112,260,144,129] 13 (by decide) (choices 1) [2,8,32] r7716 c7716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4395
  · exact u4396
  · exact u4397

def b7717 : PairBound 9 := { available := 107, camps := [{ cop := 3, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 262 148 138 123 107 107 235 363), lower := (rows 113 262 148 138 16 32 64 128 256), losses := [] }

theorem u7717 : Upper (D 1) (R 1) [112,260,144,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7717
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7718 : Route 9 := (fun mask => (mask,id))

def c7718 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7718 : Upper (D 1) (R 1) [112,260,144,160] 13 := by
  apply FastRouting.sound _ _ [112,260,144,160] 13 (by decide) (choices 1) [1,2,8,64] r7718 c7718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4398
  · exact u4399
  · exact u4400
  · exact u4401

def b7719 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 113 274 7 14 248 232 232 232 488), lower := (rows 113 274 7 14 16 32 64 128 256), losses := [] }

theorem u7719 : Upper (D 1) (R 1) [112,272,3,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7719
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7720 : PairBound 9 := { available := 204, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 274 7 42 220 236 204 204 460), lower := (rows 113 274 7 42 16 32 64 128 256), losses := [] }

theorem u7720 : Upper (D 1) (R 1) [112,272,3,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7720
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7721 : PairBound 9 := { available := 202, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 274 7 44 218 234 202 202 458), lower := (rows 113 274 7 44 16 32 64 128 256), losses := [] }

theorem u7721 : Upper (D 1) (R 1) [112,272,3,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7721
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7722 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 274 7 138 252 236 236 236 492), lower := (rows 113 274 7 138 16 32 64 128 256), losses := [] }

theorem u7722 : Upper (D 1) (R 1) [112,272,3,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7722
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7723 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 274 7 140 250 234 234 234 490), lower := (rows 113 274 7 140 16 32 64 128 256), losses := [] }

theorem u7723 : Upper (D 1) (R 1) [112,272,3,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7723
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7724 : PairBound 9 := { available := 206, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 274 7 168 222 238 206 206 462), lower := (rows 113 274 7 168 16 32 64 128 256), losses := [] }

theorem u7724 : Upper (D 1) (R 1) [112,272,3,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7724
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7725 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7725 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7725 : Upper (D 1) (R 1) [112,272,9,6] 13 := by
  apply FastRouting.sound _ _ [112,272,9,6] 13 (by decide) (choices 1) [2,32,128] r7725 c7725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4402
  · exact u4403
  · exact u4404

def b7726 : PairBound 9 := { available := 198, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 13 42 214 230 198 198 454), lower := (rows 113 274 13 42 16 32 64 128 256), losses := [] }

theorem u7726 : Upper (D 1) (R 1) [112,272,9,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7726
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7727 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 13 44 210 226 194 194 450), lower := (rows 113 274 13 44 16 32 64 128 256), losses := [] }

theorem u7727 : Upper (D 1) (R 1) [112,272,9,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7727
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7728 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 13 104 150 166 198 134 390), lower := (rows 113 274 13 104 16 32 64 128 256), losses := [] }

theorem u7728 : Upper (D 1) (R 1) [112,272,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7728
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7729 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7729 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u7729 : Upper (D 1) (R 1) [112,272,9,130] 13 := by
  apply FastRouting.sound _ _ [112,272,9,130] 13 (by decide) (choices 1) [2,4,32,128] r7729 c7729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4405
  · exact u4406
  · exact u4407
  · exact u4408

def r7730 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7730 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7730 : Upper (D 1) (R 1) [112,272,9,132] 13 := by
  apply FastRouting.sound _ _ [112,272,9,132] 13 (by decide) (choices 1) [2,32,128] r7730 c7730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4409
  · exact u4410
  · exact u4411

def b7731 : PairBound 9 := { available := 198, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 13 168 214 230 198 198 454), lower := (rows 113 274 13 168 16 32 64 128 256), losses := [] }

theorem u7731 : Upper (D 1) (R 1) [112,272,9,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7731
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7732 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 113 274 14 14 241 225 225 225 481), lower := (rows 113 274 14 14 16 32 64 128 256), losses := [] }

theorem u7732 : Upper (D 1) (R 1) [112,272,10,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7732
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7733 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 274 14 41 214 230 198 198 454), lower := (rows 113 274 14 41 16 32 64 128 256), losses := [] }

theorem u7733 : Upper (D 1) (R 1) [112,272,10,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7733
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7734 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 274 14 42 213 229 197 197 453), lower := (rows 113 274 14 42 16 32 64 128 256), losses := [] }

theorem u7734 : Upper (D 1) (R 1) [112,272,10,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7734
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7735 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 14 44 211 227 195 195 451), lower := (rows 113 274 14 44 16 32 64 128 256), losses := [] }

theorem u7735 : Upper (D 1) (R 1) [112,272,10,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7735
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7736 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 274 14 104 151 167 199 135 391), lower := (rows 113 274 14 104 16 32 64 128 256), losses := [] }

theorem u7736 : Upper (D 1) (R 1) [112,272,10,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7736
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7737 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7737 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u7737 : Upper (D 1) (R 1) [112,272,10,129] 13 := by
  apply FastRouting.sound _ _ [112,272,10,129] 13 (by decide) (choices 1) [2,4,32,128] r7737 c7737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4412
  · exact u4413
  · exact u4414
  · exact u4415

def b7738 : PairBound 9 := { available := 229, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 274 14 138 245 229 229 229 485), lower := (rows 113 274 14 138 16 32 64 128 256), losses := [] }

theorem u7738 : Upper (D 1) (R 1) [112,272,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7738
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7739 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7739 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7739 : Upper (D 1) (R 1) [112,272,10,132] 13 := by
  apply FastRouting.sound _ _ [112,272,10,132] 13 (by decide) (choices 1) [1,2,32,128] r7739 c7739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4416
  · exact u4417
  · exact u4418
  · exact u4419

#print axioms u7739
end Delivery.IrregularNine14.P01
