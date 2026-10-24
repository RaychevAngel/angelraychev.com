import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0073
import IrregularNine14P01C0074
import IrregularNine14P01C0075

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7740 : Route 9 := (fun mask => (mask,id))

def c7740 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7740 : Upper (D 1) (R 1) [112,272,10,160] 13 := by
  apply FastRouting.sound _ _ [112,272,10,160] 13 (by decide) (choices 1) [1,2,4,64,128] r7740 c7740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4420
  · exact u4421
  · exact u4422
  · exact u4423
  · exact u4424

def b7741 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 37 74 158 174 206 142 398), lower := (rows 113 274 37 74 16 32 64 128 256), losses := [] }

theorem u7741 : Upper (D 1) (R 1) [112,272,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7741
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7742 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 37 76 154 170 202 138 394), lower := (rows 113 274 37 76 16 32 64 128 256), losses := [] }

theorem u7742 : Upper (D 1) (R 1) [112,272,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7742
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7743 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 37 138 222 238 206 206 462), lower := (rows 113 274 37 138 16 32 64 128 256), losses := [] }

theorem u7743 : Upper (D 1) (R 1) [112,272,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7743
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7744 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 37 140 218 234 202 202 458), lower := (rows 113 274 37 140 16 32 64 128 256), losses := [] }

theorem u7744 : Upper (D 1) (R 1) [112,272,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7744
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7745 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 37 200 158 174 206 142 398), lower := (rows 113 274 37 200 16 32 64 128 256), losses := [] }

theorem u7745 : Upper (D 1) (R 1) [112,272,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7745
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m7746_8 : Upper (D 1) (R 1) [112,272,34,66,8] 13 :=
  permutation_upper _ _ _ [112,272,34,66,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4426

def r7746 : Route 9 := (fun mask => (mask,id))

def c7746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7746 : Upper (D 1) (R 1) [112,272,34,66] 13 := by
  apply FastRouting.sound _ _ [112,272,34,66] 13 (by decide) (choices 1) [1,4,8,128] r7746 c7746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4425
  · exact u4426
  · exact m7746_8
  · exact u4427

def r7747 : Route 9 := (fun mask => (mask,id))

def c7747 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7747 : Upper (D 1) (R 1) [112,272,34,68] 13 := by
  apply FastRouting.sound _ _ [112,272,34,68] 13 (by decide) (choices 1) [1,2,8,128] r7747 c7747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4428
  · exact u4429
  · exact u4430
  · exact u4431

def r7748 : Route 9 := (fun mask => (mask,id))

def c7748 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 256 => 8 | _ => 0)

theorem u7748 : Upper (D 1) (R 1) [112,272,34,129] 13 := by
  apply FastRouting.sound _ _ [112,272,34,129] 13 (by decide) (choices 1) [2,4,8,64,128] r7748 c7748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4432
  · exact u4433
  · exact u4434
  · exact u4435
  · exact u4436

def r7749 : Route 9 := (fun mask => (mask,id))

def c7749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7749 : Upper (D 1) (R 1) [112,272,34,130] 13 := by
  apply FastRouting.sound _ _ [112,272,34,130] 13 (by decide) (choices 1) [1,4,8,64,128] r7749 c7749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4437
  · exact u4438
  · exact u4439
  · exact u4440
  · exact u4441

def r7750 : Route 9 := (fun mask => (mask,id))

def c7750 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7750 : Upper (D 1) (R 1) [112,272,34,132] 13 := by
  apply FastRouting.sound _ _ [112,272,34,132] 13 (by decide) (choices 1) [1,2,8,64,128] r7750 c7750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4442
  · exact u4443
  · exact u4444
  · exact u4445
  · exact u4446

def r7751 : Route 9 := (fun mask => (mask,id))

def c7751 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7751 : Upper (D 1) (R 1) [112,272,34,192] 13 := by
  apply FastRouting.sound _ _ [112,272,34,192] 13 (by decide) (choices 1) [1,2,4,8,128] r7751 c7751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4447
  · exact u4448
  · exact u4449
  · exact u4450
  · exact u4451

def b7752 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 44 76 147 163 195 131 387), lower := (rows 113 274 44 76 16 32 64 128 256), losses := [] }

theorem u7752 : Upper (D 1) (R 1) [112,272,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7752
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7753 : PairBound 9 := { available := 198, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 44 137 214 230 198 198 454), lower := (rows 113 274 44 137 16 32 64 128 256), losses := [] }

theorem u7753 : Upper (D 1) (R 1) [112,272,40,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7753
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7754 : Route 9 := (fun mask => (mask,id))

def c7754 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7754 : Upper (D 1) (R 1) [112,272,40,130] 13 := by
  apply FastRouting.sound _ _ [112,272,40,130] 13 (by decide) (choices 1) [1,2,4,64,128] r7754 c7754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4452
  · exact u4453
  · exact u4454
  · exact u4455
  · exact u4456

def b7755 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 44 140 211 227 195 195 451), lower := (rows 113 274 44 140 16 32 64 128 256), losses := [] }

theorem u7755 : Upper (D 1) (R 1) [112,272,40,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7755
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7756 : Route 9 := (fun mask => (mask,id))

def c7756 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7756 : Upper (D 1) (R 1) [112,272,40,192] 13 := by
  apply FastRouting.sound _ _ [112,272,40,192] 13 (by decide) (choices 1) [1,2,4,128] r7756 c7756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4457
  · exact u4458
  · exact u4459
  · exact u4460

def b7757 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 100 137 158 174 206 142 398), lower := (rows 113 274 100 137 16 32 64 128 256), losses := [] }

theorem u7757 : Upper (D 1) (R 1) [112,272,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7757
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7758 : PairBound 9 := { available := 143, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 100 138 159 175 207 143 399), lower := (rows 113 274 100 138 16 32 64 128 256), losses := [] }

theorem u7758 : Upper (D 1) (R 1) [112,272,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7758
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7759 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 100 140 155 171 203 139 395), lower := (rows 113 274 100 140 16 32 64 128 256), losses := [] }

theorem u7759 : Upper (D 1) (R 1) [112,272,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7759
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7760 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7760 : Nat → Fin 9 := (fun mask => match mask with | 128 => 7 | 256 => 8 | _ => 0)

theorem u7760 : Upper (D 1) (R 1) [112,272,129,130] 13 := by
  apply FastRouting.sound _ _ [112,272,129,130] 13 (by decide) (choices 1) [2,4,8,32] r7760 c7760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4461
  · exact u4462
  · exact u4463
  · exact u4464

def b7761 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 274 133 140 122 106 106 234 362), lower := (rows 113 274 133 140 16 32 64 128 256), losses := [] }

theorem u7761 : Upper (D 1) (R 1) [112,272,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7761
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7762 : Route 9 := (fun mask => (mask,id))

def c7762 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7762 : Upper (D 1) (R 1) [112,272,129,160] 13 := by
  apply FastRouting.sound _ _ [112,272,129,160] 13 (by decide) (choices 1) [2,4,8,64] r7762 c7762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4465
  · exact u4466
  · exact u4467
  · exact u4468

def b7763 : PairBound 9 := { available := 109, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 274 134 138 125 109 109 237 365), lower := (rows 113 274 134 138 16 32 64 128 256), losses := [] }

theorem u7763 : Upper (D 1) (R 1) [112,272,130,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7763
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7764 : PairBound 9 := { available := 107, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 274 134 140 123 107 107 235 363), lower := (rows 113 274 134 140 16 32 64 128 256), losses := [] }

theorem u7764 : Upper (D 1) (R 1) [112,272,130,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7764
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7765 : Route 9 := (fun mask => (mask,id))

def c7765 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7765 : Upper (D 1) (R 1) [112,272,130,160] 13 := by
  apply FastRouting.sound _ _ [112,272,130,160] 13 (by decide) (choices 1) [1,2,4,8,64] r7765 c7765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4469
  · exact u4470
  · exact u4471
  · exact u4472
  · exact u4473

def b7766 : PairBound 9 := { available := 99, camps := [{ cop := 7, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 140 140 115 99 99 227 355), lower := (rows 113 274 140 140 16 32 64 128 256), losses := [] }

theorem u7766 : Upper (D 1) (R 1) [112,272,136,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7766
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7767 : PairBound 9 := { available := 71, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 140 168 87 103 71 199 327), lower := (rows 113 274 140 168 16 32 64 128 256), losses := [] }

theorem u7767 : Upper (D 1) (R 1) [112,272,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7767
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m7768_8 : Upper (D 1) (R 1) [112,272,160,192,8] 13 :=
  permutation_upper _ _ _ [112,272,160,192,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4476

def r7768 : Route 9 := (fun mask => (mask,id))

def c7768 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7768 : Upper (D 1) (R 1) [112,272,160,192] 13 := by
  apply FastRouting.sound _ _ [112,272,160,192] 13 (by decide) (choices 1) [1,2,4,8] r7768 c7768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4474
  · exact u4475
  · exact u4476
  · exact m7768_8

def b7769 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 386 7 14 248 248 248 248 504), lower := (rows 113 386 7 14 16 32 64 128 256), losses := [] }

theorem u7769 : Upper (D 1) (R 1) [112,384,3,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7769
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7770 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 256 => 8 | _ => 0)

theorem u7770 : Upper (D 1) (R 1) [112,384,3,18] 13 := by
  apply FastRouting.sound _ _ [112,384,3,18] 13 (by decide) (choices 1) [4,8,32,128] r7770 c7770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4477
  · exact u4478
  · exact u4479
  · exact u4480

def b7771 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 113 386 7 28 250 234 234 234 490), lower := (rows 113 386 7 28 16 32 64 128 256), losses := [] }

theorem u7771 : Upper (D 1) (R 1) [112,384,3,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7771
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7772 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 386 7 56 222 238 206 206 462), lower := (rows 113 386 7 56 16 32 64 128 256), losses := [] }

theorem u7772 : Upper (D 1) (R 1) [112,384,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7772
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7773 : PairBound 9 := { available := 124, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 386 7 138 124 124 124 252 380), lower := (rows 113 386 7 138 16 32 64 128 256), losses := [] }

theorem u7773 : Upper (D 1) (R 1) [112,384,3,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7773
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7774 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7774 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7774 : Upper (D 1) (R 1) [112,384,3,132] 13 := by
  apply FastRouting.sound _ _ [112,384,3,132] 13 (by decide) (choices 1) [2,8,32] r7774 c7774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4481
  · exact u4482
  · exact u4483

def r7775 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7775 : Nat → Fin 9 := (fun mask => match mask with | 128 => 7 | 256 => 8 | _ => 0)

theorem u7775 : Upper (D 1) (R 1) [112,384,3,144] 13 := by
  apply FastRouting.sound _ _ [112,384,3,144] 13 (by decide) (choices 1) [2,4,8,32] r7775 c7775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4484
  · exact u4485
  · exact u4486
  · exact u4487

def r7776 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7776 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7776 : Upper (D 1) (R 1) [112,384,9,6] 13 := by
  apply FastRouting.sound _ _ [112,384,9,6] 13 (by decide) (choices 1) [2,32,128] r7776 c7776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4488
  · exact u4489
  · exact u4490

def b7777 : PairBound 9 := { available := 230, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 113 386 13 26 246 230 230 230 486), lower := (rows 113 386 13 26 16 32 64 128 256), losses := [] }

theorem u7777 : Upper (D 1) (R 1) [112,384,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7777
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7778 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 386 13 28 242 226 226 226 482), lower := (rows 113 386 13 28 16 32 64 128 256), losses := [] }

theorem u7778 : Upper (D 1) (R 1) [112,384,9,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7778
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7779 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 386 13 56 214 230 198 198 454), lower := (rows 113 386 13 56 16 32 64 128 256), losses := [] }

theorem u7779 : Upper (D 1) (R 1) [112,384,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7779
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7780 : PairBound 9 := { available := 118, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 386 13 138 118 118 118 246 374), lower := (rows 113 386 13 138 16 32 64 128 256), losses := [] }

theorem u7780 : Upper (D 1) (R 1) [112,384,9,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7780
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7781 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 386 13 140 114 114 114 242 370), lower := (rows 113 386 13 140 16 32 64 128 256), losses := [] }

theorem u7781 : Upper (D 1) (R 1) [112,384,9,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7781
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7782 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 113 386 13 152 118 102 102 230 358), lower := (rows 113 386 13 152 16 32 64 128 256), losses := [] }

theorem u7782 : Upper (D 1) (R 1) [112,384,9,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7782
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7783 : PairBound 9 := { available := 241, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 113 386 14 14 241 241 241 241 497), lower := (rows 113 386 14 14 16 32 64 128 256), losses := [] }

theorem u7783 : Upper (D 1) (R 1) [112,384,10,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7783
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7784 : PairBound 9 := { available := 230, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 386 14 25 246 230 230 230 486), lower := (rows 113 386 14 25 16 32 64 128 256), losses := [] }

theorem u7784 : Upper (D 1) (R 1) [112,384,10,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7784
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7785 : PairBound 9 := { available := 229, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 386 14 26 245 229 229 229 485), lower := (rows 113 386 14 26 16 32 64 128 256), losses := [] }

theorem u7785 : Upper (D 1) (R 1) [112,384,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7785
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7786 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 386, targets := 16 }], pairs := [(1,4)], upper := (rows 113 386 14 28 243 227 227 227 483), lower := (rows 113 386 14 28 16 32 64 128 256), losses := [] }

theorem u7786 : Upper (D 1) (R 1) [112,384,10,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7786
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7787 : PairBound 9 := { available := 199, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 386 14 56 215 231 199 199 455), lower := (rows 113 386 14 56 16 32 64 128 256), losses := [] }

theorem u7787 : Upper (D 1) (R 1) [112,384,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7787
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7788 : PairBound 9 := { available := 118, camps := [{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 386 14 137 118 118 118 246 374), lower := (rows 113 386 14 137 16 32 64 128 256), losses := [] }

theorem u7788 : Upper (D 1) (R 1) [112,384,10,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7788
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7789 : PairBound 9 := { available := 117, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 113 386 14 138 117 117 117 245 373), lower := (rows 113 386 14 138 16 32 64 128 256), losses := [] }

theorem u7789 : Upper (D 1) (R 1) [112,384,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7789
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7790 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 113 386 14 140 115 115 115 243 371), lower := (rows 113 386 14 140 16 32 64 128 256), losses := [] }

theorem u7790 : Upper (D 1) (R 1) [112,384,10,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7790
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7791 : PairBound 9 := { available := 103, camps := [{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 386 14 152 119 103 103 231 359), lower := (rows 113 386 14 152 16 32 64 128 256), losses := [] }

theorem u7791 : Upper (D 1) (R 1) [112,384,10,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7791
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7792 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 386 21 42 222 238 206 206 462), lower := (rows 113 386 21 42 16 32 64 128 256), losses := [] }

theorem u7792 : Upper (D 1) (R 1) [112,384,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7792
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7793 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 386 21 44 218 234 202 202 458), lower := (rows 113 386 21 44 16 32 64 128 256), losses := [] }

theorem u7793 : Upper (D 1) (R 1) [112,384,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7793
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7794 : PairBound 9 := { available := 106, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 386 21 140 122 106 106 234 362), lower := (rows 113 386 21 140 16 32 64 128 256), losses := [] }

theorem u7794 : Upper (D 1) (R 1) [112,384,17,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7794
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7795 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 386 21 168 94 110 78 206 334), lower := (rows 113 386 21 168 16 32 64 128 256), losses := [] }

theorem u7795 : Upper (D 1) (R 1) [112,384,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7795
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7796 : Route 9 := (fun mask => (mask,id))

def c7796 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7796 : Upper (D 1) (R 1) [112,384,18,34] 13 := by
  apply FastRouting.sound _ _ [112,384,18,34] 13 (by decide) (choices 1) [1,4,8,64,128] r7796 c7796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4491
  · exact u4492
  · exact u4493
  · exact u4494
  · exact u4495

def r7797 : Route 9 := (fun mask => (mask,id))

def c7797 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7797 : Upper (D 1) (R 1) [112,384,18,36] 13 := by
  apply FastRouting.sound _ _ [112,384,18,36] 13 (by decide) (choices 1) [1,2,8,64,128] r7797 c7797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4496
  · exact u4497
  · exact u4498
  · exact u4499
  · exact u4500

def b7798 : PairBound 9 := { available := 143, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 386 22 104 159 175 207 143 399), lower := (rows 113 386 22 104 16 32 64 128 256), losses := [] }

theorem u7798 : Upper (D 1) (R 1) [112,384,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7798
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7799 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7799 : Nat → Fin 9 := (fun mask => match mask with | 128 => 7 | 256 => 8 | _ => 0)

theorem u7799 : Upper (D 1) (R 1) [112,384,18,129] 13 := by
  apply FastRouting.sound _ _ [112,384,18,129] 13 (by decide) (choices 1) [2,4,8,32] r7799 c7799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4501
  · exact u4502
  · exact u4503
  · exact u4504

#print axioms u7799
end Delivery.IrregularNine14.P01
