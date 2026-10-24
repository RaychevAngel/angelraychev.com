import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0022
import IrregularNine14P01C0023

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4680 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 76 140 48 242 210 210 466), lower := (rows 275 35 76 140 48 32 64 128 256), losses := [] }

theorem u4680 : Upper (D 1) (R 1) [274,33,72,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4680
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4681 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 275 35 76 140 80 178 242 178 434), lower := (rows 275 35 76 140 80 32 64 128 256), losses := [] }

theorem u4681 : Upper (D 1) (R 1) [274,33,72,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4681
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4682 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 76 152 18 228 228 228 484), lower := (rows 275 35 76 152 18 32 64 128 256), losses := [] }

theorem u4682 : Upper (D 1) (R 1) [274,33,72,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4682
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4683 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 275 35 76 152 20 226 226 226 482), lower := (rows 275 35 76 152 20 32 64 128 256), losses := [] }

theorem u4683 : Upper (D 1) (R 1) [274,33,72,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4683
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4684 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 76 152 48 230 198 198 454), lower := (rows 275 35 76 152 48 32 64 128 256), losses := [] }

theorem u4684 : Upper (D 1) (R 1) [274,33,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4684
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4685 : Route 9 := (fun mask => (mask,id))

def c4685 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4685 : Upper (D 1) (R 1) [274,33,72,144,64] 13 := by
  apply FastRouting.sound _ _ [274,33,72,144,64] 13 (by decide) (choices 1) [2,4,128] r4685 c4685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1353
  · exact u1354
  · exact u1355

def b4686 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 275 35 76 152 144 102 102 230 358), lower := (rows 275 35 76 152 144 32 64 128 256), losses := [] }

theorem u4686 : Upper (D 1) (R 1) [274,33,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4686
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4687 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 76 168 18 244 212 212 468), lower := (rows 275 35 76 168 18 32 64 128 256), losses := [] }

theorem u4687 : Upper (D 1) (R 1) [274,33,72,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4687
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4688 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 275 35 76 168 20 242 210 210 466), lower := (rows 275 35 76 168 20 32 64 128 256), losses := [] }

theorem u4688 : Upper (D 1) (R 1) [274,33,72,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4688
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4689 : Route 9 := (fun mask => (mask,id))

def c4689 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4689 : Upper (D 1) (R 1) [274,33,72,160,64] 13 := by
  apply FastRouting.sound _ _ [274,33,72,160,64] 13 (by decide) (choices 1) [2,4,16,128] r4689 c4689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1356
  · exact u1357
  · exact u1358
  · exact u1359

def r4690 : Route 9 := (fun mask => (mask,id))

def c4690 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4690 : Upper (D 1) (R 1) [274,33,72,160,128] 13 := by
  apply FastRouting.sound _ _ [274,33,72,160,128] 13 (by decide) (choices 1) [2,4,16,64] r4690 c4690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1360
  · exact u1361
  · exact u1362
  · exact u1363

def b4691 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 84 104 18 172 204 140 396), lower := (rows 275 35 84 104 18 32 64 128 256), losses := [] }

theorem u4691 : Upper (D 1) (R 1) [274,33,80,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4691
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4692 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 275 35 84 104 20 170 202 138 394), lower := (rows 275 35 84 104 20 32 64 128 256), losses := [] }

theorem u4692 : Upper (D 1) (R 1) [274,33,80,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4692
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4693 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 275 35 84 104 24 166 198 134 390), lower := (rows 275 35 84 104 24 32 64 128 256), losses := [] }

theorem u4693 : Upper (D 1) (R 1) [274,33,80,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4693
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4694 : Route 9 := (fun mask => (mask,id))

def c4694 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4694 : Upper (D 1) (R 1) [274,33,80,96,128] 13 := by
  apply FastRouting.sound _ _ [274,33,80,96,128] 13 (by decide) (choices 1) [2,4,8,128] r4694 c4694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1364
  · exact u1365
  · exact u1366
  · exact u1367

def b4695 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 84 168 18 236 204 204 460), lower := (rows 275 35 84 168 18 32 64 128 256), losses := [] }

theorem u4695 : Upper (D 1) (R 1) [274,33,80,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4695
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4696 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 275 35 84 168 20 234 202 202 458), lower := (rows 275 35 84 168 20 32 64 128 256), losses := [] }

theorem u4696 : Upper (D 1) (R 1) [274,33,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4696
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4697 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 275 35 84 168 24 230 198 198 454), lower := (rows 275 35 84 168 24 32 64 128 256), losses := [] }

theorem u4697 : Upper (D 1) (R 1) [274,33,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4697
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4698 : PairBound 9 := { available := 142, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 275 35 84 168 80 174 206 142 398), lower := (rows 275 35 84 168 80 32 64 128 256), losses := [] }

theorem u4698 : Upper (D 1) (R 1) [274,33,80,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4698
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4699 : Route 9 := (fun mask => (mask,id))

def c4699 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4699 : Upper (D 1) (R 1) [274,33,80,160,128] 13 := by
  apply FastRouting.sound _ _ [274,33,80,160,128] 13 (by decide) (choices 1) [2,4,8,64] r4699 c4699
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1368
  · exact u1369
  · exact u1370
  · exact u1371

def b4700 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 84 200 18 172 236 172 428), lower := (rows 275 35 84 200 18 32 64 128 256), losses := [] }

theorem u4700 : Upper (D 1) (R 1) [274,33,80,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4700
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4701 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 275 35 84 200 20 170 234 170 426), lower := (rows 275 35 84 200 20 32 64 128 256), losses := [] }

theorem u4701 : Upper (D 1) (R 1) [274,33,80,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4701
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4702 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 275 35 84 200 24 166 230 166 422), lower := (rows 275 35 84 200 24 32 64 128 256), losses := [] }

theorem u4702 : Upper (D 1) (R 1) [274,33,80,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4702
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4703 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 84 200 48 174 206 142 398), lower := (rows 275 35 84 200 48 32 64 128 256), losses := [] }

theorem u4703 : Upper (D 1) (R 1) [274,33,80,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4703
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4704 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 84 200 144 46 110 174 302), lower := (rows 275 35 84 200 144 32 64 128 256), losses := [] }

theorem u4704 : Upper (D 1) (R 1) [274,33,80,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4704
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4705 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 100 200 18 188 220 156 412), lower := (rows 275 35 100 200 18 32 64 128 256), losses := [] }

theorem u4705 : Upper (D 1) (R 1) [274,33,96,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4705
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4706 : PairBound 9 := { available := 154, camps := [], pairs := [], upper := (rows 275 35 100 200 20 186 218 154 410), lower := (rows 275 35 100 200 20 32 64 128 256), losses := [] }

theorem u4706 : Upper (D 1) (R 1) [274,33,96,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4706
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4707 : PairBound 9 := { available := 150, camps := [], pairs := [], upper := (rows 275 35 100 200 24 182 214 150 406), lower := (rows 275 35 100 200 24 32 64 128 256), losses := [] }

theorem u4707 : Upper (D 1) (R 1) [274,33,96,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4707
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4708 : Route 9 := (fun mask => (mask,id))

def c4708 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4708 : Upper (D 1) (R 1) [274,33,96,192,128] 13 := by
  apply FastRouting.sound _ _ [274,33,96,192,128] 13 (by decide) (choices 1) [2,4,8,16] r4708 c4708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1372
  · exact u1373
  · exact u1374
  · exact u1375

def b4709 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 13 74 48 240 208 208 464), lower := (rows 275 38 13 74 48 32 64 128 256), losses := [] }

theorem u4709 : Upper (D 1) (R 1) [274,36,9,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4709
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4710 : PairBound 9 := { available := 176, camps := [], pairs := [(1,6)], upper := (rows 275 38 13 74 80 176 240 176 432), lower := (rows 275 38 13 74 80 32 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 49 0 145 273), good := (rows 435 38 431 10 432 32 0 128 256) }] }

theorem u4710 : Upper (D 1) (R 1) [274,36,9,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4710
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4711 : Route 9 := (fun mask => (mask,id))

def c4711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4711 : Upper (D 1) (R 1) [274,36,9,66,128] 13 := by
  apply FastRouting.sound _ _ [274,36,9,66,128] 13 (by decide) (choices 1) [16,64,128] r4711 c4711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1376
  · exact u1377
  · exact u1378

def b4712 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 13 200 18 240 240 240 496), lower := (rows 275 38 13 200 18 32 64 128 256), losses := [] }

theorem u4712 : Upper (D 1) (R 1) [274,36,9,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4712
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4713 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 13 200 48 242 210 210 466), lower := (rows 275 38 13 200 48 32 64 128 256), losses := [] }

theorem u4713 : Upper (D 1) (R 1) [274,36,9,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4713
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4714 : PairBound 9 := { available := 178, camps := [], pairs := [(1,6)], upper := (rows 275 38 13 200 80 178 242 178 434), lower := (rows 275 38 13 200 80 32 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 33 0 129 257), good := (rows 435 38 431 136 16 32 0 128 256) }] }

theorem u4714 : Upper (D 1) (R 1) [274,36,9,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4714
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4715 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 69 56 18 232 200 200 456), lower := (rows 275 38 69 56 18 32 64 128 256), losses := [] }

theorem u4715 : Upper (D 1) (R 1) [274,36,65,48,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4715
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4716 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 275 38 69 56 24 226 194 194 450), lower := (rows 275 38 69 56 24 32 64 128 256), losses := [] }

theorem u4716 : Upper (D 1) (R 1) [274,36,65,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4716
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4717 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 69 56 80 170 202 138 394), lower := (rows 275 38 69 56 80 32 64 128 256), losses := [] }

theorem u4717 : Upper (D 1) (R 1) [274,36,65,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4717
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4718 : Route 9 := (fun mask => (mask,id))

def c4718 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4718 : Upper (D 1) (R 1) [274,36,65,48,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,48,128] 13 (by decide) (choices 1) [2,8,64,128] r4718 c4718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1379
  · exact u1380
  · exact u1381
  · exact u1382

def b4719 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 69 88 18 168 232 168 424), lower := (rows 275 38 69 88 18 32 64 128 256), losses := [] }

theorem u4719 : Upper (D 1) (R 1) [274,36,65,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4719
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4720 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 275 38 69 88 24 162 226 162 418), lower := (rows 275 38 69 88 24 32 64 128 256), losses := [] }

theorem u4720 : Upper (D 1) (R 1) [274,36,65,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4720
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4721 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 69 88 48 170 202 138 394), lower := (rows 275 38 69 88 48 32 64 128 256), losses := [] }

theorem u4721 : Upper (D 1) (R 1) [274,36,65,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4721
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4722 : Route 9 := (fun mask => (mask,id))

def c4722 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4722 : Upper (D 1) (R 1) [274,36,65,80,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,80,128] 13 (by decide) (choices 1) [2,8,128] r4722 c4722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1383
  · exact u1384
  · exact u1385

def b4723 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 69 104 18 184 216 152 408), lower := (rows 275 38 69 104 18 32 64 128 256), losses := [] }

theorem u4723 : Upper (D 1) (R 1) [274,36,65,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4723
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4724 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 275 38 69 104 24 178 210 146 402), lower := (rows 275 38 69 104 24 32 64 128 256), losses := [] }

theorem u4724 : Upper (D 1) (R 1) [274,36,65,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4724
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4725 : Route 9 := (fun mask => (mask,id))

def c4725 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4725 : Upper (D 1) (R 1) [274,36,65,96,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,96,128] 13 (by decide) (choices 1) [2,8,16,128] r4725 c4725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1386
  · exact u1387
  · exact u1388
  · exact u1389

def b4726 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 275 38 69 138 24 240 240 240 496), lower := (rows 275 38 69 138 24 32 64 128 256), losses := [] }

theorem u4726 : Upper (D 1) (R 1) [274,36,65,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4726
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4727 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 69 138 48 248 216 216 472), lower := (rows 275 38 69 138 48 32 64 128 256), losses := [] }

theorem u4727 : Upper (D 1) (R 1) [274,36,65,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4727
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4728 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 69 138 80 184 248 184 440), lower := (rows 275 38 69 138 80 32 64 128 256), losses := [] }

theorem u4728 : Upper (D 1) (R 1) [274,36,65,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4728
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4729 : Route 9 := (fun mask => (mask,id))

def c4729 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4729 : Upper (D 1) (R 1) [274,36,65,130,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,130,128] 13 (by decide) (choices 1) [8,16,64] r4729 c4729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1390
  · exact u1391
  · exact u1392

def b4730 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 69 152 18 232 232 232 488), lower := (rows 275 38 69 152 18 32 64 128 256), losses := [] }

theorem u4730 : Upper (D 1) (R 1) [274,36,65,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4730
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4731 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 275 38 69 152 24 226 226 226 482), lower := (rows 275 38 69 152 24 32 64 128 256), losses := [] }

theorem u4731 : Upper (D 1) (R 1) [274,36,65,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4731
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4732 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 69 152 48 234 202 202 458), lower := (rows 275 38 69 152 48 32 64 128 256), losses := [] }

theorem u4732 : Upper (D 1) (R 1) [274,36,65,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4732
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4733 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 69 152 80 170 234 170 426), lower := (rows 275 38 69 152 80 32 64 128 256), losses := [] }

theorem u4733 : Upper (D 1) (R 1) [274,36,65,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4733
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4734 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 275 38 69 152 144 106 106 234 362), lower := (rows 275 38 69 152 144 32 64 128 256), losses := [] }

theorem u4734 : Upper (D 1) (R 1) [274,36,65,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4734
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4735 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 69 168 18 248 216 216 472), lower := (rows 275 38 69 168 18 32 64 128 256), losses := [] }

theorem u4735 : Upper (D 1) (R 1) [274,36,65,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4735
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4736 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 275 38 69 168 24 242 210 210 466), lower := (rows 275 38 69 168 24 32 64 128 256), losses := [] }

theorem u4736 : Upper (D 1) (R 1) [274,36,65,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4736
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4737 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 38 69 168 80 186 218 154 410), lower := (rows 275 38 69 168 80 32 64 128 256), losses := [] }

theorem u4737 : Upper (D 1) (R 1) [274,36,65,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4737
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4738 : Route 9 := (fun mask => (mask,id))

def c4738 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4738 : Upper (D 1) (R 1) [274,36,65,160,128] 13 := by
  apply FastRouting.sound _ _ [274,36,65,160,128] 13 (by decide) (choices 1) [2,8,16,64] r4738 c4738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1393
  · exact u1394
  · exact u1395
  · exact u1396

def b4739 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 69 200 18 184 248 184 440), lower := (rows 275 38 69 200 18 32 64 128 256), losses := [] }

theorem u4739 : Upper (D 1) (R 1) [274,36,65,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4739
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u4739
end Delivery.IrregularNine14.P01
