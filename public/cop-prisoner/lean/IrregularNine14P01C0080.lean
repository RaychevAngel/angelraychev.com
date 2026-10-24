import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0023
import IrregularNine14P01C0024

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4800 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 275 98 28 168 17 230 198 198 454), lower := (rows 275 98 28 168 17 32 64 128 256), losses := [] }

theorem u4800 : Upper (D 1) (R 1) [274,96,24,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4800
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4801 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 28 168 18 229 197 197 453), lower := (rows 275 98 28 168 18 32 64 128 256), losses := [] }

theorem u4801 : Upper (D 1) (R 1) [274,96,24,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4801
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4802 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 275 98 28 168 20 227 195 195 451), lower := (rows 275 98 28 168 20 32 64 128 256), losses := [] }

theorem u4802 : Upper (D 1) (R 1) [274,96,24,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4802
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4803 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 28 168 80 167 199 135 391), lower := (rows 275 98 28 168 80 32 64 128 256), losses := [] }

theorem u4803 : Upper (D 1) (R 1) [274,96,24,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4803
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4804 : PairBound 9 := { available := 71, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 28 168 144 103 71 199 327), lower := (rows 275 98 28 168 144 32 64 128 256), losses := [] }

theorem u4804 : Upper (D 1) (R 1) [274,96,24,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4804
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4805 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 37 76 18 184 216 152 408), lower := (rows 275 98 37 76 18 32 64 128 256), losses := [] }

theorem u4805 : Upper (D 1) (R 1) [274,96,33,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4805
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4806 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 275 98 37 76 24 178 210 146 402), lower := (rows 275 98 37 76 24 32 64 128 256), losses := [] }

theorem u4806 : Upper (D 1) (R 1) [274,96,33,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4806
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4807 : Route 9 := (fun mask => (mask,id))

def c4807 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4807 : Upper (D 1) (R 1) [274,96,33,68,128] 13 := by
  apply FastRouting.sound _ _ [274,96,33,68,128] 13 (by decide) (choices 1) [2,8,16,128] r4807 c4807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1413
  · exact u1414
  · exact u1415
  · exact u1416

def b4808 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 37 88 18 172 204 140 396), lower := (rows 275 98 37 88 18 32 64 128 256), losses := [] }

theorem u4808 : Upper (D 1) (R 1) [274,96,33,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4808
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4809 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 275 98 37 88 20 170 202 138 394), lower := (rows 275 98 37 88 20 32 64 128 256), losses := [] }

theorem u4809 : Upper (D 1) (R 1) [274,96,33,80,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4809
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4810 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 275 98 37 88 24 166 198 134 390), lower := (rows 275 98 37 88 24 32 64 128 256), losses := [] }

theorem u4810 : Upper (D 1) (R 1) [274,96,33,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4810
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4811 : Route 9 := (fun mask => (mask,id))

def c4811 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4811 : Upper (D 1) (R 1) [274,96,33,80,128] 13 := by
  apply FastRouting.sound _ _ [274,96,33,80,128] 13 (by decide) (choices 1) [2,4,8,128] r4811 c4811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1417
  · exact u1418
  · exact u1419
  · exact u1420

def b4812 : PairBound 9 := { available := 216, camps := [], pairs := [], upper := (rows 275 98 37 138 20 248 216 216 472), lower := (rows 275 98 37 138 20 32 64 128 256), losses := [] }

theorem u4812 : Upper (D 1) (R 1) [274,96,33,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4812
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4813 : PairBound 9 := { available := 212, camps := [], pairs := [], upper := (rows 275 98 37 138 24 244 212 212 468), lower := (rows 275 98 37 138 24 32 64 128 256), losses := [] }

theorem u4813 : Upper (D 1) (R 1) [274,96,33,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4813
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4814 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 37 138 80 188 220 156 412), lower := (rows 275 98 37 138 80 32 64 128 256), losses := [] }

theorem u4814 : Upper (D 1) (R 1) [274,96,33,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4814
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4815 : Route 9 := (fun mask => (mask,id))

def c4815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4815 : Upper (D 1) (R 1) [274,96,33,130,128] 13 := by
  apply FastRouting.sound _ _ [274,96,33,130,128] 13 (by decide) (choices 1) [4,8,16,64] r4815 c4815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1421
  · exact u1422
  · exact u1423
  · exact u1424

def b4816 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 37 140 18 248 216 216 472), lower := (rows 275 98 37 140 18 32 64 128 256), losses := [] }

theorem u4816 : Upper (D 1) (R 1) [274,96,33,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4816
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4817 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 275 98 37 140 24 242 210 210 466), lower := (rows 275 98 37 140 24 32 64 128 256), losses := [] }

theorem u4817 : Upper (D 1) (R 1) [274,96,33,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4817
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4818 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 37 140 80 186 218 154 410), lower := (rows 275 98 37 140 80 32 64 128 256), losses := [] }

theorem u4818 : Upper (D 1) (R 1) [274,96,33,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4818
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4819 : Route 9 := (fun mask => (mask,id))

def c4819 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4819 : Upper (D 1) (R 1) [274,96,33,132,128] 13 := by
  apply FastRouting.sound _ _ [274,96,33,132,128] 13 (by decide) (choices 1) [2,8,16,64] r4819 c4819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1425
  · exact u1426
  · exact u1427
  · exact u1428

def b4820 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 37 152 18 236 204 204 460), lower := (rows 275 98 37 152 18 32 64 128 256), losses := [] }

theorem u4820 : Upper (D 1) (R 1) [274,96,33,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4820
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4821 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 275 98 37 152 20 234 202 202 458), lower := (rows 275 98 37 152 20 32 64 128 256), losses := [] }

theorem u4821 : Upper (D 1) (R 1) [274,96,33,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4821
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4822 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 275 98 37 152 24 230 198 198 454), lower := (rows 275 98 37 152 24 32 64 128 256), losses := [] }

theorem u4822 : Upper (D 1) (R 1) [274,96,33,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4822
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4823 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 37 152 80 174 206 142 398), lower := (rows 275 98 37 152 80 32 64 128 256), losses := [] }

theorem u4823 : Upper (D 1) (R 1) [274,96,33,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4823
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4824 : PairBound 9 := { available := 78, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 275 98 37 152 144 110 78 206 334), lower := (rows 275 98 37 152 144 32 64 128 256), losses := [] }

theorem u4824 : Upper (D 1) (R 1) [274,96,33,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4824
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4825 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 37 200 18 188 220 156 412), lower := (rows 275 98 37 200 18 32 64 128 256), losses := [] }

theorem u4825 : Upper (D 1) (R 1) [274,96,33,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4825
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4826 : PairBound 9 := { available := 154, camps := [], pairs := [], upper := (rows 275 98 37 200 20 186 218 154 410), lower := (rows 275 98 37 200 20 32 64 128 256), losses := [] }

theorem u4826 : Upper (D 1) (R 1) [274,96,33,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4826
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4827 : PairBound 9 := { available := 150, camps := [], pairs := [], upper := (rows 275 98 37 200 24 182 214 150 406), lower := (rows 275 98 37 200 24 32 64 128 256), losses := [] }

theorem u4827 : Upper (D 1) (R 1) [274,96,33,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4827
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4828 : Route 9 := (fun mask => (mask,id))

def c4828 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4828 : Upper (D 1) (R 1) [274,96,33,192,128] 13 := by
  apply FastRouting.sound _ _ [274,96,33,192,128] 13 (by decide) (choices 1) [2,4,8,16] r4828 c4828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1429
  · exact u1430
  · exact u1431
  · exact u1432

def b4829 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 275 98 44 88 17 166 198 134 390), lower := (rows 275 98 44 88 17 32 64 128 256), losses := [] }

theorem u4829 : Upper (D 1) (R 1) [274,96,40,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4829
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4830 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 44 88 18 165 197 133 389), lower := (rows 275 98 44 88 18 32 64 128 256), losses := [] }

theorem u4830 : Upper (D 1) (R 1) [274,96,40,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4830
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4831 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 275 98 44 88 20 163 195 131 387), lower := (rows 275 98 44 88 20 32 64 128 256), losses := [] }

theorem u4831 : Upper (D 1) (R 1) [274,96,40,80,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4831
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4832 : Route 9 := (fun mask => (mask,id))

def c4832 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4832 : Upper (D 1) (R 1) [274,96,40,80,128] 13 := by
  apply FastRouting.sound _ _ [274,96,40,80,128] 13 (by decide) (choices 1) [1,2,4,128] r4832 c4832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1433
  · exact u1434
  · exact u1435
  · exact u1436

def b4833 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 44 137 18 244 212 212 468), lower := (rows 275 98 44 137 18 32 64 128 256), losses := [] }

theorem u4833 : Upper (D 1) (R 1) [274,96,40,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4833
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4834 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 275 98 44 137 20 242 210 210 466), lower := (rows 275 98 44 137 20 32 64 128 256), losses := [] }

theorem u4834 : Upper (D 1) (R 1) [274,96,40,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4834
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4835 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 44 137 80 182 214 150 406), lower := (rows 275 98 44 137 80 32 64 128 256), losses := [] }

theorem u4835 : Upper (D 1) (R 1) [274,96,40,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4835
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4836 : Route 9 := (fun mask => (mask,id))

def c4836 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4836 : Upper (D 1) (R 1) [274,96,40,129,128] 13 := by
  apply FastRouting.sound _ _ [274,96,40,129,128] 13 (by decide) (choices 1) [2,4,16,64] r4836 c4836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1437
  · exact u1438
  · exact u1439
  · exact u1440

def b4837 : PairBound 9 := { available := 212, camps := [], pairs := [], upper := (rows 275 98 44 138 17 244 212 212 468), lower := (rows 275 98 44 138 17 32 64 128 256), losses := [] }

theorem u4837 : Upper (D 1) (R 1) [274,96,40,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4837
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4838 : PairBound 9 := { available := 209, camps := [], pairs := [], upper := (rows 275 98 44 138 20 241 209 209 465), lower := (rows 275 98 44 138 20 32 64 128 256), losses := [] }

theorem u4838 : Upper (D 1) (R 1) [274,96,40,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4838
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4839 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 44 138 80 181 213 149 405), lower := (rows 275 98 44 138 80 32 64 128 256), losses := [] }

theorem u4839 : Upper (D 1) (R 1) [274,96,40,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4839
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4840 : Route 9 := (fun mask => (mask,id))

def c4840 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4840 : Upper (D 1) (R 1) [274,96,40,130,128] 13 := by
  apply FastRouting.sound _ _ [274,96,40,130,128] 13 (by decide) (choices 1) [1,4,16,64] r4840 c4840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1441
  · exact u1442
  · exact u1443
  · exact u1444

def b4841 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 275 98 44 152 17 230 198 198 454), lower := (rows 275 98 44 152 17 32 64 128 256), losses := [] }

theorem u4841 : Upper (D 1) (R 1) [274,96,40,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4841
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4842 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 44 152 18 229 197 197 453), lower := (rows 275 98 44 152 18 32 64 128 256), losses := [] }

theorem u4842 : Upper (D 1) (R 1) [274,96,40,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4842
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4843 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 275 98 44 152 20 227 195 195 451), lower := (rows 275 98 44 152 20 32 64 128 256), losses := [] }

theorem u4843 : Upper (D 1) (R 1) [274,96,40,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4843
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4844 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 44 152 80 167 199 135 391), lower := (rows 275 98 44 152 80 32 64 128 256), losses := [] }

theorem u4844 : Upper (D 1) (R 1) [274,96,40,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4844
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4845 : PairBound 9 := { available := 71, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 275 98 44 152 144 103 71 199 327), lower := (rows 275 98 44 152 144 32 64 128 256), losses := [] }

theorem u4845 : Upper (D 1) (R 1) [274,96,40,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4845
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4846 : PairBound 9 := { available := 150, camps := [], pairs := [], upper := (rows 275 98 44 200 17 182 214 150 406), lower := (rows 275 98 44 200 17 32 64 128 256), losses := [] }

theorem u4846 : Upper (D 1) (R 1) [274,96,40,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4846
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4847 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 44 200 18 181 213 149 405), lower := (rows 275 98 44 200 18 32 64 128 256), losses := [] }

theorem u4847 : Upper (D 1) (R 1) [274,96,40,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4847
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4848 : PairBound 9 := { available := 147, camps := [], pairs := [], upper := (rows 275 98 44 200 20 179 211 147 403), lower := (rows 275 98 44 200 20 32 64 128 256), losses := [] }

theorem u4848 : Upper (D 1) (R 1) [274,96,40,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4848
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4849 : Route 9 := (fun mask => (mask,id))

def c4849 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4849 : Upper (D 1) (R 1) [274,96,40,192,128] 13 := by
  apply FastRouting.sound _ _ [274,96,40,192,128] 13 (by decide) (choices 1) [1,2,4,16] r4849 c4849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1445
  · exact u1446
  · exact u1447
  · exact u1448

def b4850 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 52 137 18 236 204 204 460), lower := (rows 275 98 52 137 18 32 64 128 256), losses := [] }

theorem u4850 : Upper (D 1) (R 1) [274,96,48,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4850
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4851 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 275 98 52 137 20 234 202 202 458), lower := (rows 275 98 52 137 20 32 64 128 256), losses := [] }

theorem u4851 : Upper (D 1) (R 1) [274,96,48,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4851
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4852 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 275 98 52 137 24 230 198 198 454), lower := (rows 275 98 52 137 24 32 64 128 256), losses := [] }

theorem u4852 : Upper (D 1) (R 1) [274,96,48,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4852
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4853 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 52 137 80 174 206 142 398), lower := (rows 275 98 52 137 80 32 64 128 256), losses := [] }

theorem u4853 : Upper (D 1) (R 1) [274,96,48,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4853
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4854 : Route 9 := (fun mask => (mask,id))

def c4854 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4854 : Upper (D 1) (R 1) [274,96,48,129,128] 13 := by
  apply FastRouting.sound _ _ [274,96,48,129,128] 13 (by decide) (choices 1) [2,4,8,64] r4854 c4854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1449
  · exact u1450
  · exact u1451
  · exact u1452

def b4855 : PairBound 9 := { available := 204, camps := [], pairs := [], upper := (rows 275 98 52 138 17 236 204 204 460), lower := (rows 275 98 52 138 17 32 64 128 256), losses := [] }

theorem u4855 : Upper (D 1) (R 1) [274,96,48,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4855
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4856 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 275 98 52 138 20 233 201 201 457), lower := (rows 275 98 52 138 20 32 64 128 256), losses := [] }

theorem u4856 : Upper (D 1) (R 1) [274,96,48,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4856
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4857 : PairBound 9 := { available := 197, camps := [], pairs := [], upper := (rows 275 98 52 138 24 229 197 197 453), lower := (rows 275 98 52 138 24 32 64 128 256), losses := [] }

theorem u4857 : Upper (D 1) (R 1) [274,96,48,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4857
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4858 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 52 138 80 173 205 141 397), lower := (rows 275 98 52 138 80 32 64 128 256), losses := [] }

theorem u4858 : Upper (D 1) (R 1) [274,96,48,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4858
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4859 : Route 9 := (fun mask => (mask,id))

def c4859 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4859 : Upper (D 1) (R 1) [274,96,48,130,128] 13 := by
  apply FastRouting.sound _ _ [274,96,48,130,128] 13 (by decide) (choices 1) [1,4,8,64] r4859 c4859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1453
  · exact u1454
  · exact u1455
  · exact u1456

#print axioms u4859
end Delivery.IrregularNine14.P01
