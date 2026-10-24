import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0024
import IrregularNine14P01C0025

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4920 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 277 26 100 138 144 99 99 227 355), lower := (rows 277 26 100 138 144 32 64 128 256), losses := [] }

theorem u4920 : Upper (D 1) (R 1) [276,24,96,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4920
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4921 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 26 100 168 17 226 194 194 450), lower := (rows 277 26 100 168 17 32 64 128 256), losses := [] }

theorem u4921 : Upper (D 1) (R 1) [276,24,96,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4921
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4922 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 277 26 100 168 18 227 195 195 451), lower := (rows 277 26 100 168 18 32 64 128 256), losses := [] }

theorem u4922 : Upper (D 1) (R 1) [276,24,96,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4922
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4923 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 26 100 168 80 163 195 131 387), lower := (rows 277 26 100 168 80 32 64 128 256), losses := [] }

theorem u4923 : Upper (D 1) (R 1) [276,24,96,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4923
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4924 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 277 26 100 168 144 99 67 195 323), lower := (rows 277 26 100 168 144 32 64 128 256), losses := [] }

theorem u4924 : Upper (D 1) (R 1) [276,24,96,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4924
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4925 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 35 14 200 18 240 240 240 496), lower := (rows 277 35 14 200 18 32 64 128 256), losses := [] }

theorem u4925 : Upper (D 1) (R 1) [276,33,10,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4925
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4926 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c4926 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4926 : Upper (D 1) (R 1) [276,33,10,192,32] 13 := by
  apply FastRouting.sound _ _ [276,33,10,192,32] 13 (by decide) (choices 1) [2,16,64] r4926 c4926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1486
  · exact u1487
  · exact u1488

def b4927 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 14 200 80 178 242 178 434), lower := (rows 277 35 14 200 80 32 64 128 256), losses := [] }

theorem u4927 : Upper (D 1) (R 1) [276,33,10,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4927
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4928 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 277 35 70 56 18 232 200 200 456), lower := (rows 277 35 70 56 18 32 64 128 256), losses := [] }

theorem u4928 : Upper (D 1) (R 1) [276,33,66,48,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4928
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4929 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 35 70 56 24 226 194 194 450), lower := (rows 277 35 70 56 24 32 64 128 256), losses := [] }

theorem u4929 : Upper (D 1) (R 1) [276,33,66,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4929
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4930 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 70 56 80 170 202 138 394), lower := (rows 277 35 70 56 80 32 64 128 256), losses := [] }

theorem u4930 : Upper (D 1) (R 1) [276,33,66,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4930
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4931 : Route 9 := (fun mask => (mask,id))

def c4931 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4931 : Upper (D 1) (R 1) [276,33,66,48,128] 13 := by
  apply FastRouting.sound _ _ [276,33,66,48,128] 13 (by decide) (choices 1) [2,8,64,128] r4931 c4931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1489
  · exact u1490
  · exact u1491
  · exact u1492

def b4932 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 277 35 70 88 18 168 232 168 424), lower := (rows 277 35 70 88 18 32 64 128 256), losses := [] }

theorem u4932 : Upper (D 1) (R 1) [276,33,66,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4932
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4933 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 277 35 70 88 24 162 226 162 418), lower := (rows 277 35 70 88 24 32 64 128 256), losses := [] }

theorem u4933 : Upper (D 1) (R 1) [276,33,66,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4933
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4934 : PairBound 9 := { available := 138, camps := [], pairs := [(3,1)], upper := (rows 277 35 70 88 48 170 202 138 394), lower := (rows 277 35 70 88 48 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 50 32 64 128 256), good := (rows 285 49 92 88 48 48 64 128 256) }] }

theorem u4934 : Upper (D 1) (R 1) [276,33,66,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4934
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4935 : Route 9 := (fun mask => (mask,id))

def c4935 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4935 : Upper (D 1) (R 1) [276,33,66,80,128] 13 := by
  apply FastRouting.sound _ _ [276,33,66,80,128] 13 (by decide) (choices 1) [2,8,128] r4935 c4935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1493
  · exact u1494
  · exact u1495

def b4936 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 35 70 104 18 184 216 152 408), lower := (rows 277 35 70 104 18 32 64 128 256), losses := [] }

theorem u4936 : Upper (D 1) (R 1) [276,33,66,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4936
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4937 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 35 70 104 24 178 210 146 402), lower := (rows 277 35 70 104 24 32 64 128 256), losses := [] }

theorem u4937 : Upper (D 1) (R 1) [276,33,66,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4937
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4938 : Route 9 := (fun mask => (mask,id))

def c4938 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4938 : Upper (D 1) (R 1) [276,33,66,96,128] 13 := by
  apply FastRouting.sound _ _ [276,33,66,96,128] 13 (by decide) (choices 1) [2,8,16,128] r4938 c4938
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1496
  · exact u1497
  · exact u1498
  · exact u1499

def b4939 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 277 35 70 138 24 240 240 240 496), lower := (rows 277 35 70 138 24 32 64 128 256), losses := [] }

theorem u4939 : Upper (D 1) (R 1) [276,33,66,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4939
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4940 : Route 9 := (fun mask => (mask,id))

def c4940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u4940 : Upper (D 1) (R 1) [276,33,66,130,32] 13 := by
  apply FastRouting.sound _ _ [276,33,66,130,32] 13 (by decide) (choices 1) [8,16,64,128] r4940 c4940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1500
  · exact u1501
  · exact u1502
  · exact u1503

def b4941 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 70 138 80 184 248 184 440), lower := (rows 277 35 70 138 80 32 64 128 256), losses := [] }

theorem u4941 : Upper (D 1) (R 1) [276,33,66,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4941
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4942 : Route 9 := (fun mask => (mask,id))

def c4942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4942 : Upper (D 1) (R 1) [276,33,66,130,128] 13 := by
  apply FastRouting.sound _ _ [276,33,66,130,128] 13 (by decide) (choices 1) [8,16,64] r4942 c4942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1504
  · exact u1505
  · exact u1506

def b4943 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 35 70 152 18 232 232 232 488), lower := (rows 277 35 70 152 18 32 64 128 256), losses := [] }

theorem u4943 : Upper (D 1) (R 1) [276,33,66,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4943
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4944 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 277 35 70 152 24 226 226 226 482), lower := (rows 277 35 70 152 24 32 64 128 256), losses := [] }

theorem u4944 : Upper (D 1) (R 1) [276,33,66,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4944
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4945 : Route 9 := (fun mask => (mask,id))

def c4945 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4945 : Upper (D 1) (R 1) [276,33,66,144,32] 13 := by
  apply FastRouting.sound _ _ [276,33,66,144,32] 13 (by decide) (choices 1) [2,8,64,128] r4945 c4945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1507
  · exact u1508
  · exact u1509
  · exact u1510

def b4946 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 70 152 80 170 234 170 426), lower := (rows 277 35 70 152 80 32 64 128 256), losses := [] }

theorem u4946 : Upper (D 1) (R 1) [276,33,66,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4946
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4947 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 277 35 70 152 144 106 106 234 362), lower := (rows 277 35 70 152 144 32 64 128 256), losses := [] }

theorem u4947 : Upper (D 1) (R 1) [276,33,66,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4947
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4948 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 35 70 168 18 248 216 216 472), lower := (rows 277 35 70 168 18 32 64 128 256), losses := [] }

theorem u4948 : Upper (D 1) (R 1) [276,33,66,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4948
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4949 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 277 35 70 168 24 242 210 210 466), lower := (rows 277 35 70 168 24 32 64 128 256), losses := [] }

theorem u4949 : Upper (D 1) (R 1) [276,33,66,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4949
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4950 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 70 168 80 186 218 154 410), lower := (rows 277 35 70 168 80 32 64 128 256), losses := [] }

theorem u4950 : Upper (D 1) (R 1) [276,33,66,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4950
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4951 : Route 9 := (fun mask => (mask,id))

def c4951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4951 : Upper (D 1) (R 1) [276,33,66,160,128] 13 := by
  apply FastRouting.sound _ _ [276,33,66,160,128] 13 (by decide) (choices 1) [2,8,16,64] r4951 c4951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1511
  · exact u1512
  · exact u1513
  · exact u1514

def b4952 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 35 70 200 18 184 248 184 440), lower := (rows 277 35 70 200 18 32 64 128 256), losses := [] }

theorem u4952 : Upper (D 1) (R 1) [276,33,66,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4952
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4953 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 277 35 70 200 24 178 242 178 434), lower := (rows 277 35 70 200 24 32 64 128 256), losses := [] }

theorem u4953 : Upper (D 1) (R 1) [276,33,66,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4953
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4954 : Route 9 := (fun mask => (mask,id))

def c4954 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4954 : Upper (D 1) (R 1) [276,33,66,192,32] 13 := by
  apply FastRouting.sound _ _ [276,33,66,192,32] 13 (by decide) (choices 1) [2,8,16,128] r4954 c4954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1515
  · exact u1516
  · exact u1517
  · exact u1518

def r4955 : Route 9 := (fun mask => (mask,id))

def c4955 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4955 : Upper (D 1) (R 1) [276,33,66,192,128] 13 := by
  apply FastRouting.sound _ _ [276,33,66,192,128] 13 (by decide) (choices 1) [2,8,16] r4955 c4955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1519
  · exact u1520
  · exact u1521

def r4956 : Route 9 := (fun mask => (mask,id))

def c4956 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4956 : Upper (D 1) (R 1) [276,33,72,130,2] 13 := by
  apply FastRouting.sound _ _ [276,33,72,130,2] 13 (by decide) (choices 1) [16,64,128] r4956 c4956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1522
  · exact u1523
  · exact u1524

def r4957 : Route 9 := (fun mask => (mask,id))

def c4957 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4957 : Upper (D 1) (R 1) [276,33,72,130,32] 13 := by
  apply FastRouting.sound _ _ [276,33,72,130,32] 13 (by decide) (choices 1) [2,16,64,128] r4957 c4957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1525
  · exact u1526
  · exact u1527
  · exact u1528

def b4958 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 76 138 80 178 242 178 434), lower := (rows 277 35 76 138 80 32 64 128 256), losses := [] }

theorem u4958 : Upper (D 1) (R 1) [276,33,72,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4958
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4959 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 277 35 76 138 144 114 114 242 370), lower := (rows 277 35 76 138 144 32 64 128 256), losses := [] }

theorem u4959 : Upper (D 1) (R 1) [276,33,72,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4959
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4960 : Route 9 := (fun mask => (mask,id))

def c4960 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4960 : Upper (D 1) (R 1) [276,33,72,160,2] 13 := by
  apply FastRouting.sound _ _ [276,33,72,160,2] 13 (by decide) (choices 1) [2,16,64,128] r4960 c4960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1529
  · exact u1530
  · exact u1531
  · exact u1532

def b4961 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 76 168 80 178 210 146 402), lower := (rows 277 35 76 168 80 32 64 128 256), losses := [] }

theorem u4961 : Upper (D 1) (R 1) [276,33,72,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4961
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4962 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 277 35 76 168 144 114 82 210 338), lower := (rows 277 35 76 168 144 32 64 128 256), losses := [] }

theorem u4962 : Upper (D 1) (R 1) [276,33,72,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4962
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4963 : PairBound 9 := { available := 202, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 277 35 196 56 18 234 202 202 458), lower := (rows 277 35 196 56 18 32 64 128 256), losses := [] }

theorem u4963 : Upper (D 1) (R 1) [276,33,192,48,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4963
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4964 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 35 196 56 24 226 194 194 450), lower := (rows 277 35 196 56 24 32 64 128 256), losses := [] }

theorem u4964 : Upper (D 1) (R 1) [276,33,192,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4964
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4965 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 35 196 56 80 170 202 138 394), lower := (rows 277 35 196 56 80 32 64 128 256), losses := [] }

theorem u4965 : Upper (D 1) (R 1) [276,33,192,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4965
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4966 : Route 9 := (fun mask => (mask,id))

def c4966 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4966 : Upper (D 1) (R 1) [276,33,192,66,2] 13 := by
  apply FastRouting.sound _ _ [276,33,192,66,2] 13 (by decide) (choices 1) [8,16,128] r4966 c4966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1533
  · exact u1534
  · exact u1535

def b4967 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 277 35 196 74 24 178 242 178 434), lower := (rows 277 35 196 74 24 32 64 128 256), losses := [] }

theorem u4967 : Upper (D 1) (R 1) [276,33,192,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4967
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4968 : Route 9 := (fun mask => (mask,id))

def c4968 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4968 : Upper (D 1) (R 1) [276,33,192,66,32] 13 := by
  apply FastRouting.sound _ _ [276,33,192,66,32] 13 (by decide) (choices 1) [2,8,16,128] r4968 c4968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1536
  · exact u1537
  · exact u1538
  · exact u1539

def b4969 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 277 35 196 74 144 58 122 186 314), lower := (rows 277 35 196 74 144 32 64 128 256), losses := [] }

theorem u4969 : Upper (D 1) (R 1) [276,33,192,66,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4969
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4970 : Route 9 := (fun mask => (mask,id))

def c4970 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4970 : Upper (D 1) (R 1) [276,33,192,80,2] 13 := by
  apply FastRouting.sound _ _ [276,33,192,80,2] 13 (by decide) (choices 1) [2,8,128] r4970 c4970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1540
  · exact u1541
  · exact u1542

def b4971 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 277 35 196 88 24 162 226 162 418), lower := (rows 277 35 196 88 24 32 64 128 256), losses := [] }

theorem u4971 : Upper (D 1) (R 1) [276,33,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4971
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4972 : Route 9 := (fun mask => (mask,id))

def c4972 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4972 : Upper (D 1) (R 1) [276,33,192,80,32] 13 := by
  apply FastRouting.sound _ _ [276,33,192,80,32] 13 (by decide) (choices 1) [2,8,128] r4972 c4972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1543
  · exact u1544
  · exact u1545

def b4973 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 277 35 196 88 144 42 106 170 298), lower := (rows 277 35 196 88 144 32 64 128 256), losses := [] }

theorem u4973 : Upper (D 1) (R 1) [276,33,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4973
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4974 : Route 9 := (fun mask => (mask,id))

def c4974 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4974 : Upper (D 1) (R 1) [276,33,192,96,2] 13 := by
  apply FastRouting.sound _ _ [276,33,192,96,2] 13 (by decide) (choices 1) [2,8,16,128] r4974 c4974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1546
  · exact u1547
  · exact u1548
  · exact u1549

def b4975 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 35 196 104 24 178 210 146 402), lower := (rows 277 35 196 104 24 32 64 128 256), losses := [] }

theorem u4975 : Upper (D 1) (R 1) [276,33,192,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4975
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4976 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 277 35 196 104 144 58 90 154 282), lower := (rows 277 35 196 104 144 32 64 128 256), losses := [] }

theorem u4976 : Upper (D 1) (R 1) [276,33,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4976
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4977 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 42 7 200 18 240 240 240 496), lower := (rows 277 42 7 200 18 32 64 128 256), losses := [] }

theorem u4977 : Upper (D 1) (R 1) [276,40,3,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4977
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4978 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c4978 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4978 : Upper (D 1) (R 1) [276,40,3,192,32] 13 := by
  apply FastRouting.sound _ _ [276,40,3,192,32] 13 (by decide) (choices 1) [2,16,64] r4978 c4978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1550
  · exact u1551
  · exact u1552

def r4979 : Route 9 := (fun mask => (mask,id))

def c4979 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4979 : Upper (D 1) (R 1) [276,40,3,192,64] 13 := by
  apply FastRouting.sound _ _ [276,40,3,192,64] 13 (by decide) (choices 1) [2,16,128] r4979 c4979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1553
  · exact u1554
  · exact u1555

#print axioms u4979
end Delivery.IrregularNine14.P01
