import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0028
import IrregularNine14P00C0029
import IrregularNine14P00C0030

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2940 : Route 9 := (fun mask => (mask,id))

def c2940 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u2940 : Upper (D 0) (R 0) [112,20,40,129] 13 := by
  apply FastRouting.sound _ _ [112,20,40,129] 13 (by decide) (choices 1) [1,2,64,128,256] r2940 c2940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1683
  · exact u1684
  · exact u1685
  · exact u1686
  · exact u1687

def r2941 : Route 9 := (fun mask => (mask,id))

def c2941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u2941 : Upper (D 0) (R 0) [112,20,40,130] 13 := by
  apply FastRouting.sound _ _ [112,20,40,130] 13 (by decide) (choices 1) [1,64,128,256] r2941 c2941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1688
  · exact u1689
  · exact u1690
  · exact u1691

def r2942 : Route 9 := (fun mask => (mask,id))

def c2942 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | _ => 0)

theorem u2942 : Upper (D 0) (R 0) [112,20,40,192] 13 := by
  apply FastRouting.sound _ _ [112,20,40,192] 13 (by decide) (choices 1) [1,2,128,256] r2942 c2942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1692
  · exact u1693
  · exact u1694
  · exact u1695

def r2943 : Route 9 := (fun mask => (mask,id))

def c2943 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2943 : Upper (D 0) (R 0) [112,20,40,257] 13 := by
  apply FastRouting.sound _ _ [112,20,40,257] 13 (by decide) (choices 1) [1,2,64,128] r2943 c2943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1696
  · exact u1697
  · exact u1698
  · exact u1699

def r2944 : Route 9 := (fun mask => (mask,id))

def c2944 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2944 : Upper (D 0) (R 0) [112,20,40,258] 13 := by
  apply FastRouting.sound _ _ [112,20,40,258] 13 (by decide) (choices 1) [1,64,128] r2944 c2944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1700
  · exact u1701
  · exact u1702

def r2945 : Route 9 := (fun mask => (mask,id))

def c2945 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2945 : Upper (D 0) (R 0) [112,20,40,320] 13 := by
  apply FastRouting.sound _ _ [112,20,40,320] 13 (by decide) (choices 1) [1,2,128] r2945 c2945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1703
  · exact u1704
  · exact u1705

def r2946 : Route 9 := (fun mask => (mask,id))

def c2946 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2946 : Upper (D 0) (R 0) [112,20,40,384] 13 := by
  apply FastRouting.sound _ _ [112,20,40,384] 13 (by decide) (choices 1) [1,2,64,128] r2946 c2946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1706
  · exact u1707
  · exact u1708
  · exact u1709

def b2947 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 100 137 411 427 459 395 395), lower := (rows 113 22 100 137 16 32 64 128 256), losses := [] }

theorem u2947 : Upper (D 0) (R 0) [112,20,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2947
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2948 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 100 138 409 425 457 393 393), lower := (rows 113 22 100 138 16 32 64 128 256), losses := [] }

theorem u2948 : Upper (D 0) (R 0) [112,20,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2948
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2949 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 100 265 155 171 203 139 395), lower := (rows 113 22 100 265 16 32 64 128 256), losses := [] }

theorem u2949 : Upper (D 0) (R 0) [112,20,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2949
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2950 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 100 266 153 169 201 137 393), lower := (rows 113 22 100 266 16 32 64 128 256), losses := [] }

theorem u2950 : Upper (D 0) (R 0) [112,20,96,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2950
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2951 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 100 392 155 171 203 139 395), lower := (rows 113 22 100 392 16 32 64 128 256), losses := [] }

theorem u2951 : Upper (D 0) (R 0) [112,20,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2951
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2952 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 133 104 411 427 459 395 395), lower := (rows 113 22 133 104 16 32 64 128 256), losses := [] }

theorem u2952 : Upper (D 0) (R 0) [112,20,129,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2952
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2953 : PairBound 9 := { available := 362, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 133 137 378 362 362 490 362), lower := (rows 113 22 133 137 16 32 64 128 256), losses := [] }

theorem u2953 : Upper (D 0) (R 0) [112,20,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2953
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2954 : PairBound 9 := { available := 361, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 133 138 377 361 361 489 361), lower := (rows 113 22 133 138 16 32 64 128 256), losses := [] }

theorem u2954 : Upper (D 0) (R 0) [112,20,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2954
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2955 : Route 9 := (fun mask => (mask,id))

def c2955 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u2955 : Upper (D 0) (R 0) [112,20,129,160] 13 := by
  apply FastRouting.sound _ _ [112,20,129,160] 13 (by decide) (choices 1) [1,2,8,64,256] r2955 c2955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1710
  · exact u1711
  · exact u1712
  · exact u1713
  · exact u1714

def r2956 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2956 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u2956 : Upper (D 0) (R 0) [112,20,129,257] 13 := by
  apply FastRouting.sound _ _ [112,20,129,257] 13 (by decide) (choices 1) [2,8,32,128] r2956 c2956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1715
  · exact u1716
  · exact u1717
  · exact u1718

def r2957 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2957 : Upper (D 0) (R 0) [112,20,129,258] 13 := by
  apply FastRouting.sound _ _ [112,20,129,258] 13 (by decide) (choices 1) [1,8,32,128] r2957 c2957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1719
  · exact u1720
  · exact u1721
  · exact u1722

def r2958 : Route 9 := (fun mask => (mask,id))

def c2958 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2958 : Upper (D 0) (R 0) [112,20,129,288] 13 := by
  apply FastRouting.sound _ _ [112,20,129,288] 13 (by decide) (choices 1) [1,2,8,64,128] r2958 c2958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1723
  · exact u1724
  · exact u1725
  · exact u1726
  · exact u1727

def r2959 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2959 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2959 : Upper (D 0) (R 0) [112,20,129,384] 13 := by
  apply FastRouting.sound _ _ [112,20,129,384] 13 (by decide) (choices 1) [1,2,8,32] r2959 c2959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1728
  · exact u1729
  · exact u1730
  · exact u1731

def b2960 : PairBound 9 := { available := 361, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 134 137 377 361 361 489 361), lower := (rows 113 22 134 137 16 32 64 128 256), losses := [] }

theorem u2960 : Upper (D 0) (R 0) [112,20,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2960
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2961 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 134 168 345 361 329 457 329), lower := (rows 113 22 134 168 16 32 64 128 256), losses := [] }

theorem u2961 : Upper (D 0) (R 0) [112,20,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2961
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2962 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 134 265 249 233 233 233 489), lower := (rows 113 22 134 265 16 32 64 128 256), losses := [] }

theorem u2962 : Upper (D 0) (R 0) [112,20,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2962
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2963 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 134 296 217 233 201 201 457), lower := (rows 113 22 134 296 16 32 64 128 256), losses := [] }

theorem u2963 : Upper (D 0) (R 0) [112,20,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2963
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2964 : PairBound 9 := { available := 105, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 134 392 121 105 105 233 361), lower := (rows 113 22 134 392 16 32 64 128 256), losses := [] }

theorem u2964 : Upper (D 0) (R 0) [112,20,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2964
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2965 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 140 104 403 419 451 387 387), lower := (rows 113 22 140 104 16 32 64 128 256), losses := [] }

theorem u2965 : Upper (D 0) (R 0) [112,20,136,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2965
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2966 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 113 22 140 137 371 355 355 483 355), lower := (rows 113 22 140 137 16 32 64 128 256), losses := [] }

theorem u2966 : Upper (D 0) (R 0) [112,20,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2966
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2967 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 113 22 140 138 369 353 353 481 353), lower := (rows 113 22 140 138 16 32 64 128 256), losses := [] }

theorem u2967 : Upper (D 0) (R 0) [112,20,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2967
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2968 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 113 22 140 168 339 355 323 451 323), lower := (rows 113 22 140 168 16 32 64 128 256), losses := [] }

theorem u2968 : Upper (D 0) (R 0) [112,20,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2968
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2969 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2969 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2969 : Upper (D 0) (R 0) [112,20,136,257] 13 := by
  apply FastRouting.sound _ _ [112,20,136,257] 13 (by decide) (choices 1) [1,2,32,128] r2969 c2969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1732
  · exact u1733
  · exact u1734
  · exact u1735

def r2970 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2970 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2970 : Upper (D 0) (R 0) [112,20,136,258] 13 := by
  apply FastRouting.sound _ _ [112,20,136,258] 13 (by decide) (choices 1) [1,32,128] r2970 c2970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1736
  · exact u1737
  · exact u1738

def r2971 : Route 9 := (fun mask => (mask,id))

def c2971 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2971 : Upper (D 0) (R 0) [112,20,136,288] 13 := by
  apply FastRouting.sound _ _ [112,20,136,288] 13 (by decide) (choices 1) [1,2,64,128] r2971 c2971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1739
  · exact u1740
  · exact u1741
  · exact u1742

def b2972 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 113 22 140 392 115 99 99 227 355), lower := (rows 113 22 140 392 16 32 64 128 256), losses := [] }

theorem u2972 : Upper (D 0) (R 0) [112,20,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2972
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2973 : Route 9 := (fun mask => (mask,id))

def c2973 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u2973 : Upper (D 0) (R 0) [112,20,160,129] 13 := by
  apply FastRouting.sound _ _ [112,20,160,129] 13 (by decide) (choices 1) [1,2,8,64,256] r2973 c2973
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1743
  · exact u1744
  · exact u1745
  · exact u1746
  · exact u1747

def b2974 : PairBound 9 := { available := 329, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 164 138 345 361 329 457 329), lower := (rows 113 22 164 138 16 32 64 128 256), losses := [] }

theorem u2974 : Upper (D 0) (R 0) [112,20,160,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2974
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2975 : Route 9 := (fun mask => (mask,id))

def c2975 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2975 : Upper (D 0) (R 0) [112,20,160,192] 13 := by
  apply FastRouting.sound _ _ [112,20,160,192] 13 (by decide) (choices 1) [1,2,8,256] r2975 c2975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1748
  · exact u1749
  · exact u1750
  · exact u1751

def r2976 : Route 9 := (fun mask => (mask,id))

def c2976 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2976 : Upper (D 0) (R 0) [112,20,160,257] 13 := by
  apply FastRouting.sound _ _ [112,20,160,257] 13 (by decide) (choices 1) [1,2,8,64,128] r2976 c2976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1752
  · exact u1753
  · exact u1754
  · exact u1755
  · exact u1756

def r2977 : Route 9 := (fun mask => (mask,id))

def c2977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2977 : Upper (D 0) (R 0) [112,20,160,258] 13 := by
  apply FastRouting.sound _ _ [112,20,160,258] 13 (by decide) (choices 1) [1,8,64,128] r2977 c2977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1757
  · exact u1758
  · exact u1759
  · exact u1760

def r2978 : Route 9 := (fun mask => (mask,id))

def c2978 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2978 : Upper (D 0) (R 0) [112,20,160,320] 13 := by
  apply FastRouting.sound _ _ [112,20,160,320] 13 (by decide) (choices 1) [1,2,8,128] r2978 c2978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1761
  · exact u1762
  · exact u1763
  · exact u1764

def r2979 : Route 9 := (fun mask => (mask,id))

def c2979 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2979 : Upper (D 0) (R 0) [112,20,160,384] 13 := by
  apply FastRouting.sound _ _ [112,20,160,384] 13 (by decide) (choices 1) [1,2,8,64] r2979 c2979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1765
  · exact u1766
  · exact u1767
  · exact u1768

def b2980 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 261 104 155 171 203 139 395), lower := (rows 113 22 261 104 16 32 64 128 256), losses := [] }

theorem u2980 : Upper (D 0) (R 0) [112,20,257,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2980
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2981 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2981 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u2981 : Upper (D 0) (R 0) [112,20,257,129] 13 := by
  apply FastRouting.sound _ _ [112,20,257,129] 13 (by decide) (choices 1) [2,8,32,128] r2981 c2981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1769
  · exact u1770
  · exact u1771
  · exact u1772

def r2982 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2982 : Upper (D 0) (R 0) [112,20,257,130] 13 := by
  apply FastRouting.sound _ _ [112,20,257,130] 13 (by decide) (choices 1) [1,8,32,128] r2982 c2982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1773
  · exact u1774
  · exact u1775
  · exact u1776

def r2983 : Route 9 := (fun mask => (mask,id))

def c2983 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2983 : Upper (D 0) (R 0) [112,20,257,160] 13 := by
  apply FastRouting.sound _ _ [112,20,257,160] 13 (by decide) (choices 1) [1,2,8,64,128] r2983 c2983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1777
  · exact u1778
  · exact u1779
  · exact u1780
  · exact u1781

def b2984 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 136, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 262 137 249 233 233 233 489), lower := (rows 113 22 262 137 16 32 64 128 256), losses := [] }

theorem u2984 : Upper (D 0) (R 0) [112,20,258,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2984
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2985 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 136, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 262 168 217 233 201 201 457), lower := (rows 113 22 262 168 16 32 64 128 256), losses := [] }

theorem u2985 : Upper (D 0) (R 0) [112,20,258,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2985
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2986 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 268 104 147 163 195 131 387), lower := (rows 113 22 268 104 16 32 64 128 256), losses := [] }

theorem u2986 : Upper (D 0) (R 0) [112,20,264,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2986
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2987 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2987 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2987 : Upper (D 0) (R 0) [112,20,264,129] 13 := by
  apply FastRouting.sound _ _ [112,20,264,129] 13 (by decide) (choices 1) [1,2,32,128] r2987 c2987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1782
  · exact u1783
  · exact u1784
  · exact u1785

def r2988 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2988 : Upper (D 0) (R 0) [112,20,264,130] 13 := by
  apply FastRouting.sound _ _ [112,20,264,130] 13 (by decide) (choices 1) [1,32,128] r2988 c2988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1786
  · exact u1787
  · exact u1788

def r2989 : Route 9 := (fun mask => (mask,id))

def c2989 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2989 : Upper (D 0) (R 0) [112,20,264,160] 13 := by
  apply FastRouting.sound _ _ [112,20,264,160] 13 (by decide) (choices 1) [1,2,64,128] r2989 c2989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1789
  · exact u1790
  · exact u1791
  · exact u1792

def r2990 : Route 9 := (fun mask => (mask,id))

def c2990 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2990 : Upper (D 0) (R 0) [112,20,288,129] 13 := by
  apply FastRouting.sound _ _ [112,20,288,129] 13 (by decide) (choices 1) [1,2,8,64,128] r2990 c2990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1793
  · exact u1794
  · exact u1795
  · exact u1796
  · exact u1797

def r2991 : Route 9 := (fun mask => (mask,id))

def c2991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2991 : Upper (D 0) (R 0) [112,20,288,130] 13 := by
  apply FastRouting.sound _ _ [112,20,288,130] 13 (by decide) (choices 1) [1,8,64,128] r2991 c2991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1798
  · exact u1799
  · exact u1800
  · exact u1801

def r2992 : Route 9 := (fun mask => (mask,id))

def c2992 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2992 : Upper (D 0) (R 0) [112,20,288,192] 13 := by
  apply FastRouting.sound _ _ [112,20,288,192] 13 (by decide) (choices 1) [1,2,8,128] r2992 c2992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1802
  · exact u1803
  · exact u1804
  · exact u1805

def b2993 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 388 104 155 171 203 139 395), lower := (rows 113 22 388 104 16 32 64 128 256), losses := [] }

theorem u2993 : Upper (D 0) (R 0) [112,20,384,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2993
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2994 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2994 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2994 : Upper (D 0) (R 0) [112,20,384,129] 13 := by
  apply FastRouting.sound _ _ [112,20,384,129] 13 (by decide) (choices 1) [1,2,8,32] r2994 c2994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1806
  · exact u1807
  · exact u1808
  · exact u1809

def b2995 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 388 138 121 105 105 233 361), lower := (rows 113 22 388 138 16 32 64 128 256), losses := [] }

theorem u2995 : Upper (D 0) (R 0) [112,20,384,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2995
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2996 : Route 9 := (fun mask => (mask,id))

def c2996 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2996 : Upper (D 0) (R 0) [112,20,384,160] 13 := by
  apply FastRouting.sound _ _ [112,20,384,160] 13 (by decide) (choices 1) [1,2,8,64] r2996 c2996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1810
  · exact u1811
  · exact u1812
  · exact u1813

def b2997 : PairBound 9 := { available := 333, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 133 138 349 365 333 461 333), lower := (rows 113 50 133 138 16 32 64 128 256), losses := [] }

theorem u2997 : Upper (D 0) (R 0) [112,48,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2997
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2998 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 133 200 287 303 335 399 271), lower := (rows 113 50 133 200 16 32 64 128 256), losses := [] }

theorem u2998 : Upper (D 0) (R 0) [112,48,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2998
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2999 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 113 50 133 265 222 238 206 206 462), lower := (rows 113 50 133 265 16 32 64 128 256), losses := [] }

theorem u2999 : Upper (D 0) (R 0) [112,48,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2999
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u2999
end Delivery.IrregularNine14.P00
