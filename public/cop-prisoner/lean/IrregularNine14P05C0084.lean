import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0030

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r5040 : Route 9 := (fun mask => (mask,id))

def c5040 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5040 : Upper (D 5) (R 5) [6,9,80,384,40] 13 := by
  apply FastRouting.sound _ _ [6,9,80,384,40] 13 (by decide) (choices 1) [1,2,4] r5040 c5040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1800
  · exact u1801
  · exact u1802

def b5041 : PairBound 9 := { available := 284, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 100 168 19 316 348 412 284), lower := (rows 7 11 100 168 19 32 64 128 256), losses := [] }

theorem u5041 : Upper (D 5) (R 5) [6,9,96,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5041
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5042 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 11 100 168 21 314 346 410 282), lower := (rows 7 11 100 168 21 32 64 128 256), losses := [] }

theorem u5042 : Upper (D 5) (R 5) [6,9,96,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5042
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5043 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 11 100 168 22 313 345 409 281), lower := (rows 7 11 100 168 22 32 64 128 256), losses := [] }

theorem u5043 : Upper (D 5) (R 5) [6,9,96,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5043
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5044 : PairBound 9 := { available := 275, camps := [{ cop := 4, region := 3, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 100 168 28 307 339 403 275), lower := (rows 7 11 100 168 28 32 64 128 256), losses := [] }

theorem u5044 : Upper (D 5) (R 5) [6,9,96,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5044
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5045 : Route 9 := (fun mask => (mask,id))

def c5045 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5045 : Upper (D 5) (R 5) [6,9,96,160,257] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,257] 13 (by decide) (choices 1) [2,4,8,16] r5045 c5045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1803
  · exact u1804
  · exact u1805
  · exact u1806

def r5046 : Route 9 := (fun mask => (mask,id))

def c5046 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5046 : Upper (D 5) (R 5) [6,9,96,160,260] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,260] 13 (by decide) (choices 1) [1,2,8,16] r5046 c5046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1807
  · exact u1808
  · exact u1809
  · exact u1810

def b5047 : PairBound 9 := { available := 60, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 100 392 19 60 124 188 316), lower := (rows 7 11 100 392 19 32 64 128 256), losses := [] }

theorem u5047 : Upper (D 5) (R 5) [6,9,96,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5047
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5048 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 11 100 392 21 58 122 186 314), lower := (rows 7 11 100 392 21 32 64 128 256), losses := [] }

theorem u5048 : Upper (D 5) (R 5) [6,9,96,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5048
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5049 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 11 100 392 22 57 121 185 313), lower := (rows 7 11 100 392 22 32 64 128 256), losses := [] }

theorem u5049 : Upper (D 5) (R 5) [6,9,96,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5049
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5050 : PairBound 9 := { available := 54, camps := [{ cop := 1, region := 16, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 7 11 100 392 25 54 118 182 310), lower := (rows 7 11 100 392 25 32 64 128 256), losses := [] }

theorem u5050 : Upper (D 5) (R 5) [6,9,96,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5050
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5051 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 11 100 392 26 53 117 181 309), lower := (rows 7 11 100 392 26 32 64 128 256), losses := [] }

theorem u5051 : Upper (D 5) (R 5) [6,9,96,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5051
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5052 : PairBound 9 := { available := 51, camps := [{ cop := 4, region := 3, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 100 392 28 51 115 179 307), lower := (rows 7 11 100 392 28 32 64 128 256), losses := [] }

theorem u5052 : Upper (D 5) (R 5) [6,9,96,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5052
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5053 : Route 9 := (fun mask => (mask,id))

def c5053 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5053 : Upper (D 5) (R 5) [6,9,96,384,33] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,33] 13 (by decide) (choices 1) [2,4,8,16] r5053 c5053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1811
  · exact u1812
  · exact u1813
  · exact u1814

def r5054 : Route 9 := (fun mask => (mask,id))

def c5054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5054 : Upper (D 5) (R 5) [6,9,96,384,34] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,34] 13 (by decide) (choices 1) [1,4,8,16] r5054 c5054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1815
  · exact u1816
  · exact u1817
  · exact u1818

def b5055 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 100 392 52 59 91 155 283), lower := (rows 7 11 100 392 52 32 64 128 256), losses := [] }

theorem u5055 : Upper (D 5) (R 5) [6,9,96,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5055
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5056 : Route 9 := (fun mask => (mask,id))

def c5056 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5056 : Upper (D 5) (R 5) [6,9,96,384,40] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,40] 13 (by decide) (choices 1) [1,2,4,16] r5056 c5056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1819
  · exact u1820
  · exact u1821
  · exact u1822

def b5057 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 44 73 22 424 488 424 424), lower := (rows 7 19 44 73 22 32 64 128 256), losses := [] }

theorem u5057 : Upper (D 5) (R 5) [6,17,40,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5057
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5058 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 19 44 73 26 420 484 420 420), lower := (rows 7 19 44 73 26 32 64 128 256), losses := [] }

theorem u5058 : Upper (D 5) (R 5) [6,17,40,65,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5058
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5059 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 44 73 28 418 482 418 418), lower := (rows 7 19 44 73 28 32 64 128 256), losses := [] }

theorem u5059 : Upper (D 5) (R 5) [6,17,40,65,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5059
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5060 : PairBound 9 := { available := 396, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 44 73 50 428 460 396 396), lower := (rows 7 19 44 73 50 32 64 128 256), losses := [] }

theorem u5060 : Upper (D 5) (R 5) [6,17,40,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5060
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5061 : PairBound 9 := { available := 394, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 44 73 52 426 458 394 394), lower := (rows 7 19 44 73 52 32 64 128 256), losses := [] }

theorem u5061 : Upper (D 5) (R 5) [6,17,40,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5061
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5062 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 44 73 56 422 454 390 390), lower := (rows 7 19 44 73 56 32 64 128 256), losses := [] }

theorem u5062 : Upper (D 5) (R 5) [6,17,40,65,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5062
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5063 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 44 73 146 300 364 428 300), lower := (rows 7 19 44 73 146 32 64 128 256), losses := [] }

theorem u5063 : Upper (D 5) (R 5) [6,17,40,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5063
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5064 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 44 73 148 298 362 426 298), lower := (rows 7 19 44 73 148 32 64 128 256), losses := [] }

theorem u5064 : Upper (D 5) (R 5) [6,17,40,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5064
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5065 : PairBound 9 := { available := 294, camps := [], pairs := [(2,0),(4,0)], upper := (rows 7 19 44 73 152 294 358 422 294), lower := (rows 7 19 44 73 152 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 33 65 129 257), good := (rows 486 498 60 508 156 32 64 128 256) }] }

theorem u5065 : Upper (D 5) (R 5) [6,17,40,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5065
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5066 : Route 9 := (fun mask => (mask,id))

def c5066 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5066 : Upper (D 5) (R 5) [6,17,40,65,160] 13 := by
  apply FastRouting.sound _ _ [6,17,40,65,160] 13 (by decide) (choices 1) [2,4,8,256] r5066 c5066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1823
  · exact u1824
  · exact u1825
  · exact u1826

def r5067 : Route 9 := (fun mask => (mask,id))

def c5067 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5067 : Upper (D 5) (R 5) [6,17,40,65,384] 13 := by
  apply FastRouting.sound _ _ [6,17,40,65,384] 13 (by decide) (choices 1) [2,4,8] r5067 c5067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1827
  · exact u1828
  · exact u1829

def b5068 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 44 74 21 424 488 424 424), lower := (rows 7 19 44 74 21 32 64 128 256), losses := [] }

theorem u5068 : Upper (D 5) (R 5) [6,17,40,66,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5068
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5069 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 44 74 25 420 484 420 420), lower := (rows 7 19 44 74 25 32 64 128 256), losses := [] }

theorem u5069 : Upper (D 5) (R 5) [6,17,40,66,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5069
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5070 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 44 74 28 417 481 417 417), lower := (rows 7 19 44 74 28 32 64 128 256), losses := [] }

theorem u5070 : Upper (D 5) (R 5) [6,17,40,66,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5070
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5071 : PairBound 9 := { available := 396, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 44 74 49 428 460 396 396), lower := (rows 7 19 44 74 49 32 64 128 256), losses := [] }

theorem u5071 : Upper (D 5) (R 5) [6,17,40,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5071
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5072 : PairBound 9 := { available := 393, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 44 74 52 425 457 393 393), lower := (rows 7 19 44 74 52 32 64 128 256), losses := [] }

theorem u5072 : Upper (D 5) (R 5) [6,17,40,66,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5072
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5073 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 44 74 56 421 453 389 389), lower := (rows 7 19 44 74 56 32 64 128 256), losses := [] }

theorem u5073 : Upper (D 5) (R 5) [6,17,40,66,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5073
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5074 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 44 74 145 300 364 428 300), lower := (rows 7 19 44 74 145 32 64 128 256), losses := [] }

theorem u5074 : Upper (D 5) (R 5) [6,17,40,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5074
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5075 : PairBound 9 := { available := 297, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 44 74 148 297 361 425 297), lower := (rows 7 19 44 74 148 32 64 128 256), losses := [] }

theorem u5075 : Upper (D 5) (R 5) [6,17,40,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5075
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5076 : Route 9 := (fun mask => (mask,id))

def c5076 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5076 : Upper (D 5) (R 5) [6,17,40,66,136] 13 := by
  apply FastRouting.sound _ _ [6,17,40,66,136] 13 (by decide) (choices 1) [1,4,256] r5076 c5076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1830
  · exact u1831
  · exact u1832

def r5077 : Route 9 := (fun mask => (mask,id))

def c5077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5077 : Upper (D 5) (R 5) [6,17,40,66,160] 13 := by
  apply FastRouting.sound _ _ [6,17,40,66,160] 13 (by decide) (choices 1) [1,4,8,256] r5077 c5077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1833
  · exact u1834
  · exact u1835
  · exact u1836

def r5078 : Route 9 := (fun mask => (mask,id))

def c5078 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5078 : Upper (D 5) (R 5) [6,17,40,66,384] 13 := by
  apply FastRouting.sound _ _ [6,17,40,66,384] 13 (by decide) (choices 1) [1,4,8] r5078 c5078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1837
  · exact u1838
  · exact u1839

def b5079 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 18, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 44 76 19 424 488 424 424), lower := (rows 7 19 44 76 19 32 64 128 256), losses := [] }

theorem u5079 : Upper (D 5) (R 5) [6,17,40,68,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5079
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5080 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 44 76 25 418 482 418 418), lower := (rows 7 19 44 76 25 32 64 128 256), losses := [] }

theorem u5080 : Upper (D 5) (R 5) [6,17,40,68,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5080
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5081 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 44 76 26 417 481 417 417), lower := (rows 7 19 44 76 26 32 64 128 256), losses := [] }

theorem u5081 : Upper (D 5) (R 5) [6,17,40,68,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5081
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5082 : PairBound 9 := { available := 394, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 44 76 49 426 458 394 394), lower := (rows 7 19 44 76 49 32 64 128 256), losses := [] }

theorem u5082 : Upper (D 5) (R 5) [6,17,40,68,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5082
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5083 : PairBound 9 := { available := 393, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 44 76 50 425 457 393 393), lower := (rows 7 19 44 76 50 32 64 128 256), losses := [] }

theorem u5083 : Upper (D 5) (R 5) [6,17,40,68,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5083
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5084 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 44 76 56 419 451 387 387), lower := (rows 7 19 44 76 56 32 64 128 256), losses := [] }

theorem u5084 : Upper (D 5) (R 5) [6,17,40,68,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5084
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5085 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 44 76 145 298 362 426 298), lower := (rows 7 19 44 76 145 32 64 128 256), losses := [] }

theorem u5085 : Upper (D 5) (R 5) [6,17,40,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5085
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5086 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 44 76 146 297 361 425 297), lower := (rows 7 19 44 76 146 32 64 128 256), losses := [] }

theorem u5086 : Upper (D 5) (R 5) [6,17,40,68,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5086
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5087 : Route 9 := (fun mask => (mask,id))

def c5087 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5087 : Upper (D 5) (R 5) [6,17,40,68,136] 13 := by
  apply FastRouting.sound _ _ [6,17,40,68,136] 13 (by decide) (choices 1) [1,2,256] r5087 c5087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1840
  · exact u1841
  · exact u1842

def r5088 : Route 9 := (fun mask => (mask,id))

def c5088 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5088 : Upper (D 5) (R 5) [6,17,40,68,160] 13 := by
  apply FastRouting.sound _ _ [6,17,40,68,160] 13 (by decide) (choices 1) [1,2,8,256] r5088 c5088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1843
  · exact u1844
  · exact u1845
  · exact u1846

def r5089 : Route 9 := (fun mask => (mask,id))

def c5089 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5089 : Upper (D 5) (R 5) [6,17,40,68,384] 13 := by
  apply FastRouting.sound _ _ [6,17,40,68,384] 13 (by decide) (choices 1) [1,2,8] r5089 c5089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1847
  · exact u1848
  · exact u1849

def b5090 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 18, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 44 200 19 300 364 428 300), lower := (rows 7 19 44 200 19 32 64 128 256), losses := [] }

theorem u5090 : Upper (D 5) (R 5) [6,17,40,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5090
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5091 : PairBound 9 := { available := 298, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 44 200 21 298 362 426 298), lower := (rows 7 19 44 200 21 32 64 128 256), losses := [] }

theorem u5091 : Upper (D 5) (R 5) [6,17,40,192,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5091
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5092 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 44 200 22 297 361 425 297), lower := (rows 7 19 44 200 22 32 64 128 256), losses := [] }

theorem u5092 : Upper (D 5) (R 5) [6,17,40,192,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5092
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5093 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 44 200 25 294 358 422 294), lower := (rows 7 19 44 200 25 32 64 128 256), losses := [] }

theorem u5093 : Upper (D 5) (R 5) [6,17,40,192,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5093
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5094 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 44 200 26 293 357 421 293), lower := (rows 7 19 44 200 26 32 64 128 256), losses := [] }

theorem u5094 : Upper (D 5) (R 5) [6,17,40,192,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5094
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5095 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 44 200 28 291 355 419 291), lower := (rows 7 19 44 200 28 32 64 128 256), losses := [] }

theorem u5095 : Upper (D 5) (R 5) [6,17,40,192,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5095
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5096 : PairBound 9 := { available := 270, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 44 200 49 302 334 398 270), lower := (rows 7 19 44 200 49 32 64 128 256), losses := [] }

theorem u5096 : Upper (D 5) (R 5) [6,17,40,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5096
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5097 : PairBound 9 := { available := 269, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 44 200 50 301 333 397 269), lower := (rows 7 19 44 200 50 32 64 128 256), losses := [] }

theorem u5097 : Upper (D 5) (R 5) [6,17,40,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5097
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5098 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 44 200 52 299 331 395 267), lower := (rows 7 19 44 200 52 32 64 128 256), losses := [] }

theorem u5098 : Upper (D 5) (R 5) [6,17,40,192,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5098
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5099 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 44 200 56 295 327 391 263), lower := (rows 7 19 44 200 56 32 64 128 256), losses := [] }

theorem u5099 : Upper (D 5) (R 5) [6,17,40,192,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5099
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u5099
end Delivery.IrregularNine14.P05
