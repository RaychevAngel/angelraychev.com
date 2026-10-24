import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0030
import IrregularNine14P05C0031

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5100 : PairBound 9 := { available := 46, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 44 200 273 46 110 174 302), lower := (rows 7 19 44 200 273 32 64 128 256), losses := [] }

theorem u5100 : Upper (D 5) (R 5) [6,17,40,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5100
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5101 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 44 200 274 45 109 173 301), lower := (rows 7 19 44 200 274 32 64 128 256), losses := [] }

theorem u5101 : Upper (D 5) (R 5) [6,17,40,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5101
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5102 : PairBound 9 := { available := 43, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 44 200 276 43 107 171 299), lower := (rows 7 19 44 200 276 32 64 128 256), losses := [] }

theorem u5102 : Upper (D 5) (R 5) [6,17,40,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5102
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5103 : Route 9 := (fun mask => (mask,id))

def c5103 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5103 : Upper (D 5) (R 5) [6,17,40,192,264] 13 := by
  apply FastRouting.sound _ _ [6,17,40,192,264] 13 (by decide) (choices 1) [1,2,4] r5103 c5103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1850
  · exact u1851
  · exact u1852

def r5104 : Route 9 := (fun mask => (mask,id))

def c5104 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5104 : Upper (D 5) (R 5) [6,17,40,192,288] 13 := by
  apply FastRouting.sound _ _ [6,17,40,192,288] 13 (by decide) (choices 1) [1,2,4,8] r5104 c5104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1853
  · exact u1854
  · exact u1855
  · exact u1856

def b5105 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 41 22 424 488 424 424), lower := (rows 7 19 76 41 22 32 64 128 256), losses := [] }

theorem u5105 : Upper (D 5) (R 5) [6,17,72,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5105
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5106 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 19 76 41 26 420 484 420 420), lower := (rows 7 19 76 41 26 32 64 128 256), losses := [] }

theorem u5106 : Upper (D 5) (R 5) [6,17,72,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5106
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5107 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 41 28 418 482 418 418), lower := (rows 7 19 76 41 28 32 64 128 256), losses := [] }

theorem u5107 : Upper (D 5) (R 5) [6,17,72,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5107
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5108 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 76 41 50 428 460 396 396), lower := (rows 7 19 76 41 50 32 64 128 256), losses := [] }

theorem u5108 : Upper (D 5) (R 5) [6,17,72,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5108
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5109 : PairBound 9 := { available := 394, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 41 52 426 458 394 394), lower := (rows 7 19 76 41 52 32 64 128 256), losses := [] }

theorem u5109 : Upper (D 5) (R 5) [6,17,72,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5109
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5110 : PairBound 9 := { available := 390, camps := [{ cop := 4, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 41 56 422 454 390 390), lower := (rows 7 19 76 41 56 32 64 128 256), losses := [] }

theorem u5110 : Upper (D 5) (R 5) [6,17,72,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5110
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5111 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 76 41 146 300 364 428 300), lower := (rows 7 19 76 41 146 32 64 128 256), losses := [] }

theorem u5111 : Upper (D 5) (R 5) [6,17,72,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5111
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5112 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 41 148 298 362 426 298), lower := (rows 7 19 76 41 148 32 64 128 256), losses := [] }

theorem u5112 : Upper (D 5) (R 5) [6,17,72,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5112
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5113 : PairBound 9 := { available := 294, camps := [], pairs := [(2,0),(4,0)], upper := (rows 7 19 76 41 152 294 358 422 294), lower := (rows 7 19 76 41 152 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 33 65 129 257), good := (rows 486 498 92 508 156 32 64 128 256) }] }

theorem u5113 : Upper (D 5) (R 5) [6,17,72,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5113
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5114 : Route 9 := (fun mask => (mask,id))

def c5114 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5114 : Upper (D 5) (R 5) [6,17,72,33,160] 13 := by
  apply FastRouting.sound _ _ [6,17,72,33,160] 13 (by decide) (choices 1) [2,4,8,256] r5114 c5114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1857
  · exact u1858
  · exact u1859
  · exact u1860

def r5115 : Route 9 := (fun mask => (mask,id))

def c5115 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5115 : Upper (D 5) (R 5) [6,17,72,33,384] 13 := by
  apply FastRouting.sound _ _ [6,17,72,33,384] 13 (by decide) (choices 1) [2,4,8] r5115 c5115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1861
  · exact u1862
  · exact u1863

def b5116 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 42 21 424 488 424 424), lower := (rows 7 19 76 42 21 32 64 128 256), losses := [] }

theorem u5116 : Upper (D 5) (R 5) [6,17,72,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5116
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5117 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 42 25 420 484 420 420), lower := (rows 7 19 76 42 25 32 64 128 256), losses := [] }

theorem u5117 : Upper (D 5) (R 5) [6,17,72,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5117
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5118 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 42 28 417 481 417 417), lower := (rows 7 19 76 42 28 32 64 128 256), losses := [] }

theorem u5118 : Upper (D 5) (R 5) [6,17,72,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5118
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5119 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 19 76 42 49 428 460 396 396), lower := (rows 7 19 76 42 49 32 64 128 256), losses := [] }

theorem u5119 : Upper (D 5) (R 5) [6,17,72,34,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5119
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5120 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 42 52 425 457 393 393), lower := (rows 7 19 76 42 52 32 64 128 256), losses := [] }

theorem u5120 : Upper (D 5) (R 5) [6,17,72,34,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5120
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5121 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 76 42 56 421 453 389 389), lower := (rows 7 19 76 42 56 32 64 128 256), losses := [] }

theorem u5121 : Upper (D 5) (R 5) [6,17,72,34,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5121
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5122 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 42 145 300 364 428 300), lower := (rows 7 19 76 42 145 32 64 128 256), losses := [] }

theorem u5122 : Upper (D 5) (R 5) [6,17,72,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5122
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5123 : PairBound 9 := { available := 297, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 42 148 297 361 425 297), lower := (rows 7 19 76 42 148 32 64 128 256), losses := [] }

theorem u5123 : Upper (D 5) (R 5) [6,17,72,34,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5123
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5124 : Route 9 := (fun mask => (mask,id))

def c5124 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5124 : Upper (D 5) (R 5) [6,17,72,34,136] 13 := by
  apply FastRouting.sound _ _ [6,17,72,34,136] 13 (by decide) (choices 1) [1,4,256] r5124 c5124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1864
  · exact u1865
  · exact u1866

def b5125 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 19 76 42 176 301 333 397 269), lower := (rows 7 19 76 42 176 32 64 128 256), losses := [] }

theorem u5125 : Upper (D 5) (R 5) [6,17,72,34,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5125
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5126 : Route 9 := (fun mask => (mask,id))

def c5126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5126 : Upper (D 5) (R 5) [6,17,72,34,384] 13 := by
  apply FastRouting.sound _ _ [6,17,72,34,384] 13 (by decide) (choices 1) [1,4,8] r5126 c5126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1867
  · exact u1868
  · exact u1869

def b5127 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 18, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 44 19 424 488 424 424), lower := (rows 7 19 76 44 19 32 64 128 256), losses := [] }

theorem u5127 : Upper (D 5) (R 5) [6,17,72,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5127
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5128 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 44 25 418 482 418 418), lower := (rows 7 19 76 44 25 32 64 128 256), losses := [] }

theorem u5128 : Upper (D 5) (R 5) [6,17,72,36,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5128
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5129 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 44 26 417 481 417 417), lower := (rows 7 19 76 44 26 32 64 128 256), losses := [] }

theorem u5129 : Upper (D 5) (R 5) [6,17,72,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5129
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5130 : PairBound 9 := { available := 394, camps := [{ cop := 3, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 76 44 49 426 458 394 394), lower := (rows 7 19 76 44 49 32 64 128 256), losses := [] }

theorem u5130 : Upper (D 5) (R 5) [6,17,72,36,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5130
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5131 : PairBound 9 := { available := 393, camps := [{ cop := 3, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 76 44 50 425 457 393 393), lower := (rows 7 19 76 44 50 32 64 128 256), losses := [] }

theorem u5131 : Upper (D 5) (R 5) [6,17,72,36,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5131
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5132 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 76 44 56 419 451 387 387), lower := (rows 7 19 76 44 56 32 64 128 256), losses := [] }

theorem u5132 : Upper (D 5) (R 5) [6,17,72,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5132
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5133 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 44 145 298 362 426 298), lower := (rows 7 19 76 44 145 32 64 128 256), losses := [] }

theorem u5133 : Upper (D 5) (R 5) [6,17,72,36,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5133
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5134 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 76 44 146 297 361 425 297), lower := (rows 7 19 76 44 146 32 64 128 256), losses := [] }

theorem u5134 : Upper (D 5) (R 5) [6,17,72,36,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5134
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5135 : Route 9 := (fun mask => (mask,id))

def c5135 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5135 : Upper (D 5) (R 5) [6,17,72,36,136] 13 := by
  apply FastRouting.sound _ _ [6,17,72,36,136] 13 (by decide) (choices 1) [1,2,256] r5135 c5135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1870
  · exact u1871
  · exact u1872

def r5136 : Route 9 := (fun mask => (mask,id))

def c5136 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5136 : Upper (D 5) (R 5) [6,17,72,36,160] 13 := by
  apply FastRouting.sound _ _ [6,17,72,36,160] 13 (by decide) (choices 1) [1,2,8,256] r5136 c5136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1873
  · exact u1874
  · exact u1875
  · exact u1876

def r5137 : Route 9 := (fun mask => (mask,id))

def c5137 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5137 : Upper (D 5) (R 5) [6,17,72,36,384] 13 := by
  apply FastRouting.sound _ _ [6,17,72,36,384] 13 (by decide) (choices 1) [1,2,8] r5137 c5137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1877
  · exact u1878
  · exact u1879

def b5138 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 137 22 296 360 424 296), lower := (rows 7 19 76 137 22 32 64 128 256), losses := [] }

theorem u5138 : Upper (D 5) (R 5) [6,17,72,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5138
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5139 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 19 76 137 26 292 356 420 292), lower := (rows 7 19 76 137 26 32 64 128 256), losses := [] }

theorem u5139 : Upper (D 5) (R 5) [6,17,72,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5139
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5140 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 137 28 290 354 418 290), lower := (rows 7 19 76 137 28 32 64 128 256), losses := [] }

theorem u5140 : Upper (D 5) (R 5) [6,17,72,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5140
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5141 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 76 137 50 300 364 428 300), lower := (rows 7 19 76 137 50 32 64 128 256), losses := [] }

theorem u5141 : Upper (D 5) (R 5) [6,17,72,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5141
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5142 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 137 52 298 362 426 298), lower := (rows 7 19 76 137 52 32 64 128 256), losses := [] }

theorem u5142 : Upper (D 5) (R 5) [6,17,72,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5142
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5143 : PairBound 9 := { available := 294, camps := [], pairs := [(2,0),(4,0)], upper := (rows 7 19 76 137 56 294 358 422 294), lower := (rows 7 19 76 137 56 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 33 65 129 257), good := (rows 486 498 92 508 60 32 64 128 256) }] }

theorem u5143 : Upper (D 5) (R 5) [6,17,72,129,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5143
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5144 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 76 137 274 44 108 172 300), lower := (rows 7 19 76 137 274 32 64 128 256), losses := [] }

theorem u5144 : Upper (D 5) (R 5) [6,17,72,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5144
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5145 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 137 276 42 106 170 298), lower := (rows 7 19 76 137 276 32 64 128 256), losses := [] }

theorem u5145 : Upper (D 5) (R 5) [6,17,72,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5145
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5146 : PairBound 9 := { available := 38, camps := [], pairs := [(2,0),(4,0)], upper := (rows 7 19 76 137 280 38 102 166 294), lower := (rows 7 19 76 137 280 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 33 65 129 257), good := (rows 486 498 92 508 284 32 64 128 256) }] }

theorem u5146 : Upper (D 5) (R 5) [6,17,72,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5146
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5147 : Route 9 := (fun mask => (mask,id))

def c5147 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5147 : Upper (D 5) (R 5) [6,17,72,129,288] 13 := by
  apply FastRouting.sound _ _ [6,17,72,129,288] 13 (by decide) (choices 1) [2,4,8] r5147 c5147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1880
  · exact u1881
  · exact u1882

def b5148 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 138 21 296 360 424 296), lower := (rows 7 19 76 138 21 32 64 128 256), losses := [] }

theorem u5148 : Upper (D 5) (R 5) [6,17,72,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5148
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5149 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 138 25 292 356 420 292), lower := (rows 7 19 76 138 25 32 64 128 256), losses := [] }

theorem u5149 : Upper (D 5) (R 5) [6,17,72,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5149
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5150 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 138 28 289 353 417 289), lower := (rows 7 19 76 138 28 32 64 128 256), losses := [] }

theorem u5150 : Upper (D 5) (R 5) [6,17,72,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5150
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5151 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 138 49 300 364 428 300), lower := (rows 7 19 76 138 49 32 64 128 256), losses := [] }

theorem u5151 : Upper (D 5) (R 5) [6,17,72,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5151
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5152 : PairBound 9 := { available := 297, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 138 52 297 361 425 297), lower := (rows 7 19 76 138 52 32 64 128 256), losses := [] }

theorem u5152 : Upper (D 5) (R 5) [6,17,72,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5152
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5153 : Route 9 := (fun mask => (mask,id))

def c5153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5153 : Upper (D 5) (R 5) [6,17,72,130,40] 13 := by
  apply FastRouting.sound _ _ [6,17,72,130,40] 13 (by decide) (choices 1) [1,4,256] r5153 c5153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1883
  · exact u1884
  · exact u1885

def b5154 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 138 273 44 108 172 300), lower := (rows 7 19 76 138 273 32 64 128 256), losses := [] }

theorem u5154 : Upper (D 5) (R 5) [6,17,72,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5154
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5155 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 138 276 41 105 169 297), lower := (rows 7 19 76 138 276 32 64 128 256), losses := [] }

theorem u5155 : Upper (D 5) (R 5) [6,17,72,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5155
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5156 : Route 9 := (fun mask => (mask,id))

def c5156 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5156 : Upper (D 5) (R 5) [6,17,72,130,264] 13 := by
  apply FastRouting.sound _ _ [6,17,72,130,264] 13 (by decide) (choices 1) [1,4] r5156 c5156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1886
  · exact u1887

def r5157 : Route 9 := (fun mask => (mask,id))

def c5157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5157 : Upper (D 5) (R 5) [6,17,72,130,288] 13 := by
  apply FastRouting.sound _ _ [6,17,72,130,288] 13 (by decide) (choices 1) [1,4,8] r5157 c5157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1888
  · exact u1889
  · exact u1890

def b5158 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 18, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 140 19 296 360 424 296), lower := (rows 7 19 76 140 19 32 64 128 256), losses := [] }

theorem u5158 : Upper (D 5) (R 5) [6,17,72,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5158
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5159 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 140 25 290 354 418 290), lower := (rows 7 19 76 140 25 32 64 128 256), losses := [] }

theorem u5159 : Upper (D 5) (R 5) [6,17,72,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5159
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u5159
end Delivery.IrregularNine14.P05
