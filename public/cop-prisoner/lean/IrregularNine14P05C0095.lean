import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0036
import IrregularNine14P05C0037

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r5700 : Route 9 := (fun mask => (mask,id))

def c5700 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5700 : Upper (D 5) (R 5) [6,33,72,48,130] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,130] 13 (by decide) (choices 1) [1,4,8,256] r5700 c5700
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2164
  · exact u2165
  · exact u2166
  · exact u2167

def r5701 : Route 9 := (fun mask => (mask,id))

def c5701 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5701 : Upper (D 5) (R 5) [6,33,72,48,132] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,132] 13 (by decide) (choices 1) [1,2,8,256] r5701 c5701
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2168
  · exact u2169
  · exact u2170
  · exact u2171

def b5702 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 291, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 76 56 152 295 327 391 263), lower := (rows 7 35 76 56 152 32 64 128 256), losses := [] }

theorem u5702 : Upper (D 5) (R 5) [6,33,72,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5702
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5703 : Route 9 := (fun mask => (mask,id))

def c5703 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5703 : Upper (D 5) (R 5) [6,33,72,48,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,384] 13 (by decide) (choices 1) [1,2,4,8] r5703 c5703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2172
  · exact u2173
  · exact u2174
  · exact u2175

def b5704 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 35 76 137 22 312 376 440 312), lower := (rows 7 35 76 137 22 32 64 128 256), losses := [] }

theorem u5704 : Upper (D 5) (R 5) [6,33,72,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5704
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5705 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 137 26 308 372 436 308), lower := (rows 7 35 76 137 26 32 64 128 256), losses := [] }

theorem u5705 : Upper (D 5) (R 5) [6,33,72,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5705
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5706 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 76 137 28 306 370 434 306), lower := (rows 7 35 76 137 28 32 64 128 256), losses := [] }

theorem u5706 : Upper (D 5) (R 5) [6,33,72,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5706
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5707 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 35 76 137 50 316 348 412 284), lower := (rows 7 35 76 137 50 32 64 128 256), losses := [] }

theorem u5707 : Upper (D 5) (R 5) [6,33,72,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5707
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5708 : PairBound 9 := { available := 282, camps := [{ cop := 4, region := 3, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 76 137 52 314 346 410 282), lower := (rows 7 35 76 137 52 32 64 128 256), losses := [] }

theorem u5708 : Upper (D 5) (R 5) [6,33,72,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5708
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5709 : Route 9 := (fun mask => (mask,id))

def c5709 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5709 : Upper (D 5) (R 5) [6,33,72,129,40] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,40] 13 (by decide) (choices 1) [2,4,16,256] r5709 c5709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2176
  · exact u2177
  · exact u2178
  · exact u2179

def r5710 : Route 9 := (fun mask => (mask,id))

def c5710 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5710 : Upper (D 5) (R 5) [6,33,72,129,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,258] 13 (by decide) (choices 1) [4,8,16] r5710 c5710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2180
  · exact u2181
  · exact u2182

def r5711 : Route 9 := (fun mask => (mask,id))

def c5711 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5711 : Upper (D 5) (R 5) [6,33,72,129,260] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,260] 13 (by decide) (choices 1) [2,8,16] r5711 c5711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2183
  · exact u2184
  · exact u2185

def r5712 : Route 9 := (fun mask => (mask,id))

def c5712 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5712 : Upper (D 5) (R 5) [6,33,72,129,264] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,264] 13 (by decide) (choices 1) [2,4,16] r5712 c5712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2186
  · exact u2187
  · exact u2188

def r5713 : Route 9 := (fun mask => (mask,id))

def c5713 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5713 : Upper (D 5) (R 5) [6,33,72,129,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,288] 13 (by decide) (choices 1) [2,4,8,16] r5713 c5713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2189
  · exact u2190
  · exact u2191
  · exact u2192

def b5714 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 35 76 138 21 312 376 440 312), lower := (rows 7 35 76 138 21 32 64 128 256), losses := [] }

theorem u5714 : Upper (D 5) (R 5) [6,33,72,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5714
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5715 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 138 25 308 372 436 308), lower := (rows 7 35 76 138 25 32 64 128 256), losses := [] }

theorem u5715 : Upper (D 5) (R 5) [6,33,72,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5715
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5716 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 76 138 28 305 369 433 305), lower := (rows 7 35 76 138 28 32 64 128 256), losses := [] }

theorem u5716 : Upper (D 5) (R 5) [6,33,72,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5716
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5717 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 76 138 49 316 348 412 284), lower := (rows 7 35 76 138 49 32 64 128 256), losses := [] }

theorem u5717 : Upper (D 5) (R 5) [6,33,72,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5717
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5718 : PairBound 9 := { available := 281, camps := [{ cop := 4, region := 3, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 76 138 52 313 345 409 281), lower := (rows 7 35 76 138 52 32 64 128 256), losses := [] }

theorem u5718 : Upper (D 5) (R 5) [6,33,72,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5718
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5719 : Route 9 := (fun mask => (mask,id))

def c5719 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5719 : Upper (D 5) (R 5) [6,33,72,130,40] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,40] 13 (by decide) (choices 1) [1,4,16,256] r5719 c5719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2193
  · exact u2194
  · exact u2195
  · exact u2196

def r5720 : Route 9 := (fun mask => (mask,id))

def c5720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5720 : Upper (D 5) (R 5) [6,33,72,130,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,257] 13 (by decide) (choices 1) [4,8,16] r5720 c5720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2197
  · exact u2198
  · exact u2199

def r5721 : Route 9 := (fun mask => (mask,id))

def c5721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5721 : Upper (D 5) (R 5) [6,33,72,130,260] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,260] 13 (by decide) (choices 1) [1,8,16] r5721 c5721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2200
  · exact u2201
  · exact u2202

def r5722 : Route 9 := (fun mask => (mask,id))

def c5722 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5722 : Upper (D 5) (R 5) [6,33,72,130,264] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,264] 13 (by decide) (choices 1) [1,4,16] r5722 c5722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2203
  · exact u2204
  · exact u2205

def r5723 : Route 9 := (fun mask => (mask,id))

def c5723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5723 : Upper (D 5) (R 5) [6,33,72,130,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,288] 13 (by decide) (choices 1) [1,4,8,16] r5723 c5723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2206
  · exact u2207
  · exact u2208
  · exact u2209

def b5724 : PairBound 9 := { available := 312, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 140 19 312 376 440 312), lower := (rows 7 35 76 140 19 32 64 128 256), losses := [] }

theorem u5724 : Upper (D 5) (R 5) [6,33,72,132,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5724
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5725 : PairBound 9 := { available := 306, camps := [{ cop := 4, region := 290, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 35 76 140 25 306 370 434 306), lower := (rows 7 35 76 140 25 32 64 128 256), losses := [] }

theorem u5725 : Upper (D 5) (R 5) [6,33,72,132,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5725
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5726 : Route 9 := (fun mask => (mask,id))

def c5726 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5726 : Upper (D 5) (R 5) [6,33,72,132,10] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,10] 13 (by decide) (choices 1) [1,16,256] r5726 c5726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2210
  · exact u2211
  · exact u2212

def b5727 : PairBound 9 := { available := 282, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 76 140 49 314 346 410 282), lower := (rows 7 35 76 140 49 32 64 128 256), losses := [] }

theorem u5727 : Upper (D 5) (R 5) [6,33,72,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5727
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5728 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 35 76 140 50 313 345 409 281), lower := (rows 7 35 76 140 50 32 64 128 256), losses := [] }

theorem u5728 : Upper (D 5) (R 5) [6,33,72,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5728
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5729 : Route 9 := (fun mask => (mask,id))

def c5729 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5729 : Upper (D 5) (R 5) [6,33,72,132,40] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,40] 13 (by decide) (choices 1) [1,2,16,256] r5729 c5729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2213
  · exact u2214
  · exact u2215
  · exact u2216

def r5730 : Route 9 := (fun mask => (mask,id))

def c5730 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5730 : Upper (D 5) (R 5) [6,33,72,132,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,257] 13 (by decide) (choices 1) [2,8,16] r5730 c5730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2217
  · exact u2218
  · exact u2219

def r5731 : Route 9 := (fun mask => (mask,id))

def c5731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5731 : Upper (D 5) (R 5) [6,33,72,132,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,258] 13 (by decide) (choices 1) [1,8,16] r5731 c5731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2220
  · exact u2221
  · exact u2222

def r5732 : Route 9 := (fun mask => (mask,id))

def c5732 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5732 : Upper (D 5) (R 5) [6,33,72,132,264] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,264] 13 (by decide) (choices 1) [1,2,16] r5732 c5732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2223
  · exact u2224
  · exact u2225

def r5733 : Route 9 := (fun mask => (mask,id))

def c5733 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5733 : Upper (D 5) (R 5) [6,33,72,132,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,288] 13 (by decide) (choices 1) [1,2,8,16] r5733 c5733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2226
  · exact u2227
  · exact u2228
  · exact u2229

def b5734 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 152 19 300 364 428 300), lower := (rows 7 35 76 152 19 32 64 128 256), losses := [] }

theorem u5734 : Upper (D 5) (R 5) [6,33,72,144,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5734
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5735 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 35 76 152 21 298 362 426 298), lower := (rows 7 35 76 152 21 32 64 128 256), losses := [] }

theorem u5735 : Upper (D 5) (R 5) [6,33,72,144,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5735
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5736 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 35 76 152 22 297 361 425 297), lower := (rows 7 35 76 152 22 32 64 128 256), losses := [] }

theorem u5736 : Upper (D 5) (R 5) [6,33,72,144,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5736
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5737 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 291, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 76 152 25 294 358 422 294), lower := (rows 7 35 76 152 25 32 64 128 256), losses := [] }

theorem u5737 : Upper (D 5) (R 5) [6,33,72,144,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5737
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5738 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 291, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 76 152 26 293 357 421 293), lower := (rows 7 35 76 152 26 32 64 128 256), losses := [] }

theorem u5738 : Upper (D 5) (R 5) [6,33,72,144,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5738
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5739 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 76 152 28 291 355 419 291), lower := (rows 7 35 76 152 28 32 64 128 256), losses := [] }

theorem u5739 : Upper (D 5) (R 5) [6,33,72,144,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5739
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5740 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 76 152 49 302 334 398 270), lower := (rows 7 35 76 152 49 32 64 128 256), losses := [] }

theorem u5740 : Upper (D 5) (R 5) [6,33,72,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5740
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5741 : PairBound 9 := { available := 269, camps := [{ cop := 1, region := 16, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 35 76 152 50 301 333 397 269), lower := (rows 7 35 76 152 50 32 64 128 256), losses := [] }

theorem u5741 : Upper (D 5) (R 5) [6,33,72,144,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5741
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5742 : PairBound 9 := { available := 267, camps := [{ cop := 4, region := 3, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 76 152 52 299 331 395 267), lower := (rows 7 35 76 152 52 32 64 128 256), losses := [] }

theorem u5742 : Upper (D 5) (R 5) [6,33,72,144,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5742
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5743 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 291, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 76 152 56 295 327 391 263), lower := (rows 7 35 76 152 56 32 64 128 256), losses := [] }

theorem u5743 : Upper (D 5) (R 5) [6,33,72,144,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5743
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5744 : Route 9 := (fun mask => (mask,id))

def c5744 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5744 : Upper (D 5) (R 5) [6,33,72,144,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,257] 13 (by decide) (choices 1) [2,4,8] r5744 c5744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2230
  · exact u2231
  · exact u2232

def r5745 : Route 9 := (fun mask => (mask,id))

def c5745 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5745 : Upper (D 5) (R 5) [6,33,72,144,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,258] 13 (by decide) (choices 1) [1,4,8] r5745 c5745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2233
  · exact u2234
  · exact u2235

def r5746 : Route 9 := (fun mask => (mask,id))

def c5746 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5746 : Upper (D 5) (R 5) [6,33,72,144,260] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,260] 13 (by decide) (choices 1) [1,2,8] r5746 c5746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2236
  · exact u2237
  · exact u2238

def b5747 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 76 152 280 39 103 167 295), lower := (rows 7 35 76 152 280 32 64 128 256), losses := [] }

theorem u5747 : Upper (D 5) (R 5) [6,33,72,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5747
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5748 : Route 9 := (fun mask => (mask,id))

def c5748 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5748 : Upper (D 5) (R 5) [6,33,72,144,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,288] 13 (by decide) (choices 1) [1,2,4,8] r5748 c5748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2239
  · exact u2240
  · exact u2241
  · exact u2242

def b5749 : PairBound 9 := { available := 284, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 168 19 316 348 412 284), lower := (rows 7 35 76 168 19 32 64 128 256), losses := [] }

theorem u5749 : Upper (D 5) (R 5) [6,33,72,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5749
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5750 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 35 76 168 21 314 346 410 282), lower := (rows 7 35 76 168 21 32 64 128 256), losses := [] }

theorem u5750 : Upper (D 5) (R 5) [6,33,72,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5750
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5751 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 35 76 168 22 313 345 409 281), lower := (rows 7 35 76 168 22 32 64 128 256), losses := [] }

theorem u5751 : Upper (D 5) (R 5) [6,33,72,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5751
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5752 : Route 9 := (fun mask => (mask,id))

def c5752 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5752 : Upper (D 5) (R 5) [6,33,72,160,9] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,9] 13 (by decide) (choices 1) [2,4,16,256] r5752 c5752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2243
  · exact u2244
  · exact u2245
  · exact u2246

def b5753 : PairBound 9 := { available := 277, camps := [{ cop := 4, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 76 168 26 309 341 405 277), lower := (rows 7 35 76 168 26 32 64 128 256), losses := [] }

theorem u5753 : Upper (D 5) (R 5) [6,33,72,160,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5753
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5754 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 76 168 28 307 339 403 275), lower := (rows 7 35 76 168 28 32 64 128 256), losses := [] }

theorem u5754 : Upper (D 5) (R 5) [6,33,72,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5754
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5755 : Route 9 := (fun mask => (mask,id))

def c5755 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5755 : Upper (D 5) (R 5) [6,33,72,160,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,257] 13 (by decide) (choices 1) [2,4,8,16] r5755 c5755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2247
  · exact u2248
  · exact u2249
  · exact u2250

def r5756 : Route 9 := (fun mask => (mask,id))

def c5756 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5756 : Upper (D 5) (R 5) [6,33,72,160,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,258] 13 (by decide) (choices 1) [1,4,8,16] r5756 c5756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2251
  · exact u2252
  · exact u2253
  · exact u2254

def r5757 : Route 9 := (fun mask => (mask,id))

def c5757 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5757 : Upper (D 5) (R 5) [6,33,72,160,260] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,260] 13 (by decide) (choices 1) [1,2,8,16] r5757 c5757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2255
  · exact u2256
  · exact u2257
  · exact u2258

def r5758 : Route 9 := (fun mask => (mask,id))

def c5758 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5758 : Upper (D 5) (R 5) [6,33,72,160,264] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,264] 13 (by decide) (choices 1) [1,2,4,16] r5758 c5758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2259
  · exact u2260
  · exact u2261
  · exact u2262

def b5759 : PairBound 9 := { available := 60, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 392 19 60 124 188 316), lower := (rows 7 35 76 392 19 32 64 128 256), losses := [] }

theorem u5759 : Upper (D 5) (R 5) [6,33,72,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5759
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u5759
end Delivery.IrregularNine14.P05
