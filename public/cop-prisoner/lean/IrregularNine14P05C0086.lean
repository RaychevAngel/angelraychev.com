import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0031
import IrregularNine14P05C0032

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5160 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 140 26 289 353 417 289), lower := (rows 7 19 76 140 26 32 64 128 256), losses := [] }

theorem u5160 : Upper (D 5) (R 5) [6,17,72,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5160
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5161 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 140 49 298 362 426 298), lower := (rows 7 19 76 140 49 32 64 128 256), losses := [] }

theorem u5161 : Upper (D 5) (R 5) [6,17,72,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5161
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5162 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 76 140 50 297 361 425 297), lower := (rows 7 19 76 140 50 32 64 128 256), losses := [] }

theorem u5162 : Upper (D 5) (R 5) [6,17,72,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5162
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5163 : Route 9 := (fun mask => (mask,id))

def c5163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5163 : Upper (D 5) (R 5) [6,17,72,132,40] 13 := by
  apply FastRouting.sound _ _ [6,17,72,132,40] 13 (by decide) (choices 1) [1,2,256] r5163 c5163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1891
  · exact u1892
  · exact u1893

def b5164 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 140 273 42 106 170 298), lower := (rows 7 19 76 140 273 32 64 128 256), losses := [] }

theorem u5164 : Upper (D 5) (R 5) [6,17,72,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5164
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5165 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 76 140 274 41 105 169 297), lower := (rows 7 19 76 140 274 32 64 128 256), losses := [] }

theorem u5165 : Upper (D 5) (R 5) [6,17,72,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5165
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5166 : Route 9 := (fun mask => (mask,id))

def c5166 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5166 : Upper (D 5) (R 5) [6,17,72,132,264] 13 := by
  apply FastRouting.sound _ _ [6,17,72,132,264] 13 (by decide) (choices 1) [1,2] r5166 c5166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1894
  · exact u1895

def r5167 : Route 9 := (fun mask => (mask,id))

def c5167 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5167 : Upper (D 5) (R 5) [6,17,72,132,288] 13 := by
  apply FastRouting.sound _ _ [6,17,72,132,288] 13 (by decide) (choices 1) [1,2,8] r5167 c5167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1896
  · exact u1897
  · exact u1898

def b5168 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 18, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 168 19 300 364 428 300), lower := (rows 7 19 76 168 19 32 64 128 256), losses := [] }

theorem u5168 : Upper (D 5) (R 5) [6,17,72,160,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5168
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5169 : PairBound 9 := { available := 298, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 168 21 298 362 426 298), lower := (rows 7 19 76 168 21 32 64 128 256), losses := [] }

theorem u5169 : Upper (D 5) (R 5) [6,17,72,160,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5169
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5170 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 168 22 297 361 425 297), lower := (rows 7 19 76 168 22 32 64 128 256), losses := [] }

theorem u5170 : Upper (D 5) (R 5) [6,17,72,160,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5170
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5171 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 168 25 294 358 422 294), lower := (rows 7 19 76 168 25 32 64 128 256), losses := [] }

theorem u5171 : Upper (D 5) (R 5) [6,17,72,160,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5171
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5172 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 168 26 293 357 421 293), lower := (rows 7 19 76 168 26 32 64 128 256), losses := [] }

theorem u5172 : Upper (D 5) (R 5) [6,17,72,160,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5172
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5173 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 168 28 291 355 419 291), lower := (rows 7 19 76 168 28 32 64 128 256), losses := [] }

theorem u5173 : Upper (D 5) (R 5) [6,17,72,160,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5173
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5174 : PairBound 9 := { available := 270, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 168 49 302 334 398 270), lower := (rows 7 19 76 168 49 32 64 128 256), losses := [] }

theorem u5174 : Upper (D 5) (R 5) [6,17,72,160,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5174
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5175 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 76 168 50 301 333 397 269), lower := (rows 7 19 76 168 50 32 64 128 256), losses := [] }

theorem u5175 : Upper (D 5) (R 5) [6,17,72,160,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5175
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5176 : PairBound 9 := { available := 267, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 168 52 299 331 395 267), lower := (rows 7 19 76 168 52 32 64 128 256), losses := [] }

theorem u5176 : Upper (D 5) (R 5) [6,17,72,160,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5176
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5177 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 76 168 56 295 327 391 263), lower := (rows 7 19 76 168 56 32 64 128 256), losses := [] }

theorem u5177 : Upper (D 5) (R 5) [6,17,72,160,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5177
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5178 : PairBound 9 := { available := 46, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 168 273 46 110 174 302), lower := (rows 7 19 76 168 273 32 64 128 256), losses := [] }

theorem u5178 : Upper (D 5) (R 5) [6,17,72,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5178
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5179 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 76 168 274 45 109 173 301), lower := (rows 7 19 76 168 274 32 64 128 256), losses := [] }

theorem u5179 : Upper (D 5) (R 5) [6,17,72,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5179
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5180 : PairBound 9 := { available := 43, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 168 276 43 107 171 299), lower := (rows 7 19 76 168 276 32 64 128 256), losses := [] }

theorem u5180 : Upper (D 5) (R 5) [6,17,72,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5180
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5181 : Route 9 := (fun mask => (mask,id))

def c5181 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5181 : Upper (D 5) (R 5) [6,17,72,160,264] 13 := by
  apply FastRouting.sound _ _ [6,17,72,160,264] 13 (by decide) (choices 1) [1,2,4] r5181 c5181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1899
  · exact u1900
  · exact u1901

def r5182 : Route 9 := (fun mask => (mask,id))

def c5182 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5182 : Upper (D 5) (R 5) [6,17,72,160,288] 13 := by
  apply FastRouting.sound _ _ [6,17,72,160,288] 13 (by decide) (choices 1) [1,2,4,8] r5182 c5182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1902
  · exact u1903
  · exact u1904
  · exact u1905

def b5183 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 18, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 392 19 44 108 172 300), lower := (rows 7 19 76 392 19 32 64 128 256), losses := [] }

theorem u5183 : Upper (D 5) (R 5) [6,17,72,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5183
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5184 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 392 21 42 106 170 298), lower := (rows 7 19 76 392 21 32 64 128 256), losses := [] }

theorem u5184 : Upper (D 5) (R 5) [6,17,72,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5184
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5185 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 392 22 41 105 169 297), lower := (rows 7 19 76 392 22 32 64 128 256), losses := [] }

theorem u5185 : Upper (D 5) (R 5) [6,17,72,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5185
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5186 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 392 25 38 102 166 294), lower := (rows 7 19 76 392 25 32 64 128 256), losses := [] }

theorem u5186 : Upper (D 5) (R 5) [6,17,72,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5186
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5187 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 392 26 37 101 165 293), lower := (rows 7 19 76 392 26 32 64 128 256), losses := [] }

theorem u5187 : Upper (D 5) (R 5) [6,17,72,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5187
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5188 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 19 76 392 28 35 99 163 291), lower := (rows 7 19 76 392 28 32 64 128 256), losses := [] }

theorem u5188 : Upper (D 5) (R 5) [6,17,72,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5188
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5189 : PairBound 9 := { available := 46, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 76 392 49 46 110 174 302), lower := (rows 7 19 76 392 49 32 64 128 256), losses := [] }

theorem u5189 : Upper (D 5) (R 5) [6,17,72,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5189
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5190 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 76 392 50 45 109 173 301), lower := (rows 7 19 76 392 50 32 64 128 256), losses := [] }

theorem u5190 : Upper (D 5) (R 5) [6,17,72,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5190
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5191 : PairBound 9 := { available := 43, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 76 392 52 43 107 171 299), lower := (rows 7 19 76 392 52 32 64 128 256), losses := [] }

theorem u5191 : Upper (D 5) (R 5) [6,17,72,384,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5191
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5192 : Route 9 := (fun mask => (mask,id))

def c5192 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5192 : Upper (D 5) (R 5) [6,17,72,384,40] 13 := by
  apply FastRouting.sound _ _ [6,17,72,384,40] 13 (by decide) (choices 1) [1,2,4] r5192 c5192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1906
  · exact u1907
  · exact u1908

def b5193 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 41 22 424 456 392 392), lower := (rows 7 19 100 41 22 32 64 128 256), losses := [] }

theorem u5193 : Upper (D 5) (R 5) [6,17,96,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5193
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5194 : PairBound 9 := { available := 396, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 19 100 41 26 428 460 396 396), lower := (rows 7 19 100 41 26 32 64 128 256), losses := [] }

theorem u5194 : Upper (D 5) (R 5) [6,17,96,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5194
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5195 : PairBound 9 := { available := 394, camps := [{ cop := 4, region := 3, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 41 28 426 458 394 394), lower := (rows 7 19 100 41 28 32 64 128 256), losses := [] }

theorem u5195 : Upper (D 5) (R 5) [6,17,96,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5195
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5196 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 100 41 146 300 332 396 268), lower := (rows 7 19 100 41 146 32 64 128 256), losses := [] }

theorem u5196 : Upper (D 5) (R 5) [6,17,96,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5196
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5197 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 41 148 298 330 394 266), lower := (rows 7 19 100 41 148 32 64 128 256), losses := [] }

theorem u5197 : Upper (D 5) (R 5) [6,17,96,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5197
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5198 : Route 9 := (fun mask => (mask,id))

def c5198 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5198 : Upper (D 5) (R 5) [6,17,96,33,136] 13 := by
  apply FastRouting.sound _ _ [6,17,96,33,136] 13 (by decide) (choices 1) [2,4,8,256] r5198 c5198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1909
  · exact u1910
  · exact u1911
  · exact u1912

def r5199 : Route 9 := (fun mask => (mask,id))

def c5199 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5199 : Upper (D 5) (R 5) [6,17,96,33,384] 13 := by
  apply FastRouting.sound _ _ [6,17,96,33,384] 13 (by decide) (choices 1) [2,4,8] r5199 c5199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1913
  · exact u1914
  · exact u1915

def b5200 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 42 21 424 456 392 392), lower := (rows 7 19 100 42 21 32 64 128 256), losses := [] }

theorem u5200 : Upper (D 5) (R 5) [6,17,96,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5200
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5201 : PairBound 9 := { available := 396, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 100 42 25 428 460 396 396), lower := (rows 7 19 100 42 25 32 64 128 256), losses := [] }

theorem u5201 : Upper (D 5) (R 5) [6,17,96,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5201
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5202 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 3, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 42 28 425 457 393 393), lower := (rows 7 19 100 42 28 32 64 128 256), losses := [] }

theorem u5202 : Upper (D 5) (R 5) [6,17,96,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5202
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5203 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 100 42 145 300 332 396 268), lower := (rows 7 19 100 42 145 32 64 128 256), losses := [] }

theorem u5203 : Upper (D 5) (R 5) [6,17,96,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5203
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5204 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 42 148 297 329 393 265), lower := (rows 7 19 100 42 148 32 64 128 256), losses := [] }

theorem u5204 : Upper (D 5) (R 5) [6,17,96,34,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5204
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5205 : Route 9 := (fun mask => (mask,id))

def c5205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5205 : Upper (D 5) (R 5) [6,17,96,34,136] 13 := by
  apply FastRouting.sound _ _ [6,17,96,34,136] 13 (by decide) (choices 1) [1,4,8,256] r5205 c5205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1916
  · exact u1917
  · exact u1918
  · exact u1919

def r5206 : Route 9 := (fun mask => (mask,id))

def c5206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5206 : Upper (D 5) (R 5) [6,17,96,34,384] 13 := by
  apply FastRouting.sound _ _ [6,17,96,34,384] 13 (by decide) (choices 1) [1,4,8] r5206 c5206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1920
  · exact u1921
  · exact u1922

def b5207 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 137 22 296 360 424 296), lower := (rows 7 19 100 137 22 32 64 128 256), losses := [] }

theorem u5207 : Upper (D 5) (R 5) [6,17,96,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5207
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5208 : PairBound 9 := { available := 300, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 19 100 137 26 300 364 428 300), lower := (rows 7 19 100 137 26 32 64 128 256), losses := [] }

theorem u5208 : Upper (D 5) (R 5) [6,17,96,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5208
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5209 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 137 28 298 362 426 298), lower := (rows 7 19 100 137 28 32 64 128 256), losses := [] }

theorem u5209 : Upper (D 5) (R 5) [6,17,96,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5209
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5210 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 137 50 300 332 396 268), lower := (rows 7 19 100 137 50 32 64 128 256), losses := [] }

theorem u5210 : Upper (D 5) (R 5) [6,17,96,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5210
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5211 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 100 137 52 298 330 394 266), lower := (rows 7 19 100 137 52 32 64 128 256), losses := [] }

theorem u5211 : Upper (D 5) (R 5) [6,17,96,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5211
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5212 : Route 9 := (fun mask => (mask,id))

def c5212 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5212 : Upper (D 5) (R 5) [6,17,96,129,40] 13 := by
  apply FastRouting.sound _ _ [6,17,96,129,40] 13 (by decide) (choices 1) [2,4,8,256] r5212 c5212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1923
  · exact u1924
  · exact u1925
  · exact u1926

def b5213 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 19 100 137 274 44 108 172 300), lower := (rows 7 19 100 137 274 32 64 128 256), losses := [] }

theorem u5213 : Upper (D 5) (R 5) [6,17,96,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5213
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5214 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 137 276 42 106 170 298), lower := (rows 7 19 100 137 276 32 64 128 256), losses := [] }

theorem u5214 : Upper (D 5) (R 5) [6,17,96,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5214
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5215 : Route 9 := (fun mask => (mask,id))

def c5215 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5215 : Upper (D 5) (R 5) [6,17,96,129,264] 13 := by
  apply FastRouting.sound _ _ [6,17,96,129,264] 13 (by decide) (choices 1) [2,4,8] r5215 c5215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1927
  · exact u1928
  · exact u1929

def r5216 : Route 9 := (fun mask => (mask,id))

def c5216 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5216 : Upper (D 5) (R 5) [6,17,96,129,288] 13 := by
  apply FastRouting.sound _ _ [6,17,96,129,288] 13 (by decide) (choices 1) [2,4,8] r5216 c5216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1930
  · exact u1931
  · exact u1932

def b5217 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 19, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 138 21 296 360 424 296), lower := (rows 7 19 100 138 21 32 64 128 256), losses := [] }

theorem u5217 : Upper (D 5) (R 5) [6,17,96,130,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5217
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5218 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 2, targets := 12 }], pairs := [(1,2),(1,3)], upper := (rows 7 19 100 138 25 300 364 428 300), lower := (rows 7 19 100 138 25 32 64 128 256), losses := [] }

theorem u5218 : Upper (D 5) (R 5) [6,17,96,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5218
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5219 : PairBound 9 := { available := 297, camps := [{ cop := 4, region := 3, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 19 100 138 28 297 361 425 297), lower := (rows 7 19 100 138 28 32 64 128 256), losses := [] }

theorem u5219 : Upper (D 5) (R 5) [6,17,96,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5219
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u5219
end Delivery.IrregularNine14.P05
