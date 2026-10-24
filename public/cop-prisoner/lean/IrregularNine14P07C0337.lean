import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0093

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20220 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 88 304 34 197 133 389), lower := (rows 35 194 13 88 304 34 64 128 256), losses := [] }

theorem u20220 : Upper (D 7) (R 7) [34,192,9,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20221 : Route 9 := (fun mask => (mask,id))

def c20221 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20221 : Upper (D 7) (R 7) [34,192,9,80,288,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,288,4] 13 (by decide) (choices 1) [1,2,128] r20221 c20221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5593
  · exact u5594
  · exact u5595

def b20222 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 88 304 160 71 135 263), lower := (rows 35 194 13 88 304 160 64 128 256), losses := [] }

theorem u20222 : Upper (D 7) (R 7) [34,192,9,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20223 : Route 9 := (fun mask => (mask,id))

def c20223 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20223 : Upper (D 7) (R 7) [34,192,9,80,384,1] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,384,1] 13 (by decide) (choices 1) [2,4,32] r20223 c20223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5596
  · exact u5597
  · exact u5598

def b20224 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 88 400 34 101 165 293), lower := (rows 35 194 13 88 400 34 64 128 256), losses := [] }

theorem u20224 : Upper (D 7) (R 7) [34,192,9,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20225 : Route 9 := (fun mask => (mask,id))

def c20225 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20225 : Upper (D 7) (R 7) [34,192,9,80,384,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,384,4] 13 (by decide) (choices 1) [1,2,32] r20225 c20225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5599
  · exact u5600
  · exact u5601

def b20226 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 104 22 33 464 400 400), lower := (rows 35 194 13 104 22 33 64 128 256), losses := [] }

theorem u20226 : Upper (D 7) (R 7) [34,192,9,96,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20227 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 104 22 48 449 385 385), lower := (rows 35 194 13 104 22 48 64 128 256), losses := [] }

theorem u20227 : Upper (D 7) (R 7) [34,192,9,96,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20227 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20228 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 104 22 160 337 401 273), lower := (rows 35 194 13 104 22 160 64 128 256), losses := [] }

theorem u20228 : Upper (D 7) (R 7) [34,192,9,96,6,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20229 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(4,5)], upper := (rows 35 194 13 104 22 288 209 145 401), lower := (rows 35 194 13 104 22 288 64 128 256), losses := [] }

theorem u20229 : Upper (D 7) (R 7) [34,192,9,96,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20229 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20230 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 104 145 34 340 404 276), lower := (rows 35 194 13 104 145 34 64 128 256), losses := [] }

theorem u20230 : Upper (D 7) (R 7) [34,192,9,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20231 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 104 145 36 338 402 274), lower := (rows 35 194 13 104 145 36 64 128 256), losses := [] }

theorem u20231 : Upper (D 7) (R 7) [34,192,9,96,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20231 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20232 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 13 104 145 48 326 390 262), lower := (rows 35 194 13 104 145 48 64 128 256), losses := [] }

theorem u20232 : Upper (D 7) (R 7) [34,192,9,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20232 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20233 : Route 9 := (fun mask => (mask,id))

def c20233 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20233 : Upper (D 7) (R 7) [34,192,9,96,129,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,129,256] 13 (by decide) (choices 1) [2,4,16] r20233 c20233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5602
  · exact u5603
  · exact u5604

def b20234 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 104 148 33 338 402 274), lower := (rows 35 194 13 104 148 33 64 128 256), losses := [] }

theorem u20234 : Upper (D 7) (R 7) [34,192,9,96,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20235 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 104 148 34 337 401 273), lower := (rows 35 194 13 104 148 34 64 128 256), losses := [] }

theorem u20235 : Upper (D 7) (R 7) [34,192,9,96,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20236 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,7),(3,7)], upper := (rows 35 194 13 104 148 48 323 387 259), lower := (rows 35 194 13 104 148 48 64 128 256), losses := [] }

theorem u20236 : Upper (D 7) (R 7) [34,192,9,96,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20236 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20237 : Route 9 := (fun mask => (mask,id))

def c20237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20237 : Upper (D 7) (R 7) [34,192,9,96,132,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96,132,256] 13 (by decide) (choices 1) [1,2,16] r20237 c20237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5605
  · exact u5606
  · exact u5607

def b20238 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 104 273 34 212 148 404), lower := (rows 35 194 13 104 273 34 64 128 256), losses := [] }

theorem u20238 : Upper (D 7) (R 7) [34,192,9,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20239 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 104 273 36 210 146 402), lower := (rows 35 194 13 104 273 36 64 128 256), losses := [] }

theorem u20239 : Upper (D 7) (R 7) [34,192,9,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20239 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20240 : PairBound 9 := { available := 134, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 35 194 13 104 273 48 198 134 390), lower := (rows 35 194 13 104 273 48 64 128 256), losses := [] }

theorem u20240 : Upper (D 7) (R 7) [34,192,9,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20240 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20241 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 104 273 160 86 150 278), lower := (rows 35 194 13 104 273 160 64 128 256), losses := [] }

theorem u20241 : Upper (D 7) (R 7) [34,192,9,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20242 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 104 274 33 212 148 404), lower := (rows 35 194 13 104 274 33 64 128 256), losses := [] }

theorem u20242 : Upper (D 7) (R 7) [34,192,9,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20243 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 104 274 36 209 145 401), lower := (rows 35 194 13 104 274 36 64 128 256), losses := [] }

theorem u20243 : Upper (D 7) (R 7) [34,192,9,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20243 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20244 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 35 194 13 104 274 48 197 133 389), lower := (rows 35 194 13 104 274 48 64 128 256), losses := [] }

theorem u20244 : Upper (D 7) (R 7) [34,192,9,96,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20244 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20245 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 104 274 160 85 149 277), lower := (rows 35 194 13 104 274 160 64 128 256), losses := [] }

theorem u20245 : Upper (D 7) (R 7) [34,192,9,96,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20246 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 104 276 33 210 146 402), lower := (rows 35 194 13 104 276 33 64 128 256), losses := [] }

theorem u20246 : Upper (D 7) (R 7) [34,192,9,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20246 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20247 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 104 276 34 209 145 401), lower := (rows 35 194 13 104 276 34 64 128 256), losses := [] }

theorem u20247 : Upper (D 7) (R 7) [34,192,9,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20248 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(4,5),(4,6)], upper := (rows 35 194 13 104 276 48 195 131 387), lower := (rows 35 194 13 104 276 48 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 20 52 0 129 257), good := (rows 419 130 445 40 308 48 0 128 256) }] }

theorem u20248 : Upper (D 7) (R 7) [34,192,9,96,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20248 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20249 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 104 276 160 83 147 275), lower := (rows 35 194 13 104 276 160 64 128 256), losses := [] }

theorem u20249 : Upper (D 7) (R 7) [34,192,9,96,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20250 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 104 400 33 86 150 278), lower := (rows 35 194 13 104 400 33 64 128 256), losses := [] }

theorem u20250 : Upper (D 7) (R 7) [34,192,9,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20251 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 104 400 34 85 149 277), lower := (rows 35 194 13 104 400 34 64 128 256), losses := [] }

theorem u20251 : Upper (D 7) (R 7) [34,192,9,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20252 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 45, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 104 400 36 83 147 275), lower := (rows 35 194 13 104 400 36 64 128 256), losses := [] }

theorem u20252 : Upper (D 7) (R 7) [34,192,9,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20252 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20253 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,7),(3,7)], upper := (rows 35 194 13 104 400 48 71 135 263), lower := (rows 35 194 13 104 400 48 64 128 256), losses := [] }

theorem u20253 : Upper (D 7) (R 7) [34,192,9,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20253 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20254 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 13 266 52 33 208 208 464), lower := (rows 35 194 13 266 52 33 64 128 256), losses := [] }

theorem u20254 : Upper (D 7) (R 7) [34,192,9,258,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20255 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 194 13 266 52 48 193 193 449), lower := (rows 35 194 13 266 52 48 64 128 256), losses := [] }

theorem u20255 : Upper (D 7) (R 7) [34,192,9,258,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20255 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20256 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 266 52 96 209 145 401), lower := (rows 35 194 13 266 52 96 64 128 256), losses := [] }

theorem u20256 : Upper (D 7) (R 7) [34,192,9,258,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20257 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 194 13 266 81 36 240 176 432), lower := (rows 35 194 13 266 81 36 64 128 256), losses := [] }

theorem u20257 : Upper (D 7) (R 7) [34,192,9,258,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20257 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20258 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 194 13 266 81 48 228 164 420), lower := (rows 35 194 13 266 81 48 64 128 256), losses := [] }

theorem u20258 : Upper (D 7) (R 7) [34,192,9,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20258 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20259 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 266 81 160 116 180 308), lower := (rows 35 194 13 266 81 160 64 128 256), losses := [] }

theorem u20259 : Upper (D 7) (R 7) [34,192,9,258,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20260 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 13 266 84 33 240 176 432), lower := (rows 35 194 13 266 84 33 64 128 256), losses := [] }

theorem u20260 : Upper (D 7) (R 7) [34,192,9,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20261 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 240, targets := 2 }], pairs := [(2,6),(3,6),(4,1)], upper := (rows 35 194 13 266 84 48 225 161 417), lower := (rows 35 194 13 266 84 48 64 128 256), losses := [] }

theorem u20261 : Upper (D 7) (R 7) [34,192,9,258,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20261 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20262 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 266 84 160 113 177 305), lower := (rows 35 194 13 266 84 160 64 128 256), losses := [] }

theorem u20262 : Upper (D 7) (R 7) [34,192,9,258,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20263 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 13 266 112 33 212 148 404), lower := (rows 35 194 13 266 112 33 64 128 256), losses := [] }

theorem u20263 : Upper (D 7) (R 7) [34,192,9,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20264 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 194 13 266 112 36 209 145 401), lower := (rows 35 194 13 266 112 36 64 128 256), losses := [] }

theorem u20264 : Upper (D 7) (R 7) [34,192,9,258,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20264 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20265 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 13 266 112 48 197 133 389), lower := (rows 35 194 13 266 112 48 64 128 256), losses := [] }

theorem u20265 : Upper (D 7) (R 7) [34,192,9,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20265 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20266 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(2,7),(3,7),(4,0),(4,7)], upper := (rows 35 194 13 266 112 160 85 149 277), lower := (rows 35 194 13 266 112 160 64 128 256), losses := [] }

theorem u20266 : Upper (D 7) (R 7) [34,192,9,258,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20267 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 268 81 34 240 176 432), lower := (rows 35 194 13 268 81 34 64 128 256), losses := [] }

theorem u20267 : Upper (D 7) (R 7) [34,192,9,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20268 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 194 13 268 81 48 226 162 418), lower := (rows 35 194 13 268 81 48 64 128 256), losses := [] }

theorem u20268 : Upper (D 7) (R 7) [34,192,9,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20268 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20269 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 268 81 160 114 178 306), lower := (rows 35 194 13 268 81 160 64 128 256), losses := [] }

theorem u20269 : Upper (D 7) (R 7) [34,192,9,260,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20270 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 210, targets := 1 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(1,0),(4,0),(4,7)], upper := (rows 35 194 13 268 112 33 210 146 402), lower := (rows 35 194 13 268 112 33 64 128 256), losses := [] }

theorem u20270 : Upper (D 7) (R 7) [34,192,9,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20271 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 268 112 34 209 145 401), lower := (rows 35 194 13 268 112 34 64 128 256), losses := [] }

theorem u20271 : Upper (D 7) (R 7) [34,192,9,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20272 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 13 268 112 48 195 131 387), lower := (rows 35 194 13 268 112 48 64 128 256), losses := [] }

theorem u20272 : Upper (D 7) (R 7) [34,192,9,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20272 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20273 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(2,7),(3,7),(4,0),(4,7)], upper := (rows 35 194 13 268 112 160 83 147 275), lower := (rows 35 194 13 268 112 160 64 128 256), losses := [] }

theorem u20273 : Upper (D 7) (R 7) [34,192,9,260,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20274 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,6),(0,7),(1,0),(3,0)], upper := (rows 35 194 13 280 22 33 224 224 480), lower := (rows 35 194 13 280 22 33 64 128 256), losses := [{ target := 0, region := (rows 0 39 4 12 20 32 97 161 289), good := (rows 482 194 478 280 30 482 64 128 256) }] }

theorem u20274 : Upper (D 7) (R 7) [34,192,9,272,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20275 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 280 22 96 225 161 417), lower := (rows 35 194 13 280 22 96 64 128 256), losses := [] }

theorem u20275 : Upper (D 7) (R 7) [34,192,9,272,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20276 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 280 52 33 194 194 450), lower := (rows 35 194 13 280 52 33 64 128 256), losses := [] }

theorem u20276 : Upper (D 7) (R 7) [34,192,9,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20277 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 280 52 34 193 193 449), lower := (rows 35 194 13 280 52 34 64 128 256), losses := [] }

theorem u20277 : Upper (D 7) (R 7) [34,192,9,272,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20278 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 280 52 96 195 131 387), lower := (rows 35 194 13 280 52 96 64 128 256), losses := [] }

theorem u20278 : Upper (D 7) (R 7) [34,192,9,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20279 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 280 81 34 228 164 420), lower := (rows 35 194 13 280 81 34 64 128 256), losses := [] }

theorem u20279 : Upper (D 7) (R 7) [34,192,9,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u20279
end Delivery.IrregularNine14.P07
