import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0031
import IrregularNine14P09C0032

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5220 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 2, region := 195, targets := 256 }], pairs := [(0,8),(1,8),(2,7),(3,7)], upper := (rows 35 194 44 328 400 48 69 133 261), lower := (rows 35 194 44 328 400 48 64 128 256), losses := [] }

theorem u5220 : Upper (D 9) (R 9) [34,192,40,320,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5220 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5221 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 45, targets := 256 },{ cop := 0, region := 340, targets := 128 }], pairs := [(0,8),(2,7),(2,8),(3,8)], upper := (rows 35 194 69 137 276 40 368 432 304), lower := (rows 35 194 69 137 276 40 64 128 256), losses := [] }

theorem u5221 : Upper (D 9) (R 9) [34,192,65,129,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5221 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5222 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 440, targets := 64 },{ cop := 3, region := 372, targets := 128 }], pairs := [(2,7),(3,6),(4,6),(4,7)], upper := (rows 35 194 69 137 276 48 360 424 296), lower := (rows 35 194 69 137 276 48 64 128 256), losses := [] }

theorem u5222 : Upper (D 9) (R 9) [34,192,65,129,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5222 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5223 : Route 9 := (fun mask => (mask,id))

def c5223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5223 : Upper (D 9) (R 9) [34,192,65,129,260,256] 13 := by
  apply FastRouting.sound _ _ [34,192,65,129,260,256] 13 (by decide) (choices 1) [8,16,32] r5223 c5223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1894
  · exact u1895
  · exact u1896

def b5224 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 45, targets := 256 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,8),(2,8),(3,6),(3,8)], upper := (rows 35 194 69 137 304 36 344 408 280), lower := (rows 35 194 69 137 304 36 64 128 256), losses := [] }

theorem u5224 : Upper (D 9) (R 9) [34,192,65,129,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5224 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5225 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 194 69 137 304 48 332 396 268), lower := (rows 35 194 69 137 304 48 64 128 256), losses := [] }

theorem u5225 : Upper (D 9) (R 9) [34,192,65,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5225 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5226 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 194 69 137 304 288 92 156 284), lower := (rows 35 194 69 137 304 288 64 128 256), losses := [] }

theorem u5226 : Upper (D 9) (R 9) [34,192,65,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5226 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5227 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 45, targets := 256 },{ cop := 0, region := 340, targets := 128 }], pairs := [(0,8),(2,7),(2,8),(3,8)], upper := (rows 35 194 69 140 273 40 368 432 304), lower := (rows 35 194 69 140 273 40 64 128 256), losses := [] }

theorem u5227 : Upper (D 9) (R 9) [34,192,65,132,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5227 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5228 : Route 9 := (fun mask => (mask,id))

def c5228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u5228 : Upper (D 9) (R 9) [34,192,65,132,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,65,132,257,16] 13 (by decide) (choices 1) [8,32,256] r5228 c5228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1897
  · exact u1898
  · exact u1899

def r5229 : Route 9 := (fun mask => (mask,id))

def c5229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5229 : Upper (D 9) (R 9) [34,192,65,132,257,256] 13 := by
  apply FastRouting.sound _ _ [34,192,65,132,257,256] 13 (by decide) (choices 1) [8,16,32] r5229 c5229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1900
  · exact u1901
  · exact u1902

def b5230 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 45, targets := 256 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,8)], upper := (rows 35 194 69 140 280 33 368 432 304), lower := (rows 35 194 69 140 280 33 64 128 256), losses := [] }

theorem u5230 : Upper (D 9) (R 9) [34,192,65,132,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5230 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5231 : Route 9 := (fun mask => (mask,id))

def c5231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u5231 : Upper (D 9) (R 9) [34,192,65,132,264,16] 13 := by
  apply FastRouting.sound _ _ [34,192,65,132,264,16] 13 (by decide) (choices 1) [1,32,256] r5231 c5231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1903
  · exact u1904
  · exact u1905

def r5232 : Route 9 := (fun mask => (mask,id))

def c5232 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5232 : Upper (D 9) (R 9) [34,192,65,132,264,256] 13 := by
  apply FastRouting.sound _ _ [34,192,65,132,264,256] 13 (by decide) (choices 1) [1,16,32] r5232 c5232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1906
  · exact u1907
  · exact u1908

def b5233 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 45, targets := 256 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,8)], upper := (rows 35 194 69 140 304 33 344 408 280), lower := (rows 35 194 69 140 304 33 64 128 256), losses := [] }

theorem u5233 : Upper (D 9) (R 9) [34,192,65,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5233 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5234 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 45, targets := 256 },{ cop := 0, region := 340, targets := 128 }], pairs := [(0,8),(2,7),(2,8),(3,8)], upper := (rows 35 194 69 140 304 40 337 401 273), lower := (rows 35 194 69 140 304 40 64 128 256), losses := [] }

theorem u5234 : Upper (D 9) (R 9) [34,192,65,132,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5234 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5235 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 194 69 140 304 48 329 393 265), lower := (rows 35 194 69 140 304 48 64 128 256), losses := [] }

theorem u5235 : Upper (D 9) (R 9) [34,192,65,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5235 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5236 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 194 69 140 304 288 89 153 281), lower := (rows 35 194 69 140 304 288 64 128 256), losses := [] }

theorem u5236 : Upper (D 9) (R 9) [34,192,65,132,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5236 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5237 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 37, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8)], upper := (rows 35 194 69 152 273 36 360 424 296), lower := (rows 35 194 69 152 273 36 64 128 256), losses := [] }

theorem u5237 : Upper (D 9) (R 9) [34,192,65,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5237 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5238 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 2, region := 440, targets := 64 }], pairs := [(2,7),(3,6),(4,6),(4,7)], upper := (rows 35 194 69 152 273 40 356 420 292), lower := (rows 35 194 69 152 273 40 64 128 256), losses := [] }

theorem u5238 : Upper (D 9) (R 9) [34,192,65,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5238 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5239 : Route 9 := (fun mask => (mask,id))

def c5239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5239 : Upper (D 9) (R 9) [34,192,65,144,257,256] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,257,256] 13 (by decide) (choices 1) [4,8,32] r5239 c5239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1909
  · exact u1910
  · exact u1911

def b5240 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 37, targets := 384 },{ cop := 2, region := 440, targets := 64 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,6)], upper := (rows 35 194 69 152 276 33 360 424 296), lower := (rows 35 194 69 152 276 33 64 128 256), losses := [] }

theorem u5240 : Upper (D 9) (R 9) [34,192,65,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5240 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5241 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 2, region := 440, targets := 64 }], pairs := [(2,7),(3,6),(4,6),(4,7)], upper := (rows 35 194 69 152 276 40 353 417 289), lower := (rows 35 194 69 152 276 40 64 128 256), losses := [] }

theorem u5241 : Upper (D 9) (R 9) [34,192,65,144,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5241 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5242 : Route 9 := (fun mask => (mask,id))

def c5242 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5242 : Upper (D 9) (R 9) [34,192,65,144,260,256] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,260,256] 13 (by decide) (choices 1) [1,8,32] r5242 c5242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1912
  · exact u1913
  · exact u1914

def b5243 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 1, region := 37, targets := 256 },{ cop := 2, region := 440, targets := 64 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,6)], upper := (rows 35 194 69 152 280 33 356 420 292), lower := (rows 35 194 69 152 280 33 64 128 256), losses := [] }

theorem u5243 : Upper (D 9) (R 9) [34,192,65,144,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5243 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5244 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(3,6),(4,6)], upper := (rows 35 194 69 152 280 36 353 417 289), lower := (rows 35 194 69 152 280 36 64 128 256), losses := [] }

theorem u5244 : Upper (D 9) (R 9) [34,192,65,144,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5244 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5245 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 1, region := 293, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,7),(2,8)], upper := (rows 35 194 69 152 280 288 101 165 293), lower := (rows 35 194 69 152 280 288 64 128 256), losses := [] }

theorem u5245 : Upper (D 9) (R 9) [34,192,65,144,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5245 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5246 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 37, targets := 384 },{ cop := 2, region := 440, targets := 64 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,6)], upper := (rows 35 194 69 152 304 33 332 396 268), lower := (rows 35 194 69 152 304 33 64 128 256), losses := [] }

theorem u5246 : Upper (D 9) (R 9) [34,192,65,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5246 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5247 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 37, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8)], upper := (rows 35 194 69 152 304 36 329 393 265), lower := (rows 35 194 69 152 304 36 64 128 256), losses := [] }

theorem u5247 : Upper (D 9) (R 9) [34,192,65,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5247 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5248 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 340, targets := 128 }], pairs := [(1,5),(2,5),(2,7),(4,7)], upper := (rows 35 194 69 152 304 40 325 389 261), lower := (rows 35 194 69 152 304 40 64 128 256), losses := [] }

theorem u5248 : Upper (D 9) (R 9) [34,192,65,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5248 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5249 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 194 69 152 304 288 77 141 269), lower := (rows 35 194 69 152 304 288 64 128 256), losses := [] }

theorem u5249 : Upper (D 9) (R 9) [34,192,65,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5249 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5250 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 45, targets := 256 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,8),(2,8),(3,6),(3,8)], upper := (rows 35 194 69 168 273 36 344 408 280), lower := (rows 35 194 69 168 273 36 64 128 256), losses := [] }

theorem u5250 : Upper (D 9) (R 9) [34,192,65,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5250 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5251 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 1, region := 41, targets := 256 }], pairs := [(0,8),(1,5),(2,5),(4,5)], upper := (rows 35 194 69 168 273 40 340 404 276), lower := (rows 35 194 69 168 273 40 64 128 256), losses := [] }

theorem u5251 : Upper (D 9) (R 9) [34,192,65,160,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5251 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5252 : Route 9 := (fun mask => (mask,id))

def c5252 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5252 : Upper (D 9) (R 9) [34,192,65,160,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,65,160,257,16] 13 (by decide) (choices 1) [4,8,256] r5252 c5252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1915
  · exact u1916
  · exact u1917

def r5253 : Route 9 := (fun mask => (mask,id))

def c5253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5253 : Upper (D 9) (R 9) [34,192,65,160,257,256] 13 := by
  apply FastRouting.sound _ _ [34,192,65,160,257,256] 13 (by decide) (choices 1) [4,8,16] r5253 c5253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1918
  · exact u1919
  · exact u1920

def b5254 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 45, targets := 256 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(0,8),(2,8),(3,6),(3,8)], upper := (rows 35 194 69 168 276 33 344 408 280), lower := (rows 35 194 69 168 276 33 64 128 256), losses := [] }

theorem u5254 : Upper (D 9) (R 9) [34,192,65,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5254 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5255 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 1, region := 41, targets := 256 }], pairs := [(0,8),(1,5),(2,5),(4,5)], upper := (rows 35 194 69 168 276 40 337 401 273), lower := (rows 35 194 69 168 276 40 64 128 256), losses := [] }

theorem u5255 : Upper (D 9) (R 9) [34,192,65,160,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5255 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5256 : Route 9 := (fun mask => (mask,id))

def c5256 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5256 : Upper (D 9) (R 9) [34,192,65,160,260,16] 13 := by
  apply FastRouting.sound _ _ [34,192,65,160,260,16] 13 (by decide) (choices 1) [1,8,256] r5256 c5256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1921
  · exact u1922
  · exact u1923

def r5257 : Route 9 := (fun mask => (mask,id))

def c5257 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5257 : Upper (D 9) (R 9) [34,192,65,160,260,256] 13 := by
  apply FastRouting.sound _ _ [34,192,65,160,260,256] 13 (by decide) (choices 1) [1,8,16] r5257 c5257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1924
  · exact u1925
  · exact u1926

def b5258 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 45, targets := 256 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(0,8),(2,8),(3,6),(3,8)], upper := (rows 35 194 69 168 280 33 340 404 276), lower := (rows 35 194 69 168 280 33 64 128 256), losses := [] }

theorem u5258 : Upper (D 9) (R 9) [34,192,65,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5258 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5259 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 45, targets := 256 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,8),(2,8),(3,6),(3,8)], upper := (rows 35 194 69 168 280 36 337 401 273), lower := (rows 35 194 69 168 280 36 64 128 256), losses := [] }

theorem u5259 : Upper (D 9) (R 9) [34,192,65,160,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5259 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5260 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 440, targets := 64 }], pairs := [(1,5),(2,5),(3,6),(4,6)], upper := (rows 35 194 69 168 280 48 325 389 261), lower := (rows 35 194 69 168 280 48 64 128 256), losses := [] }

theorem u5260 : Upper (D 9) (R 9) [34,192,65,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5260 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5261 : Route 9 := (fun mask => (mask,id))

def c5261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5261 : Upper (D 9) (R 9) [34,192,65,160,264,256] 13 := by
  apply FastRouting.sound _ _ [34,192,65,160,264,256] 13 (by decide) (choices 1) [1,4,16] r5261 c5261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1927
  · exact u1928
  · exact u1929

def r5262 : Route 9 := (fun mask => (mask,id))

def c5262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5262 : Upper (D 9) (R 9) [34,192,65,257,260,8] 13 := by
  apply FastRouting.sound _ _ [34,192,65,257,260,8] 13 (by decide) (choices 1) [16,32,128] r5262 c5262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1930
  · exact u1931
  · exact u1932

def r5263 : Route 9 := (fun mask => (mask,id))

def c5263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5263 : Upper (D 9) (R 9) [34,192,65,257,260,16] 13 := by
  apply FastRouting.sound _ _ [34,192,65,257,260,16] 13 (by decide) (choices 1) [8,32,128] r5263 c5263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1933
  · exact u1934
  · exact u1935

def b5264 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 37, targets := 256 }], pairs := [(0,8),(2,7),(2,8),(3,7),(4,7)], upper := (rows 35 194 69 265 276 160 120 184 312), lower := (rows 35 194 69 265 276 160 64 128 256), losses := [] }

theorem u5264 : Upper (D 9) (R 9) [34,192,65,257,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5264 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5265 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 37, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8)], upper := (rows 35 194 69 265 304 36 216 152 408), lower := (rows 35 194 69 265 304 36 64 128 256), losses := [] }

theorem u5265 : Upper (D 9) (R 9) [34,192,65,257,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5265 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5266 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 48, targets := 193 },{ cop := 4, region := 199, targets := 256 }], pairs := [(0,8),(4,0),(4,6),(4,7)], upper := (rows 35 194 69 265 304 40 212 148 404), lower := (rows 35 194 69 265 304 40 64 128 256), losses := [] }

theorem u5266 : Upper (D 9) (R 9) [34,192,65,257,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5266 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5267 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 194 69 265 304 48 204 140 396), lower := (rows 35 194 69 265 304 48 64 128 256), losses := [] }

theorem u5267 : Upper (D 9) (R 9) [34,192,65,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5267 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5268 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 37, targets := 256 }], pairs := [(0,8),(2,7),(2,8),(3,7),(4,7)], upper := (rows 35 194 69 265 304 160 92 156 284), lower := (rows 35 194 69 265 304 160 64 128 256), losses := [] }

theorem u5268 : Upper (D 9) (R 9) [34,192,65,257,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5268 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5269 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 37, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8)], upper := (rows 35 194 69 265 400 36 120 184 312), lower := (rows 35 194 69 265 400 36 64 128 256), losses := [] }

theorem u5269 : Upper (D 9) (R 9) [34,192,65,257,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5269 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5270 : Route 9 := (fun mask => (mask,id))

def c5270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5270 : Upper (D 9) (R 9) [34,192,65,257,384,8] 13 := by
  apply FastRouting.sound _ _ [34,192,65,257,384,8] 13 (by decide) (choices 1) [4,16,32] r5270 c5270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1936
  · exact u1937
  · exact u1938

def b5271 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 2, region := 440, targets := 64 }], pairs := [(2,7),(3,6),(3,7),(4,6)], upper := (rows 35 194 69 265 400 48 108 172 300), lower := (rows 35 194 69 265 400 48 64 128 256), losses := [] }

theorem u5271 : Upper (D 9) (R 9) [34,192,65,257,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5271 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5272 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 37, targets := 384 },{ cop := 2, region := 440, targets := 64 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,6)], upper := (rows 35 194 69 268 304 33 216 152 408), lower := (rows 35 194 69 268 304 33 64 128 256), losses := [] }

theorem u5272 : Upper (D 9) (R 9) [34,192,65,260,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5272 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5273 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 48, targets := 193 },{ cop := 4, region := 195, targets := 256 }], pairs := [(0,8),(4,0),(4,6),(4,7)], upper := (rows 35 194 69 268 304 40 209 145 401), lower := (rows 35 194 69 268 304 40 64 128 256), losses := [] }

theorem u5273 : Upper (D 9) (R 9) [34,192,65,260,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5273 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5274 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 194 69 268 304 48 201 137 393), lower := (rows 35 194 69 268 304 48 64 128 256), losses := [] }

theorem u5274 : Upper (D 9) (R 9) [34,192,65,260,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5274 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5275 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 37, targets := 256 }], pairs := [(0,8),(2,7),(2,8),(3,7),(4,7)], upper := (rows 35 194 69 268 304 160 89 153 281), lower := (rows 35 194 69 268 304 160 64 128 256), losses := [] }

theorem u5275 : Upper (D 9) (R 9) [34,192,65,260,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5275 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5276 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 37, targets := 384 },{ cop := 2, region := 440, targets := 64 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,6)], upper := (rows 35 194 69 268 400 33 120 184 312), lower := (rows 35 194 69 268 400 33 64 128 256), losses := [] }

theorem u5276 : Upper (D 9) (R 9) [34,192,65,260,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5276 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5277 : Route 9 := (fun mask => (mask,id))

def c5277 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5277 : Upper (D 9) (R 9) [34,192,65,260,384,8] 13 := by
  apply FastRouting.sound _ _ [34,192,65,260,384,8] 13 (by decide) (choices 1) [1,16,32] r5277 c5277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1939
  · exact u1940
  · exact u1941

def b5278 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 2, region := 440, targets := 64 }], pairs := [(2,7),(3,6),(3,7),(4,6)], upper := (rows 35 194 69 268 400 48 105 169 297), lower := (rows 35 194 69 268 400 48 64 128 256), losses := [] }

theorem u5278 : Upper (D 9) (R 9) [34,192,65,260,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5278 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5279 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 37, targets := 384 },{ cop := 2, region := 440, targets := 64 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,6)], upper := (rows 35 194 69 296 400 33 92 156 284), lower := (rows 35 194 69 296 400 33 64 128 256), losses := [] }

theorem u5279 : Upper (D 9) (R 9) [34,192,65,288,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5279 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u5279
end Delivery.IrregularNine14.P09
