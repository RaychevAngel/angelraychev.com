import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0032
import IrregularNine14P09C0033

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5280 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 37, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8)], upper := (rows 35 194 69 296 400 36 89 153 281), lower := (rows 35 194 69 296 400 36 64 128 256), losses := [] }

theorem u5280 : Upper (D 9) (R 9) [34,192,65,288,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5280 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5281 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 35 194 69 296 400 40 85 149 277), lower := (rows 35 194 69 296 400 40 64 128 256), losses := [] }

theorem u5281 : Upper (D 9) (R 9) [34,192,65,288,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5281 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5282 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 194 69 296 400 48 77 141 269), lower := (rows 35 194 69 296 400 48 64 128 256), losses := [] }

theorem u5282 : Upper (D 9) (R 9) [34,192,65,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5282 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5283 : Route 9 := (fun mask => (mask,id))

def c5283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u5283 : Upper (D 9) (R 9) [34,192,72,144,257,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,257,1] 13 (by decide) (choices 1) [4,32,256] r5283 c5283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1942
  · exact u1943
  · exact u1944

def r5284 : Route 9 := (fun mask => (mask,id))

def c5284 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u5284 : Upper (D 9) (R 9) [34,192,72,144,257,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,257,4] 13 (by decide) (choices 1) [1,32,256] r5284 c5284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1945
  · exact u1946
  · exact u1947

def r5285 : Route 9 := (fun mask => (mask,id))

def c5285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5285 : Upper (D 9) (R 9) [34,192,72,144,257,256] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,257,256] 13 (by decide) (choices 1) [1,4,32] r5285 c5285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1948
  · exact u1949
  · exact u1950

def r5286 : Route 9 := (fun mask => (mask,id))

def c5286 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u5286 : Upper (D 9) (R 9) [34,192,72,144,260,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,260,1] 13 (by decide) (choices 1) [1,32,256] r5286 c5286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1951
  · exact u1952
  · exact u1953

def r5287 : Route 9 := (fun mask => (mask,id))

def c5287 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5287 : Upper (D 9) (R 9) [34,192,72,144,260,256] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,260,256] 13 (by decide) (choices 1) [1,32] r5287 c5287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1954
  · exact u1955

def r5288 : Route 9 := (fun mask => (mask,id))

def c5288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5288 : Upper (D 9) (R 9) [34,192,72,144,288,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,288,1] 13 (by decide) (choices 1) [1,4,256] r5288 c5288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1956
  · exact u1957
  · exact u1958

def b5289 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 0, region := 450, targets := 32 },{ cop := 0, region := 272, targets := 128 }], pairs := [(1,5),(3,6),(4,6),(4,7)], upper := (rows 35 194 76 152 304 36 321 385 257), lower := (rows 35 194 76 152 304 36 64 128 256), losses := [] }

theorem u5289 : Upper (D 9) (R 9) [34,192,72,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5289 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5290 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 194 76 152 304 288 69 133 261), lower := (rows 35 194 76 152 304 288 64 128 256), losses := [] }

theorem u5290 : Upper (D 9) (R 9) [34,192,72,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5290 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5291 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 45, targets := 256 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(0,8),(2,8),(3,6),(3,8)], upper := (rows 35 194 76 168 273 33 340 404 276), lower := (rows 35 194 76 168 273 33 64 128 256), losses := [] }

theorem u5291 : Upper (D 9) (R 9) [34,192,72,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5291 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5292 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 45, targets := 256 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,8),(1,5),(2,8),(3,8)], upper := (rows 35 194 76 168 273 36 337 401 273), lower := (rows 35 194 76 168 273 36 64 128 256), losses := [] }

theorem u5292 : Upper (D 9) (R 9) [34,192,72,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5292 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5293 : Route 9 := (fun mask => (mask,id))

def c5293 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5293 : Upper (D 9) (R 9) [34,192,72,160,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,257,16] 13 (by decide) (choices 1) [1,4,256] r5293 c5293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1959
  · exact u1960
  · exact u1961

def r5294 : Route 9 := (fun mask => (mask,id))

def c5294 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5294 : Upper (D 9) (R 9) [34,192,72,160,257,256] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,257,256] 13 (by decide) (choices 1) [1,4,16] r5294 c5294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1962
  · exact u1963
  · exact u1964

def b5295 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 45, targets := 256 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(0,8),(2,8),(3,6),(3,8)], upper := (rows 35 194 76 168 276 33 337 401 273), lower := (rows 35 194 76 168 276 33 64 128 256), losses := [] }

theorem u5295 : Upper (D 9) (R 9) [34,192,72,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5295 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5296 : Route 9 := (fun mask => (mask,id))

def c5296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5296 : Upper (D 9) (R 9) [34,192,72,160,260,16] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,260,16] 13 (by decide) (choices 1) [1,256] r5296 c5296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1965
  · exact u1966

def r5297 : Route 9 := (fun mask => (mask,id))

def c5297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5297 : Upper (D 9) (R 9) [34,192,72,160,260,256] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,260,256] 13 (by decide) (choices 1) [1,16] r5297 c5297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1967
  · exact u1968

def b5298 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 49, targets := 320 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(4,6),(4,8)], upper := (rows 35 194 76 265 176 33 340 404 276), lower := (rows 35 194 76 265 176 33 64 128 256), losses := [] }

theorem u5298 : Upper (D 9) (R 9) [34,192,72,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5298 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5299 : Route 9 := (fun mask => (mask,id))

def c5299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5299 : Upper (D 9) (R 9) [34,192,72,257,160,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,160,4] 13 (by decide) (choices 1) [1,16,256] r5299 c5299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1969
  · exact u1970
  · exact u1971

def b5300 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 49, targets := 320 }], pairs := [(0,6),(0,8),(4,6),(4,8)], upper := (rows 35 194 76 265 176 48 325 389 261), lower := (rows 35 194 76 265 176 48 64 128 256), losses := [] }

theorem u5300 : Upper (D 9) (R 9) [34,192,72,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5300 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5301 : Route 9 := (fun mask => (mask,id))

def c5301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5301 : Upper (D 9) (R 9) [34,192,72,257,160,256] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,160,256] 13 (by decide) (choices 1) [1,4,16] r5301 c5301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1972
  · exact u1973
  · exact u1974

def b5302 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,8),(4,6)], upper := (rows 35 194 76 265 276 33 240 176 432), lower := (rows 35 194 76 265 276 33 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 20 43 0 132 260), good := (rows 35 163 444 297 404 33 0 128 256) }] }

theorem u5302 : Upper (D 9) (R 9) [34,192,72,257,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5302 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5303 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 227, targets := 256 },{ cop := 0, region := 392, targets := 64 }], pairs := [(0,8),(1,8),(2,8),(3,6)], upper := (rows 35 194 76 265 276 48 225 161 417), lower := (rows 35 194 76 265 276 48 64 128 256), losses := [{ target := 8, region := (rows 49 59 12 8 16 48 113 177 0), good := (rows 227 194 78 207 247 243 64 128 0) }] }

theorem u5303 : Upper (D 9) (R 9) [34,192,72,257,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5303 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5304 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 76 265 276 160 113 177 305), lower := (rows 35 194 76 265 276 160 64 128 256), losses := [] }

theorem u5304 : Upper (D 9) (R 9) [34,192,72,257,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5304 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5305 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 3, region := 48, targets := 192 }], pairs := [(0,6),(0,7),(0,8),(4,6),(4,7)], upper := (rows 35 194 76 265 304 33 212 148 404), lower := (rows 35 194 76 265 304 33 64 128 256), losses := [] }

theorem u5305 : Upper (D 9) (R 9) [34,192,72,257,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5305 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5306 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 4, region := 195, targets := 256 }], pairs := [(0,8),(1,8),(3,6),(4,6)], upper := (rows 35 194 76 265 304 36 209 145 401), lower := (rows 35 194 76 265 304 36 64 128 256), losses := [] }

theorem u5306 : Upper (D 9) (R 9) [34,192,72,257,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5306 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5307 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 194 76 265 304 48 197 133 389), lower := (rows 35 194 76 265 304 48 64 128 256), losses := [] }

theorem u5307 : Upper (D 9) (R 9) [34,192,72,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5307 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5308 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 76 265 304 160 85 149 277), lower := (rows 35 194 76 265 304 160 64 128 256), losses := [] }

theorem u5308 : Upper (D 9) (R 9) [34,192,72,257,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5308 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5309 : Route 9 := (fun mask => (mask,id))

def c5309 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5309 : Upper (D 9) (R 9) [34,192,72,257,384,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,384,1] 13 (by decide) (choices 1) [4,16,32] r5309 c5309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1975
  · exact u1976
  · exact u1977

def r5310 : Route 9 := (fun mask => (mask,id))

def c5310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5310 : Upper (D 9) (R 9) [34,192,72,257,384,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,384,4] 13 (by decide) (choices 1) [1,16,32] r5310 c5310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1978
  · exact u1979
  · exact u1980

def r5311 : Route 9 := (fun mask => (mask,id))

def c5311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5311 : Upper (D 9) (R 9) [34,192,72,257,384,16] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,384,16] 13 (by decide) (choices 1) [1,4,32] r5311 c5311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1981
  · exact u1982
  · exact u1983

def b5312 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 49, targets := 256 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(4,6),(4,8)], upper := (rows 35 194 76 268 176 33 337 401 273), lower := (rows 35 194 76 268 176 33 64 128 256), losses := [] }

theorem u5312 : Upper (D 9) (R 9) [34,192,72,260,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5312 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5313 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 7, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 194 76 268 176 48 321 385 257), lower := (rows 35 194 76 268 176 48 64 128 256), losses := [] }

theorem u5313 : Upper (D 9) (R 9) [34,192,72,260,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5313 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5314 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 211, targets := 256 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(4,6),(4,8)], upper := (rows 35 194 76 268 176 288 81 145 273), lower := (rows 35 194 76 268 176 288 64 128 256), losses := [] }

theorem u5314 : Upper (D 9) (R 9) [34,192,72,260,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5314 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5315 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 384 },{ cop := 4, region := 226, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,8),(4,6)], upper := (rows 35 194 76 268 273 33 240 176 432), lower := (rows 35 194 76 268 273 33 64 128 256), losses := [] }

theorem u5315 : Upper (D 9) (R 9) [34,192,72,260,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5315 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5316 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,6),(0,8),(1,8),(4,6)], upper := (rows 35 194 76 268 273 48 225 161 417), lower := (rows 35 194 76 268 273 48 64 128 256), losses := [] }

theorem u5316 : Upper (D 9) (R 9) [34,192,72,260,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5316 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5317 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,6),(4,7)], upper := (rows 35 194 76 268 273 160 113 177 305), lower := (rows 35 194 76 268 273 160 64 128 256), losses := [] }

theorem u5317 : Upper (D 9) (R 9) [34,192,72,260,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5317 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5318 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 384 },{ cop := 4, region := 195, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,8),(4,6)], upper := (rows 35 194 76 268 304 33 209 145 401), lower := (rows 35 194 76 268 304 33 64 128 256), losses := [] }

theorem u5318 : Upper (D 9) (R 9) [34,192,72,260,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5318 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5319 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 194 76 268 304 48 193 129 385), lower := (rows 35 194 76 268 304 48 64 128 256), losses := [] }

theorem u5319 : Upper (D 9) (R 9) [34,192,72,260,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5319 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5320 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,6),(4,7)], upper := (rows 35 194 76 268 304 160 81 145 273), lower := (rows 35 194 76 268 304 160 64 128 256), losses := [] }

theorem u5320 : Upper (D 9) (R 9) [34,192,72,260,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5320 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5321 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 384 },{ cop := 4, region := 99, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,8),(4,6)], upper := (rows 35 194 76 268 400 33 113 177 305), lower := (rows 35 194 76 268 400 33 64 128 256), losses := [] }

theorem u5321 : Upper (D 9) (R 9) [34,192,72,260,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5321 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5322 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,6)], upper := (rows 35 194 76 268 400 48 97 161 289), lower := (rows 35 194 76 268 400 48 64 128 256), losses := [] }

theorem u5322 : Upper (D 9) (R 9) [34,192,72,260,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5322 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5323 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 49, targets := 320 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(4,6),(4,8)], upper := (rows 35 194 76 280 176 33 325 389 261), lower := (rows 35 194 76 280 176 33 64 128 256), losses := [] }

theorem u5323 : Upper (D 9) (R 9) [34,192,72,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5323 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5324 : Route 9 := (fun mask => (mask,id))

def c5324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5324 : Upper (D 9) (R 9) [34,192,72,272,160,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272,160,4] 13 (by decide) (choices 1) [1,256] r5324 c5324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1984
  · exact u1985

def r5325 : Route 9 := (fun mask => (mask,id))

def c5325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5325 : Upper (D 9) (R 9) [34,192,72,272,160,256] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272,160,256] 13 (by decide) (choices 1) [1,4] r5325 c5325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1986
  · exact u1987

def b5326 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 4, region := 40, targets := 192 }], pairs := [(0,6),(0,7),(0,8),(3,6),(3,7)], upper := (rows 35 194 76 296 273 33 212 148 404), lower := (rows 35 194 76 296 273 33 64 128 256), losses := [] }

theorem u5326 : Upper (D 9) (R 9) [34,192,72,288,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5326 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5327 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 408, targets := 64 }], pairs := [(1,5),(3,6),(4,5),(4,6)], upper := (rows 35 194 76 296 273 36 209 145 401), lower := (rows 35 194 76 296 273 36 64 128 256), losses := [] }

theorem u5327 : Upper (D 9) (R 9) [34,192,72,288,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5327 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5328 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 194 76 296 273 48 197 133 389), lower := (rows 35 194 76 296 273 48 64 128 256), losses := [] }

theorem u5328 : Upper (D 9) (R 9) [34,192,72,288,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5328 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5329 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 76 296 273 160 85 149 277), lower := (rows 35 194 76 296 273 160 64 128 256), losses := [] }

theorem u5329 : Upper (D 9) (R 9) [34,192,72,288,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5329 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5330 : Route 9 := (fun mask => (mask,id))

def c5330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5330 : Upper (D 9) (R 9) [34,192,72,288,260,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,260,1] 13 (by decide) (choices 1) [1,16,128] r5330 c5330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1988
  · exact u1989
  · exact u1990

def b5331 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 194 76 296 276 48 193 129 385), lower := (rows 35 194 76 296 276 48 64 128 256), losses := [] }

theorem u5331 : Upper (D 9) (R 9) [34,192,72,288,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5331 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5332 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 320 }], pairs := [(0,6),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 76 296 276 160 81 145 273), lower := (rows 35 194 76 296 276 160 64 128 256), losses := [] }

theorem u5332 : Upper (D 9) (R 9) [34,192,72,288,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5332 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5333 : Route 9 := (fun mask => (mask,id))

def c5333 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5333 : Upper (D 9) (R 9) [34,192,72,288,384,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,288,384,1] 13 (by decide) (choices 1) [1,4,16] r5333 c5333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1991
  · exact u1992
  · exact u1993

def b5334 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 0, region := 408, targets := 64 }], pairs := [(1,5),(3,6),(4,5),(4,6)], upper := (rows 35 194 76 296 400 36 81 145 273), lower := (rows 35 194 76 296 400 36 64 128 256), losses := [] }

theorem u5334 : Upper (D 9) (R 9) [34,192,72,288,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5334 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5335 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 194 76 296 400 48 69 133 261), lower := (rows 35 194 76 296 400 48 64 128 256), losses := [] }

theorem u5335 : Upper (D 9) (R 9) [34,192,72,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5335 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5336 : Route 9 := (fun mask => (mask,id))

def c5336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5336 : Upper (D 9) (R 9) [34,192,72,384,257,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,257,1] 13 (by decide) (choices 1) [4,16,32] r5336 c5336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1994
  · exact u1995
  · exact u1996

def r5337 : Route 9 := (fun mask => (mask,id))

def c5337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5337 : Upper (D 9) (R 9) [34,192,72,384,257,4] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,257,4] 13 (by decide) (choices 1) [1,16,32] r5337 c5337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1997
  · exact u1998
  · exact u1999

def r5338 : Route 9 := (fun mask => (mask,id))

def c5338 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5338 : Upper (D 9) (R 9) [34,192,72,384,257,16] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,257,16] 13 (by decide) (choices 1) [1,4,32] r5338 c5338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2000
  · exact u2001
  · exact u2002

def r5339 : Route 9 := (fun mask => (mask,id))

def c5339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5339 : Upper (D 9) (R 9) [34,192,72,384,260,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,384,260,1] 13 (by decide) (choices 1) [1,16,32] r5339 c5339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2003
  · exact u2004
  · exact u2005

#print axioms u5339
end Delivery.IrregularNine14.P09
