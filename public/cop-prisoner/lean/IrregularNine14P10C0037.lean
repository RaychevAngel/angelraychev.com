import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0015
import IrregularNine14P10C0016

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2220 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 265 400 56 120 184 312), lower := (rows 35 70 196 265 400 32 64 128 256), losses := [] }

theorem u2220 : Upper (D 10) (R 10) [34,68,192,257,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2220 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2221 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 196 296 400 57 121 185 313), lower := (rows 35 70 196 296 400 32 64 128 256), losses := [] }

theorem u2221 : Upper (D 10) (R 10) [34,68,192,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2221 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2222 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 35 70 388 56 112 425 457 393 393), lower := (rows 35 70 388 56 112 32 64 128 256), losses := [] }

theorem u2222 : Upper (D 10) (R 10) [34,68,384,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2222 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2223 : PairBound 9 := { available := 329, camps := [{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 35 70 388 56 176 361 329 457 329), lower := (rows 35 70 388 56 176 32 64 128 256), losses := [] }

theorem u2223 : Upper (D 10) (R 10) [34,68,384,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2223 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2224 : Route 9 := (fun mask => (mask,id))

def c2224 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2224 : Upper (D 10) (R 10) [34,68,384,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48,192] 13 (by decide) (choices 1) [1,8,256] r2224 c2224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u937
  · exact u938
  · exact u939

def b2225 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 35 70 388 56 400 105 105 233 361), lower := (rows 35 70 388 56 400 32 64 128 256), losses := [] }

theorem u2225 : Upper (D 10) (R 10) [34,68,384,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2225 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2226 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 388 73 152 304 368 432 304), lower := (rows 35 70 388 73 152 32 64 128 256), losses := [] }

theorem u2226 : Upper (D 10) (R 10) [34,68,384,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2226 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2227 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 35 70 388 73 176 312 376 440 312), lower := (rows 35 70 388 73 176 32 64 128 256), losses := [] }

theorem u2227 : Upper (D 10) (R 10) [34,68,384,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2227 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2228 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 420, targets := 64 },{ cop := 4, region := 360, targets := 128 }], pairs := [(2,6),(3,7)], upper := (rows 35 70 388 88 145 296 360 424 296), lower := (rows 35 70 388 88 145 32 64 128 256), losses := [] }

theorem u2228 : Upper (D 10) (R 10) [34,68,384,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2228 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2229 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 388 88 152 289 353 417 289), lower := (rows 35 70 388 88 152 32 64 128 256), losses := [] }

theorem u2229 : Upper (D 10) (R 10) [34,68,384,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2229 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2230 : Route 9 := (fun mask => (mask,id))

def c2230 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2230 : Upper (D 10) (R 10) [34,68,384,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80,160] 13 (by decide) (choices 1) [1,8,256] r2230 c2230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u940
  · exact u941
  · exact u942

def b2231 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 35 70 388 88 400 41 105 169 297), lower := (rows 35 70 388 88 400 32 64 128 256), losses := [] }

theorem u2231 : Upper (D 10) (R 10) [34,68,384,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2231 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2232 : Route 9 := (fun mask => (mask,id))

def c2232 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2232 : Upper (D 10) (R 10) [34,68,384,96,129] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,129] 13 (by decide) (choices 1) [8,16,256] r2232 c2232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u943
  · exact u944
  · exact u945

def r2233 : Route 9 := (fun mask => (mask,id))

def c2233 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2233 : Upper (D 10) (R 10) [34,68,384,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,136] 13 (by decide) (choices 1) [1,16,256] r2233 c2233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u946
  · exact u947
  · exact u948

def r2234 : Route 9 := (fun mask => (mask,id))

def c2234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2234 : Upper (D 10) (R 10) [34,68,384,96,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96,160] 13 (by decide) (choices 1) [1,8,16,256] r2234 c2234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u949
  · exact u950
  · exact u951
  · exact u952

def b2235 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 35 70 388 104 400 57 121 185 313), lower := (rows 35 70 388 104 400 32 64 128 256), losses := [] }

theorem u2235 : Upper (D 10) (R 10) [34,68,384,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2235 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2236 : Route 9 := (fun mask => (mask,id))

def c2236 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2236 : Upper (D 10) (R 10) [34,68,384,129,264] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,264] 13 (by decide) (choices 1) [16,64] r2236 c2236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u953
  · exact u954

def r2237 : Route 9 := (fun mask => (mask,id))

def c2237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2237 : Upper (D 10) (R 10) [34,68,384,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,288] 13 (by decide) (choices 1) [8,16,64] r2237 c2237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u955
  · exact u956
  · exact u957

def r2238 : Route 9 := (fun mask => (mask,id))

def c2238 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2238 : Upper (D 10) (R 10) [34,68,384,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,320] 13 (by decide) (choices 1) [8,16] r2238 c2238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u958
  · exact u959

def b2239 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 24, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 35 70 388 152 280 97 97 225 353), lower := (rows 35 70 388 152 280 32 64 128 256), losses := [] }

theorem u2239 : Upper (D 10) (R 10) [34,68,384,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2239 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2240 : Route 9 := (fun mask => (mask,id))

def c2240 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2240 : Upper (D 10) (R 10) [34,68,384,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,384,144,288] 13 (by decide) (choices 1) [1,8,64] r2240 c2240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u960
  · exact u961
  · exact u962

def r2241 : Route 9 := (fun mask => (mask,id))

def c2241 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2241 : Upper (D 10) (R 10) [34,68,384,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,384,144,320] 13 (by decide) (choices 1) [1,8] r2241 c2241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u963
  · exact u964

theorem m2242_16 : Upper (D 10) (R 10) [34,68,384,160,288,16] 13 :=
  permutation_upper _ _ _ [34,68,384,160,288,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u966

def r2242 : Route 9 := (fun mask => (mask,id))

def c2242 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2242 : Upper (D 10) (R 10) [34,68,384,160,288] 13 := by
  apply FastRouting.sound _ _ [34,68,384,160,288] 13 (by decide) (choices 1) [1,8,16,64] r2242 c2242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u965
  · exact u966
  · exact m2242_16
  · exact u967

def r2243 : Route 9 := (fun mask => (mask,id))

def c2243 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2243 : Upper (D 10) (R 10) [34,68,384,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,384,160,320] 13 (by decide) (choices 1) [1,8,16] r2243 c2243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u968
  · exact u969
  · exact u970

def b2244 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 44 200 145 308 340 404 276), lower := (rows 35 98 44 200 145 32 64 128 256), losses := [] }

theorem u2244 : Upper (D 10) (R 10) [34,96,40,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2244 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2245 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 44 200 273 436 468 404 404), lower := (rows 35 98 44 200 273 32 64 128 256), losses := [] }

theorem u2245 : Upper (D 10) (R 10) [34,96,40,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2245 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2246 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 44 200 276 433 465 401 401), lower := (rows 35 98 44 200 276 32 64 128 256), losses := [] }

theorem u2246 : Upper (D 10) (R 10) [34,96,40,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2246 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2247 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 44 200 400 309 341 405 277), lower := (rows 35 98 44 200 400 32 64 128 256), losses := [] }

theorem u2247 : Upper (D 10) (R 10) [34,96,40,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2247 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2248 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 44 392 81 436 468 404 404), lower := (rows 35 98 44 392 81 32 64 128 256), losses := [] }

theorem u2248 : Upper (D 10) (R 10) [34,96,40,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2248 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2249 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 44 392 84 433 465 401 401), lower := (rows 35 98 44 392 84 32 64 128 256), losses := [] }

theorem u2249 : Upper (D 10) (R 10) [34,96,40,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2249 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2250 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 44 392 145 372 340 468 340), lower := (rows 35 98 44 392 145 32 64 128 256), losses := [] }

theorem u2250 : Upper (D 10) (R 10) [34,96,40,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2250 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2251 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 44 392 208 309 341 405 277), lower := (rows 35 98 44 392 208 32 64 128 256), losses := [] }

theorem u2251 : Upper (D 10) (R 10) [34,96,40,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2251 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2252 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 69 140 176 312 344 408 280), lower := (rows 35 98 69 140 176 32 64 128 256), losses := [] }

theorem u2252 : Upper (D 10) (R 10) [34,96,65,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2252 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2253 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 69 140 280 432 496 432 432), lower := (rows 35 98 69 140 280 32 64 128 256), losses := [] }

theorem u2253 : Upper (D 10) (R 10) [34,96,65,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2253 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2254 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 69 140 304 440 472 408 408), lower := (rows 35 98 69 140 304 32 64 128 256), losses := [] }

theorem u2254 : Upper (D 10) (R 10) [34,96,65,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2254 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2255 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 69 140 400 312 376 440 312), lower := (rows 35 98 69 140 400 32 64 128 256), losses := [] }

theorem u2255 : Upper (D 10) (R 10) [34,96,65,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2255 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2256 : PairBound 9 := { available := 420, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 69 152 280 420 484 420 420), lower := (rows 35 98 69 152 280 32 64 128 256), losses := [] }

theorem u2256 : Upper (D 10) (R 10) [34,96,65,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2256 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2257 : PairBound 9 := { available := 396, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 69 152 304 428 460 396 396), lower := (rows 35 98 69 152 304 32 64 128 256), losses := [] }

theorem u2257 : Upper (D 10) (R 10) [34,96,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2257 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2258 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 69 168 400 316 348 412 284), lower := (rows 35 98 69 168 400 32 64 128 256), losses := [] }

theorem u2258 : Upper (D 10) (R 10) [34,96,65,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2258 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2259 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 76 137 176 308 340 404 276), lower := (rows 35 98 76 137 176 32 64 128 256), losses := [] }

theorem u2259 : Upper (D 10) (R 10) [34,96,72,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2259 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2260 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 76 137 276 432 496 432 432), lower := (rows 35 98 76 137 276 32 64 128 256), losses := [] }

theorem u2260 : Upper (D 10) (R 10) [34,96,72,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2260 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2261 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 76 137 304 436 468 404 404), lower := (rows 35 98 76 137 304 32 64 128 256), losses := [] }

theorem u2261 : Upper (D 10) (R 10) [34,96,72,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2261 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2262 : PairBound 9 := { available := 308, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 76 137 400 308 372 436 308), lower := (rows 35 98 76 137 400 32 64 128 256), losses := [] }

theorem u2262 : Upper (D 10) (R 10) [34,96,72,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2262 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2263 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 98 76 140 273 432 496 432 432), lower := (rows 35 98 76 140 273 32 64 128 256), losses := [] }

theorem u2263 : Upper (D 10) (R 10) [34,96,72,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2263 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2264 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 98 76 140 304 433 465 401 401), lower := (rows 35 98 76 140 304 32 64 128 256), losses := [] }

theorem u2264 : Upper (D 10) (R 10) [34,96,72,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2264 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2265 : PairBound 9 := { available := 420, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 76 152 273 420 484 420 420), lower := (rows 35 98 76 152 273 32 64 128 256), losses := [] }

theorem u2265 : Upper (D 10) (R 10) [34,96,72,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2265 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2266 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 76 152 276 417 481 417 417), lower := (rows 35 98 76 152 276 32 64 128 256), losses := [] }

theorem u2266 : Upper (D 10) (R 10) [34,96,72,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2266 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2267 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 76 152 304 421 453 389 389), lower := (rows 35 98 76 152 304 32 64 128 256), losses := [] }

theorem u2267 : Upper (D 10) (R 10) [34,96,72,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2267 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2268 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 76 168 145 308 340 404 276), lower := (rows 35 98 76 168 145 32 64 128 256), losses := [] }

theorem u2268 : Upper (D 10) (R 10) [34,96,72,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2268 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2269 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 76 168 273 436 468 404 404), lower := (rows 35 98 76 168 273 32 64 128 256), losses := [] }

theorem u2269 : Upper (D 10) (R 10) [34,96,72,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2269 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2270 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 76 168 276 433 465 401 401), lower := (rows 35 98 76 168 276 32 64 128 256), losses := [] }

theorem u2270 : Upper (D 10) (R 10) [34,96,72,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2270 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2271 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 76 168 400 309 341 405 277), lower := (rows 35 98 76 168 400 32 64 128 256), losses := [] }

theorem u2271 : Upper (D 10) (R 10) [34,96,72,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2271 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2272 : PairBound 9 := { available := 308, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 76 392 145 308 372 436 308), lower := (rows 35 98 76 392 145 32 64 128 256), losses := [] }

theorem u2272 : Upper (D 10) (R 10) [34,96,72,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2272 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2273 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 76 392 176 309 341 405 277), lower := (rows 35 98 76 392 176 32 64 128 256), losses := [] }

theorem u2273 : Upper (D 10) (R 10) [34,96,72,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2273 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2274 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 100 137 148 312 344 408 280), lower := (rows 35 98 100 137 148 32 64 128 256), losses := [] }

theorem u2274 : Upper (D 10) (R 10) [34,96,96,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2274 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2275 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 100 137 276 440 472 408 408), lower := (rows 35 98 100 137 276 32 64 128 256), losses := [] }

theorem u2275 : Upper (D 10) (R 10) [34,96,96,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2275 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2276 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 100 137 280 436 468 404 404), lower := (rows 35 98 100 137 280 32 64 128 256), losses := [] }

theorem u2276 : Upper (D 10) (R 10) [34,96,96,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2276 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2277 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 100 137 400 316 348 412 284), lower := (rows 35 98 100 137 400 32 64 128 256), losses := [] }

theorem u2277 : Upper (D 10) (R 10) [34,96,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2277 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2278 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 100 140 280 433 465 401 401), lower := (rows 35 98 100 140 280 32 64 128 256), losses := [] }

theorem u2278 : Upper (D 10) (R 10) [34,96,96,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2278 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2279 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 100 140 400 313 345 409 281), lower := (rows 35 98 100 140 400 32 64 128 256), losses := [] }

theorem u2279 : Upper (D 10) (R 10) [34,96,96,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2279 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u2279
end Delivery.IrregularNine14.P10
