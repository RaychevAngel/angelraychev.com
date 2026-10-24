import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0398
import IrregularNine14P06C0399
import IrregularNine14P06C0400

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b38220 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 100 13 84 307 339 403 275), lower := (rows 35 138 100 13 84 32 64 128 256), losses := [] }

theorem u38220 : Upper (D 6) (R 6) [34,136,96,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38221 : Route 9 := (fun mask => (mask,id))

def c38221 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38221 : Upper (D 6) (R 6) [34,136,96,5,257] 13 := by
  apply FastRouting.sound _ _ [34,136,96,5,257] 13 (by decide) (choices 1) [2,4,16,64] r38221 c38221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23925
  · exact u23926
  · exact u23927
  · exact u23928

def r38222 : Route 9 := (fun mask => (mask,id))

def c38222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38222 : Upper (D 6) (R 6) [34,136,96,5,258] 13 := by
  apply FastRouting.sound _ _ [34,136,96,5,258] 13 (by decide) (choices 1) [1,4,16,64] r38222 c38222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23929
  · exact u23930
  · exact u23931
  · exact u23932

def r38223 : Route 9 := (fun mask => (mask,id))

def c38223 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38223 : Upper (D 6) (R 6) [34,136,96,5,260] 13 := by
  apply FastRouting.sound _ _ [34,136,96,5,260] 13 (by decide) (choices 1) [1,2,16,64] r38223 c38223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23933
  · exact u23934
  · exact u23935
  · exact u23936

def r38224 : Route 9 := (fun mask => (mask,id))

def c38224 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38224 : Upper (D 6) (R 6) [34,136,96,5,320] 13 := by
  apply FastRouting.sound _ _ [34,136,96,5,320] 13 (by decide) (choices 1) [1,2,4,16] r38224 c38224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23937
  · exact u23938
  · exact u23939
  · exact u23940

def b38225 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 138 100 14 21 369 337 465 337), lower := (rows 35 138 100 14 21 32 64 128 256), losses := [] }

theorem u38225 : Upper (D 6) (R 6) [34,136,96,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38226 : Route 9 := (fun mask => (mask,id))

def c38226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38226 : Upper (D 6) (R 6) [34,136,96,6,65] 13 := by
  apply FastRouting.sound _ _ [34,136,96,6,65] 13 (by decide) (choices 1) [1,4,16,256] r38226 c38226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23941
  · exact u23942
  · exact u23943
  · exact u23944

def b38227 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 100 14 84 305 337 401 273), lower := (rows 35 138 100 14 84 32 64 128 256), losses := [] }

theorem u38227 : Upper (D 6) (R 6) [34,136,96,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38228 : Route 9 := (fun mask => (mask,id))

def c38228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38228 : Upper (D 6) (R 6) [34,136,96,6,257] 13 := by
  apply FastRouting.sound _ _ [34,136,96,6,257] 13 (by decide) (choices 1) [1,4,16,64] r38228 c38228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23945
  · exact u23946
  · exact u23947
  · exact u23948

def r38229 : Route 9 := (fun mask => (mask,id))

def c38229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38229 : Upper (D 6) (R 6) [34,136,96,6,260] 13 := by
  apply FastRouting.sound _ _ [34,136,96,6,260] 13 (by decide) (choices 1) [1,16,64] r38229 c38229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23949
  · exact u23950
  · exact u23951

def r38230 : Route 9 := (fun mask => (mask,id))

def c38230 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38230 : Upper (D 6) (R 6) [34,136,96,6,320] 13 := by
  apply FastRouting.sound _ _ [34,136,96,6,320] 13 (by decide) (choices 1) [1,4,16] r38230 c38230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23952
  · exact u23953
  · exact u23954

def b38231 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 138 100 25 19 356 324 452 324), lower := (rows 35 138 100 25 19 32 64 128 256), losses := [] }

theorem u38231 : Upper (D 6) (R 6) [34,136,96,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38232 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 138 100 25 21 358 326 454 326), lower := (rows 35 138 100 25 21 32 64 128 256), losses := [] }

theorem u38232 : Upper (D 6) (R 6) [34,136,96,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38233 : Route 9 := (fun mask => (mask,id))

def c38233 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u38233 : Upper (D 6) (R 6) [34,136,96,17,6] 13 := by
  apply FastRouting.sound _ _ [34,136,96,17,6] 13 (by decide) (choices 1) [1,4,64,256] r38233 c38233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23955
  · exact u23956
  · exact u23957
  · exact u23958

def b38234 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 138 100 25 81 294 326 390 262), lower := (rows 35 138 100 25 81 32 64 128 256), losses := [] }

theorem u38234 : Upper (D 6) (R 6) [34,136,96,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38235 : Route 9 := (fun mask => (mask,id))

def c38235 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38235 : Upper (D 6) (R 6) [34,136,96,17,66] 13 := by
  apply FastRouting.sound _ _ [34,136,96,17,66] 13 (by decide) (choices 1) [1,4,256] r38235 c38235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23959
  · exact u23960
  · exact u23961

def b38236 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 100 25 84 295 327 391 263), lower := (rows 35 138 100 25 84 32 64 128 256), losses := [] }

theorem u38236 : Upper (D 6) (R 6) [34,136,96,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38237 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 138 100 25 273 102 70 198 326), lower := (rows 35 138 100 25 273 32 64 128 256), losses := [] }

theorem u38237 : Upper (D 6) (R 6) [34,136,96,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38238 : Route 9 := (fun mask => (mask,id))

def c38238 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38238 : Upper (D 6) (R 6) [34,136,96,17,258] 13 := by
  apply FastRouting.sound _ _ [34,136,96,17,258] 13 (by decide) (choices 1) [1,4,64] r38238 c38238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23962
  · exact u23963
  · exact u23964

def r38239 : Route 9 := (fun mask => (mask,id))

def c38239 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38239 : Upper (D 6) (R 6) [34,136,96,17,260] 13 := by
  apply FastRouting.sound _ _ [34,136,96,17,260] 13 (by decide) (choices 1) [1,2,4,64] r38239 c38239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23965
  · exact u23966
  · exact u23967
  · exact u23968

def r38240 : Route 9 := (fun mask => (mask,id))

def c38240 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38240 : Upper (D 6) (R 6) [34,136,96,17,320] 13 := by
  apply FastRouting.sound _ _ [34,136,96,17,320] 13 (by decide) (choices 1) [1,2,4] r38240 c38240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23969
  · exact u23970
  · exact u23971

def b38241 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 138 100 26 21 357 325 453 325), lower := (rows 35 138 100 26 21 32 64 128 256), losses := [] }

theorem u38241 : Upper (D 6) (R 6) [34,136,96,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38242 : Route 9 := (fun mask => (mask,id))

def c38242 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38242 : Upper (D 6) (R 6) [34,136,96,18,65] 13 := by
  apply FastRouting.sound _ _ [34,136,96,18,65] 13 (by decide) (choices 1) [1,4,256] r38242 c38242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23972
  · exact u23973
  · exact u23974

def b38243 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 100 26 84 293 325 389 261), lower := (rows 35 138 100 26 84 32 64 128 256), losses := [] }

theorem u38243 : Upper (D 6) (R 6) [34,136,96,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38244 : Route 9 := (fun mask => (mask,id))

def c38244 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38244 : Upper (D 6) (R 6) [34,136,96,18,257] 13 := by
  apply FastRouting.sound _ _ [34,136,96,18,257] 13 (by decide) (choices 1) [1,4,64] r38244 c38244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23975
  · exact u23976
  · exact u23977

def r38245 : Route 9 := (fun mask => (mask,id))

def c38245 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38245 : Upper (D 6) (R 6) [34,136,96,18,260] 13 := by
  apply FastRouting.sound _ _ [34,136,96,18,260] 13 (by decide) (choices 1) [1,4,64] r38245 c38245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23978
  · exact u23979
  · exact u23980

def r38246 : Route 9 := (fun mask => (mask,id))

def c38246 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38246 : Upper (D 6) (R 6) [34,136,96,18,320] 13 := by
  apply FastRouting.sound _ _ [34,136,96,18,320] 13 (by decide) (choices 1) [1,4] r38246 c38246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23981
  · exact u23982

def b38247 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 100 28 19 357 325 453 325), lower := (rows 35 138 100 28 19 32 64 128 256), losses := [] }

theorem u38247 : Upper (D 6) (R 6) [34,136,96,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38248 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 138 100 28 21 355 323 451 323), lower := (rows 35 138 100 28 21 32 64 128 256), losses := [] }

theorem u38248 : Upper (D 6) (R 6) [34,136,96,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38249 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 100 28 22 353 321 449 321), lower := (rows 35 138 100 28 22 32 64 128 256), losses := [] }

theorem u38249 : Upper (D 6) (R 6) [34,136,96,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38250 : Route 9 := (fun mask => (mask,id))

def c38250 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38250 : Upper (D 6) (R 6) [34,136,96,20,65] 13 := by
  apply FastRouting.sound _ _ [34,136,96,20,65] 13 (by decide) (choices 1) [1,2,4,256] r38250 c38250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23983
  · exact u23984
  · exact u23985
  · exact u23986

def b38251 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 35 138 100 28 82 293 325 389 261), lower := (rows 35 138 100 28 82 32 64 128 256), losses := [] }

theorem u38251 : Upper (D 6) (R 6) [34,136,96,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38252 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 100 28 84 291 323 387 259), lower := (rows 35 138 100 28 84 32 64 128 256), losses := [] }

theorem u38252 : Upper (D 6) (R 6) [34,136,96,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38253 : Route 9 := (fun mask => (mask,id))

def c38253 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38253 : Upper (D 6) (R 6) [34,136,96,20,257] 13 := by
  apply FastRouting.sound _ _ [34,136,96,20,257] 13 (by decide) (choices 1) [1,2,4,64] r38253 c38253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23987
  · exact u23988
  · exact u23989
  · exact u23990

def r38254 : Route 9 := (fun mask => (mask,id))

def c38254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38254 : Upper (D 6) (R 6) [34,136,96,20,258] 13 := by
  apply FastRouting.sound _ _ [34,136,96,20,258] 13 (by decide) (choices 1) [1,4,64] r38254 c38254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23991
  · exact u23992
  · exact u23993

def b38255 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 100 28 276 99 67 195 323), lower := (rows 35 138 100 28 276 32 64 128 256), losses := [] }

theorem u38255 : Upper (D 6) (R 6) [34,136,96,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38256 : Route 9 := (fun mask => (mask,id))

def c38256 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38256 : Upper (D 6) (R 6) [34,136,96,20,320] 13 := by
  apply FastRouting.sound _ _ [34,136,96,20,320] 13 (by decide) (choices 1) [1,2,4] r38256 c38256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23994
  · exact u23995
  · exact u23996

def b38257 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 100 73 19 308 340 404 276), lower := (rows 35 138 100 73 19 32 64 128 256), losses := [] }

theorem u38257 : Upper (D 6) (R 6) [34,136,96,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38258 : Route 9 := (fun mask => (mask,id))

def c38258 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38258 : Upper (D 6) (R 6) [34,136,96,65,5] 13 := by
  apply FastRouting.sound _ _ [34,136,96,65,5] 13 (by decide) (choices 1) [2,4,16,256] r38258 c38258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23997
  · exact u23998
  · exact u23999
  · exact u24000

def r38259 : Route 9 := (fun mask => (mask,id))

def c38259 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38259 : Upper (D 6) (R 6) [34,136,96,65,6] 13 := by
  apply FastRouting.sound _ _ [34,136,96,65,6] 13 (by decide) (choices 1) [1,4,16,256] r38259 c38259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24001
  · exact u24002
  · exact u24003
  · exact u24004

def r38260 : Route 9 := (fun mask => (mask,id))

def c38260 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38260 : Upper (D 6) (R 6) [34,136,96,65,257] 13 := by
  apply FastRouting.sound _ _ [34,136,96,65,257] 13 (by decide) (choices 1) [2,4,16] r38260 c38260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24005
  · exact u24006
  · exact u24007

def r38261 : Route 9 := (fun mask => (mask,id))

def c38261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38261 : Upper (D 6) (R 6) [34,136,96,65,258] 13 := by
  apply FastRouting.sound _ _ [34,136,96,65,258] 13 (by decide) (choices 1) [1,4,16] r38261 c38261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24008
  · exact u24009
  · exact u24010

def r38262 : Route 9 := (fun mask => (mask,id))

def c38262 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38262 : Upper (D 6) (R 6) [34,136,96,65,260] 13 := by
  apply FastRouting.sound _ _ [34,136,96,65,260] 13 (by decide) (choices 1) [1,2,4,16] r38262 c38262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24011
  · exact u24012
  · exact u24013
  · exact u24014

def b38263 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 138 100 74 21 309 341 405 277), lower := (rows 35 138 100 74 21 32 64 128 256), losses := [] }

theorem u38263 : Upper (D 6) (R 6) [34,136,96,66,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38264 : Route 9 := (fun mask => (mask,id))

def c38264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38264 : Upper (D 6) (R 6) [34,136,96,66,257] 13 := by
  apply FastRouting.sound _ _ [34,136,96,66,257] 13 (by decide) (choices 1) [1,4,16] r38264 c38264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24015
  · exact u24016
  · exact u24017

def r38265 : Route 9 := (fun mask => (mask,id))

def c38265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38265 : Upper (D 6) (R 6) [34,136,96,66,260] 13 := by
  apply FastRouting.sound _ _ [34,136,96,66,260] 13 (by decide) (choices 1) [1,4,16] r38265 c38265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24018
  · exact u24019
  · exact u24020

def b38266 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 100 88 19 293 325 389 261), lower := (rows 35 138 100 88 19 32 64 128 256), losses := [] }

theorem u38266 : Upper (D 6) (R 6) [34,136,96,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38267 : Route 9 := (fun mask => (mask,id))

def c38267 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38267 : Upper (D 6) (R 6) [34,136,96,80,5] 13 := by
  apply FastRouting.sound _ _ [34,136,96,80,5] 13 (by decide) (choices 1) [1,2,4,256] r38267 c38267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24021
  · exact u24022
  · exact u24023
  · exact u24024

def b38268 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 324, targets := 2 },{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 35 138 100 88 22 293 325 389 261), lower := (rows 35 138 100 88 22 32 64 128 256), losses := [{ target := 6, region := (rows 25 10 4 8 16 48 0 144 272), good := (rows 35 139 36 443 439 32 0 128 256) }] }

theorem u38268 : Upper (D 6) (R 6) [34,136,96,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38269 : Route 9 := (fun mask => (mask,id))

def c38269 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38269 : Upper (D 6) (R 6) [34,136,96,80,257] 13 := by
  apply FastRouting.sound _ _ [34,136,96,80,257] 13 (by decide) (choices 1) [1,2,4] r38269 c38269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24025
  · exact u24026
  · exact u24027

def r38270 : Route 9 := (fun mask => (mask,id))

def c38270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38270 : Upper (D 6) (R 6) [34,136,96,80,258] 13 := by
  apply FastRouting.sound _ _ [34,136,96,80,258] 13 (by decide) (choices 1) [1,4] r38270 c38270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24028
  · exact u24029

def r38271 : Route 9 := (fun mask => (mask,id))

def c38271 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38271 : Upper (D 6) (R 6) [34,136,96,80,260] 13 := by
  apply FastRouting.sound _ _ [34,136,96,80,260] 13 (by decide) (choices 1) [1,2,4] r38271 c38271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24030
  · exact u24031
  · exact u24032

def b38272 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 100 265 19 116 84 212 340), lower := (rows 35 138 100 265 19 32 64 128 256), losses := [] }

theorem u38272 : Upper (D 6) (R 6) [34,136,96,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38273 : Route 9 := (fun mask => (mask,id))

def c38273 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38273 : Upper (D 6) (R 6) [34,136,96,257,5] 13 := by
  apply FastRouting.sound _ _ [34,136,96,257,5] 13 (by decide) (choices 1) [2,4,16,64] r38273 c38273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24033
  · exact u24034
  · exact u24035
  · exact u24036

def r38274 : Route 9 := (fun mask => (mask,id))

def c38274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38274 : Upper (D 6) (R 6) [34,136,96,257,6] 13 := by
  apply FastRouting.sound _ _ [34,136,96,257,6] 13 (by decide) (choices 1) [1,4,16,64] r38274 c38274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24037
  · exact u24038
  · exact u24039
  · exact u24040

def r38275 : Route 9 := (fun mask => (mask,id))

def c38275 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38275 : Upper (D 6) (R 6) [34,136,96,257,65] 13 := by
  apply FastRouting.sound _ _ [34,136,96,257,65] 13 (by decide) (choices 1) [2,4,16] r38275 c38275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24041
  · exact u24042
  · exact u24043

def r38276 : Route 9 := (fun mask => (mask,id))

def c38276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38276 : Upper (D 6) (R 6) [34,136,96,257,66] 13 := by
  apply FastRouting.sound _ _ [34,136,96,257,66] 13 (by decide) (choices 1) [1,4,16] r38276 c38276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24044
  · exact u24045
  · exact u24046

def b38277 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 100 265 84 55 87 151 279), lower := (rows 35 138 100 265 84 32 64 128 256), losses := [] }

theorem u38277 : Upper (D 6) (R 6) [34,136,96,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38278 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 84, targets := 2 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 138 100 266 21 117 85 213 341), lower := (rows 35 138 100 266 21 32 64 128 256), losses := [] }

theorem u38278 : Upper (D 6) (R 6) [34,136,96,258,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38279 : Route 9 := (fun mask => (mask,id))

def c38279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38279 : Upper (D 6) (R 6) [34,136,96,258,65] 13 := by
  apply FastRouting.sound _ _ [34,136,96,258,65] 13 (by decide) (choices 1) [1,4,16] r38279 c38279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24047
  · exact u24048
  · exact u24049

#print axioms u38279
end Delivery.IrregularNine14.P06
