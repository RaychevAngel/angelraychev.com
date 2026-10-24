import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0482
import IrregularNine14P07C0483
import IrregularNine14P07C0484

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40320 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 28 41 146 227 195 195 451), lower := (rows 97 262 28 41 146 32 64 128 256), losses := [] }

theorem u40320 : Upper (D 7) (R 7) [96,260,24,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40321 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 97 262 28 41 208 163 195 131 387), lower := (rows 97 262 28 41 208 32 64 128 256), losses := [] }

theorem u40321 : Upper (D 7) (R 7) [96,260,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40322 : Route 9 := (fun mask => (mask,id))

def c40322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40322 : Upper (D 7) (R 7) [96,260,24,34,66] 13 := by
  apply FastRouting.sound _ _ [96,260,24,34,66] 13 (by decide) (choices 1) [1,128] r40322 c40322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u28940
  · exact u28941

def r40323 : Route 9 := (fun mask => (mask,id))

def c40323 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40323 : Upper (D 7) (R 7) [96,260,24,34,129] 13 := by
  apply FastRouting.sound _ _ [96,260,24,34,129] 13 (by decide) (choices 1) [1,2,64,128] r40323 c40323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28942
  · exact u28943
  · exact u28944
  · exact u28945

def r40324 : Route 9 := (fun mask => (mask,id))

def c40324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40324 : Upper (D 7) (R 7) [96,260,24,34,130] 13 := by
  apply FastRouting.sound _ _ [96,260,24,34,130] 13 (by decide) (choices 1) [1,64,128] r40324 c40324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28946
  · exact u28947
  · exact u28948

def r40325 : Route 9 := (fun mask => (mask,id))

def c40325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40325 : Upper (D 7) (R 7) [96,260,24,34,192] 13 := by
  apply FastRouting.sound _ _ [96,260,24,34,192] 13 (by decide) (choices 1) [1,2,128] r40325 c40325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28949
  · exact u28950
  · exact u28951

def b40326 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 262 28 104 145 163 195 131 387), lower := (rows 97 262 28 104 145 32 64 128 256), losses := [] }

theorem u40326 : Upper (D 7) (R 7) [96,260,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40327 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 130 },{ cop := 3, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 97 262 28 104 146 163 195 131 387), lower := (rows 97 262 28 104 146 32 64 128 256), losses := [] }

theorem u40327 : Upper (D 7) (R 7) [96,260,24,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40328 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 20, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 97 262 28 137 145 98 98 226 354), lower := (rows 97 262 28 137 145 32 64 128 256), losses := [] }

theorem u40328 : Upper (D 7) (R 7) [96,260,24,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40329 : Route 9 := (fun mask => (mask,id))

def c40329 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40329 : Upper (D 7) (R 7) [96,260,24,129,130] 13 := by
  apply FastRouting.sound _ _ [96,260,24,129,130] 13 (by decide) (choices 1) [1,2,64] r40329 c40329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28952
  · exact u28953
  · exact u28954

def r40330 : Route 9 := (fun mask => (mask,id))

def c40330 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40330 : Upper (D 7) (R 7) [96,260,24,129,160] 13 := by
  apply FastRouting.sound _ _ [96,260,24,129,160] 13 (by decide) (choices 1) [1,2,64] r40330 c40330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28955
  · exact u28956
  · exact u28957

def b40331 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 20, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(4,0)], upper := (rows 97 262 28 138 146 97 97 225 353), lower := (rows 97 262 28 138 146 32 64 128 256), losses := [] }

theorem u40331 : Upper (D 7) (R 7) [96,260,24,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40332 : Route 9 := (fun mask => (mask,id))

def c40332 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40332 : Upper (D 7) (R 7) [96,260,24,130,160] 13 := by
  apply FastRouting.sound _ _ [96,260,24,130,160] 13 (by decide) (choices 1) [1,2,64] r40332 c40332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28958
  · exact u28959
  · exact u28960

def r40333 : Route 9 := (fun mask => (mask,id))

def c40333 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40333 : Upper (D 7) (R 7) [96,260,24,160,192] 13 := by
  apply FastRouting.sound _ _ [96,260,24,160,192] 13 (by decide) (choices 1) [1,2] r40333 c40333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u28961
  · exact u28962

def b40334 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 241, targets := 2 },{ cop := 3, region := 16, targets := 192 }], pairs := [(0,1),(4,1),(4,6),(4,7)], upper := (rows 97 262 38 11 25 240 208 208 464), lower := (rows 97 262 38 11 25 32 64 128 256), losses := [] }

theorem u40334 : Upper (D 7) (R 7) [96,260,34,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40335 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 262 38 11 81 184 216 152 408), lower := (rows 97 262 38 11 81 32 64 128 256), losses := [] }

theorem u40335 : Upper (D 7) (R 7) [96,260,34,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40335 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40336 : Route 9 := (fun mask => (mask,id))

def c40336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40336 : Upper (D 7) (R 7) [96,260,34,3,72] 13 := by
  apply FastRouting.sound _ _ [96,260,34,3,72] 13 (by decide) (choices 1) [1,16,128] r40336 c40336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28963
  · exact u28964
  · exact u28965

def r40337 : Route 9 := (fun mask => (mask,id))

def c40337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u40337 : Upper (D 7) (R 7) [96,260,34,3,129] 13 := by
  apply FastRouting.sound _ _ [96,260,34,3,129] 13 (by decide) (choices 1) [8,16,64,128] r40337 c40337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28966
  · exact u28967
  · exact u28968
  · exact u28969

def r40338 : Route 9 := (fun mask => (mask,id))

def c40338 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40338 : Upper (D 7) (R 7) [96,260,34,3,136] 13 := by
  apply FastRouting.sound _ _ [96,260,34,3,136] 13 (by decide) (choices 1) [1,16,64,128] r40338 c40338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28970
  · exact u28971
  · exact u28972
  · exact u28973

def r40339 : Route 9 := (fun mask => (mask,id))

def c40339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40339 : Upper (D 7) (R 7) [96,260,34,3,192] 13 := by
  apply FastRouting.sound _ _ [96,260,34,3,192] 13 (by decide) (choices 1) [1,8,16,128] r40339 c40339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28974
  · exact u28975
  · exact u28976
  · exact u28977

def b40340 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 262 38 25 25 226 194 194 450), lower := (rows 97 262 38 25 25 32 64 128 256), losses := [] }

theorem u40340 : Upper (D 7) (R 7) [96,260,34,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40341 : Route 9 := (fun mask => (mask,id))

def c40341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40341 : Upper (D 7) (R 7) [96,260,34,17,10] 13 := by
  apply FastRouting.sound _ _ [96,260,34,17,10] 13 (by decide) (choices 1) [1,64,128] r40341 c40341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28978
  · exact u28979
  · exact u28980

def b40342 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 24, targets := 162 }], pairs := [(3,1),(3,5),(3,7),(4,1)], upper := (rows 97 262 38 25 81 170 202 138 394), lower := (rows 97 262 38 25 81 32 64 128 256), losses := [] }

theorem u40342 : Upper (D 7) (R 7) [96,260,34,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40343 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 422, targets := 64 },{ cop := 4, region := 169, targets := 2 }], pairs := [(0,1),(1,6),(2,6),(3,1)], upper := (rows 97 262 38 25 82 169 201 137 393), lower := (rows 97 262 38 25 82 32 64 128 256), losses := [] }

theorem u40343 : Upper (D 7) (R 7) [96,260,34,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40344 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 24, targets := 162 }], pairs := [(3,1),(3,5),(3,7),(4,1)], upper := (rows 97 262 38 25 88 163 195 131 387), lower := (rows 97 262 38 25 88 32 64 128 256), losses := [] }

theorem u40344 : Upper (D 7) (R 7) [96,260,34,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40345 : PairBound 9 := { available := 202, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 262 38 25 145 234 202 202 458), lower := (rows 97 262 38 25 145 32 64 128 256), losses := [] }

theorem u40345 : Upper (D 7) (R 7) [96,260,34,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40346 : Route 9 := (fun mask => (mask,id))

def c40346 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40346 : Upper (D 7) (R 7) [96,260,34,17,130] 13 := by
  apply FastRouting.sound _ _ [96,260,34,17,130] 13 (by decide) (choices 1) [1,8,64,128] r40346 c40346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28981
  · exact u28982
  · exact u28983
  · exact u28984

def r40347 : Route 9 := (fun mask => (mask,id))

def c40347 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40347 : Upper (D 7) (R 7) [96,260,34,17,136] 13 := by
  apply FastRouting.sound _ _ [96,260,34,17,136] 13 (by decide) (choices 1) [1,2,64,128] r40347 c40347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28985
  · exact u28986
  · exact u28987
  · exact u28988

def r40348 : Route 9 := (fun mask => (mask,id))

def c40348 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40348 : Upper (D 7) (R 7) [96,260,34,17,192] 13 := by
  apply FastRouting.sound _ _ [96,260,34,17,192] 13 (by decide) (choices 1) [1,2,8,128] r40348 c40348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28989
  · exact u28990
  · exact u28991
  · exact u28992

def b40349 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 262 38 26 81 169 201 137 393), lower := (rows 97 262 38 26 81 32 64 128 256), losses := [] }

theorem u40349 : Upper (D 7) (R 7) [96,260,34,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40350 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 3, region := 241, targets := 2 }], pairs := [(0,1),(1,6),(2,6),(4,1)], upper := (rows 97 262 38 26 88 161 193 129 385), lower := (rows 97 262 38 26 88 32 64 128 256), losses := [] }

theorem u40350 : Upper (D 7) (R 7) [96,260,34,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40351 : Route 9 := (fun mask => (mask,id))

def c40351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40351 : Upper (D 7) (R 7) [96,260,34,18,129] 13 := by
  apply FastRouting.sound _ _ [96,260,34,18,129] 13 (by decide) (choices 1) [1,8,64,128] r40351 c40351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28993
  · exact u28994
  · exact u28995
  · exact u28996

def r40352 : Route 9 := (fun mask => (mask,id))

def c40352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u40352 : Upper (D 7) (R 7) [96,260,34,18,136] 13 := by
  apply FastRouting.sound _ _ [96,260,34,18,136] 13 (by decide) (choices 1) [1,64,128] r40352 c40352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u28997
  · exact u28998
  · exact u28999

def r40353 : Route 9 := (fun mask => (mask,id))

def c40353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40353 : Upper (D 7) (R 7) [96,260,34,18,192] 13 := by
  apply FastRouting.sound _ _ [96,260,34,18,192] 13 (by decide) (choices 1) [1,8,128] r40353 c40353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29000
  · exact u29001
  · exact u29002

def b40354 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 262 38 73 145 186 218 154 410), lower := (rows 97 262 38 73 145 32 64 128 256), losses := [] }

theorem u40354 : Upper (D 7) (R 7) [96,260,34,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40355 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 262 38 73 146 185 217 153 409), lower := (rows 97 262 38 73 146 32 64 128 256), losses := [] }

theorem u40355 : Upper (D 7) (R 7) [96,260,34,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40356 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 262 38 73 152 179 211 147 403), lower := (rows 97 262 38 73 152 32 64 128 256), losses := [] }

theorem u40356 : Upper (D 7) (R 7) [96,260,34,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40357 : Route 9 := (fun mask => (mask,id))

def c40357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40357 : Upper (D 7) (R 7) [96,260,34,66,129] 13 := by
  apply FastRouting.sound _ _ [96,260,34,66,129] 13 (by decide) (choices 1) [1,8,16,128] r40357 c40357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29003
  · exact u29004
  · exact u29005
  · exact u29006

def r40358 : Route 9 := (fun mask => (mask,id))

def c40358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40358 : Upper (D 7) (R 7) [96,260,34,66,136] 13 := by
  apply FastRouting.sound _ _ [96,260,34,66,136] 13 (by decide) (choices 1) [1,16,128] r40358 c40358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29007
  · exact u29008
  · exact u29009

def r40359 : Route 9 := (fun mask => (mask,id))

def c40359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40359 : Upper (D 7) (R 7) [96,260,34,80,129] 13 := by
  apply FastRouting.sound _ _ [96,260,34,80,129] 13 (by decide) (choices 1) [1,2,8,128] r40359 c40359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29010
  · exact u29011
  · exact u29012
  · exact u29013

def r40360 : Route 9 := (fun mask => (mask,id))

def c40360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40360 : Upper (D 7) (R 7) [96,260,34,80,130] 13 := by
  apply FastRouting.sound _ _ [96,260,34,80,130] 13 (by decide) (choices 1) [1,8,128] r40360 c40360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29014
  · exact u29015
  · exact u29016

def r40361 : Route 9 := (fun mask => (mask,id))

def c40361 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40361 : Upper (D 7) (R 7) [96,260,34,80,136] 13 := by
  apply FastRouting.sound _ _ [96,260,34,80,136] 13 (by decide) (choices 1) [1,2,128] r40361 c40361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29017
  · exact u29018
  · exact u29019

def b40362 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 97 262 38 137 145 122 90 218 346), lower := (rows 97 262 38 137 145 32 64 128 256), losses := [] }

theorem u40362 : Upper (D 7) (R 7) [96,260,34,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40362 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40363 : Route 9 := (fun mask => (mask,id))

def c40363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40363 : Upper (D 7) (R 7) [96,260,34,129,130] 13 := by
  apply FastRouting.sound _ _ [96,260,34,129,130] 13 (by decide) (choices 1) [1,8,16,64] r40363 c40363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29020
  · exact u29021
  · exact u29022
  · exact u29023

def b40364 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 97 262 38 137 152 115 83 211 339), lower := (rows 97 262 38 137 152 32 64 128 256), losses := [] }

theorem u40364 : Upper (D 7) (R 7) [96,260,34,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40365 : Route 9 := (fun mask => (mask,id))

def c40365 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40365 : Upper (D 7) (R 7) [96,260,34,129,192] 13 := by
  apply FastRouting.sound _ _ [96,260,34,129,192] 13 (by decide) (choices 1) [1,2,8,16] r40365 c40365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29024
  · exact u29025
  · exact u29026
  · exact u29027

def b40366 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 262 38 138 152 113 81 209 337), lower := (rows 97 262 38 138 152 32 64 128 256), losses := [] }

theorem u40366 : Upper (D 7) (R 7) [96,260,34,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40367 : Route 9 := (fun mask => (mask,id))

def c40367 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40367 : Upper (D 7) (R 7) [96,260,34,130,192] 13 := by
  apply FastRouting.sound _ _ [96,260,34,130,192] 13 (by decide) (choices 1) [1,8,16] r40367 c40367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29028
  · exact u29029
  · exact u29030

def b40368 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 262 38 152 152 99 67 195 323), lower := (rows 97 262 38 152 152 32 64 128 256), losses := [] }

theorem u40368 : Upper (D 7) (R 7) [96,260,34,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40369 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 97 262 38 152 208 43 75 139 267), lower := (rows 97 262 38 152 208 32 64 128 256), losses := [] }

theorem u40369 : Upper (D 7) (R 7) [96,260,34,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40370 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 16, targets := 192 },{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 97 262 44 11 19 240 208 208 464), lower := (rows 97 262 44 11 19 32 64 128 256), losses := [] }

theorem u40370 : Upper (D 7) (R 7) [96,260,40,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40371 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 262 44 11 81 178 210 146 402), lower := (rows 97 262 44 11 81 32 64 128 256), losses := [] }

theorem u40371 : Upper (D 7) (R 7) [96,260,40,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40372 : Route 9 := (fun mask => (mask,id))

def c40372 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40372 : Upper (D 7) (R 7) [96,260,40,3,66] 13 := by
  apply FastRouting.sound _ _ [96,260,40,3,66] 13 (by decide) (choices 1) [1,16,128] r40372 c40372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29031
  · exact u29032
  · exact u29033

def r40373 : Route 9 := (fun mask => (mask,id))

def c40373 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40373 : Upper (D 7) (R 7) [96,260,40,3,129] 13 := by
  apply FastRouting.sound _ _ [96,260,40,3,129] 13 (by decide) (choices 1) [2,16,64,128] r40373 c40373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29034
  · exact u29035
  · exact u29036
  · exact u29037

def r40374 : Route 9 := (fun mask => (mask,id))

def c40374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u40374 : Upper (D 7) (R 7) [96,260,40,3,130] 13 := by
  apply FastRouting.sound _ _ [96,260,40,3,130] 13 (by decide) (choices 1) [1,16,64,128] r40374 c40374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29038
  · exact u29039
  · exact u29040
  · exact u29041

def r40375 : Route 9 := (fun mask => (mask,id))

def c40375 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40375 : Upper (D 7) (R 7) [96,260,40,3,192] 13 := by
  apply FastRouting.sound _ _ [96,260,40,3,192] 13 (by decide) (choices 1) [1,2,16,128] r40375 c40375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u29042
  · exact u29043
  · exact u29044
  · exact u29045

def b40376 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 194 },{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 97 262 44 25 19 226 194 194 450), lower := (rows 97 262 44 25 19 32 64 128 256), losses := [] }

theorem u40376 : Upper (D 7) (R 7) [96,260,40,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40377 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 28, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 97 262 44 25 81 162 194 130 386), lower := (rows 97 262 44 25 81 32 64 128 256), losses := [] }

theorem u40377 : Upper (D 7) (R 7) [96,260,40,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r40378 : Route 9 := (fun mask => (mask,id))

def c40378 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u40378 : Upper (D 7) (R 7) [96,260,40,17,66] 13 := by
  apply FastRouting.sound _ _ [96,260,40,17,66] 13 (by decide) (choices 1) [1,2,128] r40378 c40378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u29046
  · exact u29047
  · exact u29048

def b40379 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 262 44 25 145 226 194 194 450), lower := (rows 97 262 44 25 145 32 64 128 256), losses := [] }

theorem u40379 : Upper (D 7) (R 7) [96,260,40,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u40379
end Delivery.IrregularNine14.P07
