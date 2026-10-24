import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0298
import IrregularNine14P06C0299

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34320 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 276 76 50 101 69 197 325), lower := (rows 11 162 276 76 50 32 64 128 256), losses := [] }

theorem u34320 : Upper (D 6) (R 6) [10,160,272,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34321 : Route 9 := (fun mask => (mask,id))

def c34321 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34321 : Upper (D 6) (R 6) [10,160,272,68,36] 13 := by
  apply FastRouting.sound _ _ [10,160,272,68,36] 13 (by decide) (choices 1) [1,2,64] r34321 c34321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17909
  · exact u17910
  · exact u17911

def b34322 : PairBound 9 := { available := 39, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 4, region := 422, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 162 276 76 81 39 103 167 295), lower := (rows 11 162 276 76 81 32 64 128 256), losses := [] }

theorem u34322 : Upper (D 6) (R 6) [10,160,272,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34323 : Route 9 := (fun mask => (mask,id))

def c34323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34323 : Upper (D 6) (R 6) [10,160,272,68,66] 13 := by
  apply FastRouting.sound _ _ [10,160,272,68,66] 13 (by decide) (choices 1) [1,4] r34323 c34323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17912
  · exact u17913

def b34324 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 276 76 84 35 99 163 291), lower := (rows 11 162 276 76 84 32 64 128 256), losses := [] }

theorem u34324 : Upper (D 6) (R 6) [10,160,272,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34325 : Route 9 := (fun mask => (mask,id))

def c34325 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34325 : Upper (D 6) (R 6) [10,160,272,68,96] 13 := by
  apply FastRouting.sound _ _ [10,160,272,68,96] 13 (by decide) (choices 1) [1,2,4] r34325 c34325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17914
  · exact u17915
  · exact u17916

def b34326 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 162 276 104 19 101 69 197 325), lower := (rows 11 162 276 104 19 32 64 128 256), losses := [] }

theorem u34326 : Upper (D 6) (R 6) [10,160,272,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34326 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34327 : Route 9 := (fun mask => (mask,id))

def c34327 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34327 : Upper (D 6) (R 6) [10,160,272,96,5] 13 := by
  apply FastRouting.sound _ _ [10,160,272,96,5] 13 (by decide) (choices 1) [1,2,4,64] r34327 c34327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17917
  · exact u17918
  · exact u17919
  · exact u17920

def r34328 : Route 9 := (fun mask => (mask,id))

def c34328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34328 : Upper (D 6) (R 6) [10,160,272,96,6] 13 := by
  apply FastRouting.sound _ _ [10,160,272,96,6] 13 (by decide) (choices 1) [1,4,64] r34328 c34328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17921
  · exact u17922
  · exact u17923

def b34329 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 162 276 104 81 39 71 135 263), lower := (rows 11 162 276 104 81 32 64 128 256), losses := [] }

theorem u34329 : Upper (D 6) (R 6) [10,160,272,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34330 : Route 9 := (fun mask => (mask,id))

def c34330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34330 : Upper (D 6) (R 6) [10,160,272,96,66] 13 := by
  apply FastRouting.sound _ _ [10,160,272,96,66] 13 (by decide) (choices 1) [1,4] r34330 c34330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17924
  · exact u17925

def r34331 : Route 9 := (fun mask => (mask,id))

def c34331 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34331 : Upper (D 6) (R 6) [10,160,272,96,68] 13 := by
  apply FastRouting.sound _ _ [10,160,272,96,68] 13 (by decide) (choices 1) [1,2,4] r34331 c34331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17926
  · exact u17927
  · exact u17928

def b34332 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 292 13 19 116 84 212 340), lower := (rows 11 162 292 13 19 32 64 128 256), losses := [] }

theorem u34332 : Upper (D 6) (R 6) [10,160,288,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34333 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 292 13 21 114 82 210 338), lower := (rows 11 162 292 13 21 32 64 128 256), losses := [] }

theorem u34333 : Upper (D 6) (R 6) [10,160,288,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34334 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 9, targets := 32 },{ cop := 4, region := 9, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 292 13 22 113 81 209 337), lower := (rows 11 162 292 13 22 32 64 128 256), losses := [] }

theorem u34334 : Upper (D 6) (R 6) [10,160,288,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34335 : Route 9 := (fun mask => (mask,id))

def c34335 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34335 : Upper (D 6) (R 6) [10,160,288,5,65] 13 := by
  apply FastRouting.sound _ _ [10,160,288,5,65] 13 (by decide) (choices 1) [2,4,16,64] r34335 c34335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17929
  · exact u17930
  · exact u17931
  · exact u17932

def r34336 : Route 9 := (fun mask => (mask,id))

def c34336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34336 : Upper (D 6) (R 6) [10,160,288,5,66] 13 := by
  apply FastRouting.sound _ _ [10,160,288,5,66] 13 (by decide) (choices 1) [1,4,16,64] r34336 c34336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17933
  · exact u17934
  · exact u17935
  · exact u17936

def r34337 : Route 9 := (fun mask => (mask,id))

def c34337 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34337 : Upper (D 6) (R 6) [10,160,288,5,68] 13 := by
  apply FastRouting.sound _ _ [10,160,288,5,68] 13 (by decide) (choices 1) [1,2,16,64] r34337 c34337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17937
  · exact u17938
  · exact u17939
  · exact u17940

def b34338 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 292 25 19 100 68 196 324), lower := (rows 11 162 292 25 19 32 64 128 256), losses := [] }

theorem u34338 : Upper (D 6) (R 6) [10,160,288,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34339 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 162 292 25 21 102 70 198 326), lower := (rows 11 162 292 25 21 32 64 128 256), losses := [] }

theorem u34339 : Upper (D 6) (R 6) [10,160,288,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34340 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 162 292 25 22 101 69 197 325), lower := (rows 11 162 292 25 22 32 64 128 256), losses := [] }

theorem u34340 : Upper (D 6) (R 6) [10,160,288,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34341 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 162 292 25 81 102 70 198 326), lower := (rows 11 162 292 25 81 32 64 128 256), losses := [] }

theorem u34341 : Upper (D 6) (R 6) [10,160,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34342 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 292 25 82 101 69 197 325), lower := (rows 11 162 292 25 82 32 64 128 256), losses := [] }

theorem u34342 : Upper (D 6) (R 6) [10,160,288,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34343 : Route 9 := (fun mask => (mask,id))

def c34343 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34343 : Upper (D 6) (R 6) [10,160,288,17,68] 13 := by
  apply FastRouting.sound _ _ [10,160,288,17,68] 13 (by decide) (choices 1) [1,2,4,64] r34343 c34343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17941
  · exact u17942
  · exact u17943
  · exact u17944

def b34344 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 292 28 19 101 69 197 325), lower := (rows 11 162 292 28 19 32 64 128 256), losses := [] }

theorem u34344 : Upper (D 6) (R 6) [10,160,288,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34345 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 292 28 21 99 67 195 323), lower := (rows 11 162 292 28 21 32 64 128 256), losses := [] }

theorem u34345 : Upper (D 6) (R 6) [10,160,288,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34346 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 4, region := 8, targets := 1 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 162 292 28 22 97 65 193 321), lower := (rows 11 162 292 28 22 32 64 128 256), losses := [] }

theorem u34346 : Upper (D 6) (R 6) [10,160,288,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34347 : Route 9 := (fun mask => (mask,id))

def c34347 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34347 : Upper (D 6) (R 6) [10,160,288,20,65] 13 := by
  apply FastRouting.sound _ _ [10,160,288,20,65] 13 (by decide) (choices 1) [1,2,4,64] r34347 c34347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17945
  · exact u17946
  · exact u17947
  · exact u17948

def r34348 : Route 9 := (fun mask => (mask,id))

def c34348 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34348 : Upper (D 6) (R 6) [10,160,288,20,66] 13 := by
  apply FastRouting.sound _ _ [10,160,288,20,66] 13 (by decide) (choices 1) [1,4,64] r34348 c34348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17949
  · exact u17950
  · exact u17951

def b34349 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 292 28 84 99 67 195 323), lower := (rows 11 162 292 28 84 32 64 128 256), losses := [] }

theorem u34349 : Upper (D 6) (R 6) [10,160,288,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34350 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 292 73 19 116 84 212 340), lower := (rows 11 162 292 73 19 32 64 128 256), losses := [] }

theorem u34350 : Upper (D 6) (R 6) [10,160,288,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34351 : Route 9 := (fun mask => (mask,id))

def c34351 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34351 : Upper (D 6) (R 6) [10,160,288,65,5] 13 := by
  apply FastRouting.sound _ _ [10,160,288,65,5] 13 (by decide) (choices 1) [2,4,16,64] r34351 c34351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17952
  · exact u17953
  · exact u17954
  · exact u17955

def r34352 : Route 9 := (fun mask => (mask,id))

def c34352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34352 : Upper (D 6) (R 6) [10,160,288,65,6] 13 := by
  apply FastRouting.sound _ _ [10,160,288,65,6] 13 (by decide) (choices 1) [1,4,16,64] r34352 c34352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17956
  · exact u17957
  · exact u17958
  · exact u17959

def b34353 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 162 292 73 81 54 86 150 278), lower := (rows 11 162 292 73 81 32 64 128 256), losses := [] }

theorem u34353 : Upper (D 6) (R 6) [10,160,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34354 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 292 73 82 53 85 149 277), lower := (rows 11 162 292 73 82 32 64 128 256), losses := [] }

theorem u34354 : Upper (D 6) (R 6) [10,160,288,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34355 : Route 9 := (fun mask => (mask,id))

def c34355 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34355 : Upper (D 6) (R 6) [10,160,288,65,68] 13 := by
  apply FastRouting.sound _ _ [10,160,288,65,68] 13 (by decide) (choices 1) [1,2,4,16] r34355 c34355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17960
  · exact u17961
  · exact u17962
  · exact u17963

def b34356 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 292 76 19 117 85 213 341), lower := (rows 11 162 292 76 19 32 64 128 256), losses := [] }

theorem u34356 : Upper (D 6) (R 6) [10,160,288,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34357 : Route 9 := (fun mask => (mask,id))

def c34357 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34357 : Upper (D 6) (R 6) [10,160,288,68,5] 13 := by
  apply FastRouting.sound _ _ [10,160,288,68,5] 13 (by decide) (choices 1) [1,2,16,64] r34357 c34357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17964
  · exact u17965
  · exact u17966
  · exact u17967

def r34358 : Route 9 := (fun mask => (mask,id))

def c34358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34358 : Upper (D 6) (R 6) [10,160,288,68,6] 13 := by
  apply FastRouting.sound _ _ [10,160,288,68,6] 13 (by decide) (choices 1) [1,16,64] r34358 c34358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17968
  · exact u17969
  · exact u17970

def r34359 : Route 9 := (fun mask => (mask,id))

def c34359 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34359 : Upper (D 6) (R 6) [10,160,288,68,65] 13 := by
  apply FastRouting.sound _ _ [10,160,288,68,65] 13 (by decide) (choices 1) [1,2,4,16] r34359 c34359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17971
  · exact u17972
  · exact u17973
  · exact u17974

def r34360 : Route 9 := (fun mask => (mask,id))

def c34360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34360 : Upper (D 6) (R 6) [10,160,288,68,66] 13 := by
  apply FastRouting.sound _ _ [10,160,288,68,66] 13 (by decide) (choices 1) [1,4,16] r34360 c34360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17975
  · exact u17976
  · exact u17977

def b34361 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 292 76 84 51 83 147 275), lower := (rows 11 162 292 76 84 32 64 128 256), losses := [] }

theorem u34361 : Upper (D 6) (R 6) [10,160,288,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34362 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 292 88 19 101 69 197 325), lower := (rows 11 162 292 88 19 32 64 128 256), losses := [] }

theorem u34362 : Upper (D 6) (R 6) [10,160,288,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34363 : Route 9 := (fun mask => (mask,id))

def c34363 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34363 : Upper (D 6) (R 6) [10,160,288,80,5] 13 := by
  apply FastRouting.sound _ _ [10,160,288,80,5] 13 (by decide) (choices 1) [1,2,4,64] r34363 c34363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17978
  · exact u17979
  · exact u17980
  · exact u17981

def b34364 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 73, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,5),(2,1),(3,5)], upper := (rows 11 162 292 88 22 101 69 197 325), lower := (rows 11 162 292 88 22 32 64 128 256), losses := [] }

theorem u34364 : Upper (D 6) (R 6) [10,160,288,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34365 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 162 292 88 81 39 71 135 263), lower := (rows 11 162 292 88 81 32 64 128 256), losses := [] }

theorem u34365 : Upper (D 6) (R 6) [10,160,288,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34366 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 292 88 82 37 69 133 261), lower := (rows 11 162 292 88 82 32 64 128 256), losses := [] }

theorem u34366 : Upper (D 6) (R 6) [10,160,288,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34367 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 162 292 88 84 39 71 135 263), lower := (rows 11 162 292 88 84 32 64 128 256), losses := [] }

theorem u34367 : Upper (D 6) (R 6) [10,160,288,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34368 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 324 13 19 116 116 244 372), lower := (rows 11 162 324 13 19 32 64 128 256), losses := [] }

theorem u34368 : Upper (D 6) (R 6) [10,160,320,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34369 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 324 13 21 114 114 242 370), lower := (rows 11 162 324 13 21 32 64 128 256), losses := [] }

theorem u34369 : Upper (D 6) (R 6) [10,160,320,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34370 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 324 13 22 113 113 241 369), lower := (rows 11 162 324 13 22 32 64 128 256), losses := [] }

theorem u34370 : Upper (D 6) (R 6) [10,160,320,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34371 : Route 9 := (fun mask => (mask,id))

def c34371 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34371 : Upper (D 6) (R 6) [10,160,320,5,33] 13 := by
  apply FastRouting.sound _ _ [10,160,320,5,33] 13 (by decide) (choices 1) [2,4,16,64] r34371 c34371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17982
  · exact u17983
  · exact u17984
  · exact u17985

def b34372 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 324 13 50 117 85 213 341), lower := (rows 11 162 324 13 50 32 64 128 256), losses := [] }

theorem u34372 : Upper (D 6) (R 6) [10,160,320,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34373 : Route 9 := (fun mask => (mask,id))

def c34373 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34373 : Upper (D 6) (R 6) [10,160,320,5,36] 13 := by
  apply FastRouting.sound _ _ [10,160,320,5,36] 13 (by decide) (choices 1) [1,2,16,64] r34373 c34373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17986
  · exact u17987
  · exact u17988
  · exact u17989

def r34374 : Route 9 := (fun mask => (mask,id))

def c34374 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34374 : Upper (D 6) (R 6) [10,160,320,5,65] 13 := by
  apply FastRouting.sound _ _ [10,160,320,5,65] 13 (by decide) (choices 1) [2,4,16] r34374 c34374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17990
  · exact u17991
  · exact u17992

def r34375 : Route 9 := (fun mask => (mask,id))

def c34375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34375 : Upper (D 6) (R 6) [10,160,320,5,66] 13 := by
  apply FastRouting.sound _ _ [10,160,320,5,66] 13 (by decide) (choices 1) [1,4,16] r34375 c34375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17993
  · exact u17994
  · exact u17995

def b34376 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 324 13 84 51 115 179 307), lower := (rows 11 162 324 13 84 32 64 128 256), losses := [] }

theorem u34376 : Upper (D 6) (R 6) [10,160,320,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34377 : Route 9 := (fun mask => (mask,id))

def c34377 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34377 : Upper (D 6) (R 6) [10,160,320,5,96] 13 := by
  apply FastRouting.sound _ _ [10,160,320,5,96] 13 (by decide) (choices 1) [1,2,4,16] r34377 c34377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17996
  · exact u17997
  · exact u17998
  · exact u17999

def b34378 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 162 324 25 19 100 100 228 356), lower := (rows 11 162 324 25 19 32 64 128 256), losses := [] }

theorem u34378 : Upper (D 6) (R 6) [10,160,320,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34379 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 162 324 25 21 102 102 230 358), lower := (rows 11 162 324 25 21 32 64 128 256), losses := [] }

theorem u34379 : Upper (D 6) (R 6) [10,160,320,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u34379
end Delivery.IrregularNine14.P06
