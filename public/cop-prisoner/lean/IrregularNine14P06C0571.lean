import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0296
import IrregularNine14P06C0297
import IrregularNine14P06C0298

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r34260 : Route 9 := (fun mask => (mask,id))

def c34260 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34260 : Upper (D 6) (R 6) [10,160,258,20,65] 13 := by
  apply FastRouting.sound _ _ [10,160,258,20,65] 13 (by decide) (choices 1) [1,4,64] r34260 c34260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17795
  · exact u17796
  · exact u17797

def b34261 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 262 28 84 97 97 225 353), lower := (rows 11 162 262 28 84 32 64 128 256), losses := [] }

theorem u34261 : Upper (D 6) (R 6) [10,160,258,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34262 : Route 9 := (fun mask => (mask,id))

def c34262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34262 : Upper (D 6) (R 6) [10,160,258,20,96] 13 := by
  apply FastRouting.sound _ _ [10,160,258,20,96] 13 (by decide) (choices 1) [1,4,64] r34262 c34262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17798
  · exact u17799
  · exact u17800

def b34263 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 104, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 262 44 21 113 81 209 337), lower := (rows 11 162 262 44 21 32 64 128 256), losses := [] }

theorem u34263 : Upper (D 6) (R 6) [10,160,258,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34264 : Route 9 := (fun mask => (mask,id))

def c34264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34264 : Upper (D 6) (R 6) [10,160,258,36,65] 13 := by
  apply FastRouting.sound _ _ [10,160,258,36,65] 13 (by decide) (choices 1) [1,4,16,64] r34264 c34264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17801
  · exact u17802
  · exact u17803
  · exact u17804

def r34265 : Route 9 := (fun mask => (mask,id))

def c34265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34265 : Upper (D 6) (R 6) [10,160,258,36,68] 13 := by
  apply FastRouting.sound _ _ [10,160,258,36,68] 13 (by decide) (choices 1) [1,16,64] r34265 c34265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17805
  · exact u17806
  · exact u17807

def b34266 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 104, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 262 56 21 101 69 197 325), lower := (rows 11 162 262 56 21 32 64 128 256), losses := [] }

theorem u34266 : Upper (D 6) (R 6) [10,160,258,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34267 : Route 9 := (fun mask => (mask,id))

def c34267 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34267 : Upper (D 6) (R 6) [10,160,258,48,65] 13 := by
  apply FastRouting.sound _ _ [10,160,258,48,65] 13 (by decide) (choices 1) [1,4,64] r34267 c34267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17808
  · exact u17809
  · exact u17810

def r34268 : Route 9 := (fun mask => (mask,id))

def c34268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34268 : Upper (D 6) (R 6) [10,160,258,48,68] 13 := by
  apply FastRouting.sound _ _ [10,160,258,48,68] 13 (by decide) (choices 1) [1,4,64] r34268 c34268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17811
  · exact u17812
  · exact u17813

def b34269 : PairBound 9 := { available := 116, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 104, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 162 262 73 21 116 116 244 372), lower := (rows 11 162 262 73 21 32 64 128 256), losses := [] }

theorem u34269 : Upper (D 6) (R 6) [10,160,258,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34270 : Route 9 := (fun mask => (mask,id))

def c34270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34270 : Upper (D 6) (R 6) [10,160,258,65,33] 13 := by
  apply FastRouting.sound _ _ [10,160,258,65,33] 13 (by decide) (choices 1) [4,16,64] r34270 c34270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17814
  · exact u17815
  · exact u17816

def r34271 : Route 9 := (fun mask => (mask,id))

def c34271 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34271 : Upper (D 6) (R 6) [10,160,258,65,36] 13 := by
  apply FastRouting.sound _ _ [10,160,258,65,36] 13 (by decide) (choices 1) [1,4,16,64] r34271 c34271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17817
  · exact u17818
  · exact u17819
  · exact u17820

def b34272 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 162 262 73 81 52 116 180 308), lower := (rows 11 162 262 73 81 32 64 128 256), losses := [] }

theorem u34272 : Upper (D 6) (R 6) [10,160,258,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34273 : Route 9 := (fun mask => (mask,id))

def c34273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34273 : Upper (D 6) (R 6) [10,160,258,65,68] 13 := by
  apply FastRouting.sound _ _ [10,160,258,65,68] 13 (by decide) (choices 1) [1,4,16] r34273 c34273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17821
  · exact u17822
  · exact u17823

def r34274 : Route 9 := (fun mask => (mask,id))

def c34274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34274 : Upper (D 6) (R 6) [10,160,258,65,96] 13 := by
  apply FastRouting.sound _ _ [10,160,258,65,96] 13 (by decide) (choices 1) [1,4,16] r34274 c34274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17824
  · exact u17825
  · exact u17826

def r34275 : Route 9 := (fun mask => (mask,id))

def c34275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34275 : Upper (D 6) (R 6) [10,160,258,68,5] 13 := by
  apply FastRouting.sound _ _ [10,160,258,68,5] 13 (by decide) (choices 1) [1,16,64] r34275 c34275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17827
  · exact u17828
  · exact u17829

def r34276 : Route 9 := (fun mask => (mask,id))

def c34276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34276 : Upper (D 6) (R 6) [10,160,258,68,33] 13 := by
  apply FastRouting.sound _ _ [10,160,258,68,33] 13 (by decide) (choices 1) [1,4,16,64] r34276 c34276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17830
  · exact u17831
  · exact u17832
  · exact u17833

def r34277 : Route 9 := (fun mask => (mask,id))

def c34277 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34277 : Upper (D 6) (R 6) [10,160,258,68,36] 13 := by
  apply FastRouting.sound _ _ [10,160,258,68,36] 13 (by decide) (choices 1) [1,16,64] r34277 c34277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17834
  · exact u17835
  · exact u17836

def r34278 : Route 9 := (fun mask => (mask,id))

def c34278 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34278 : Upper (D 6) (R 6) [10,160,258,68,65] 13 := by
  apply FastRouting.sound _ _ [10,160,258,68,65] 13 (by decide) (choices 1) [1,4,16] r34278 c34278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17837
  · exact u17838
  · exact u17839

def b34279 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 162 262 76 84 49 113 177 305), lower := (rows 11 162 262 76 84 32 64 128 256), losses := [] }

theorem u34279 : Upper (D 6) (R 6) [10,160,258,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34280 : Route 9 := (fun mask => (mask,id))

def c34280 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34280 : Upper (D 6) (R 6) [10,160,258,68,96] 13 := by
  apply FastRouting.sound _ _ [10,160,258,68,96] 13 (by decide) (choices 1) [1,4,16] r34280 c34280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17840
  · exact u17841
  · exact u17842

def r34281 : Route 9 := (fun mask => (mask,id))

def c34281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34281 : Upper (D 6) (R 6) [10,160,258,80,5] 13 := by
  apply FastRouting.sound _ _ [10,160,258,80,5] 13 (by decide) (choices 1) [1,4,64] r34281 c34281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17843
  · exact u17844
  · exact u17845

def r34282 : Route 9 := (fun mask => (mask,id))

def c34282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34282 : Upper (D 6) (R 6) [10,160,258,80,33] 13 := by
  apply FastRouting.sound _ _ [10,160,258,80,33] 13 (by decide) (choices 1) [1,4,64] r34282 c34282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17846
  · exact u17847
  · exact u17848

def r34283 : Route 9 := (fun mask => (mask,id))

def c34283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34283 : Upper (D 6) (R 6) [10,160,258,80,36] 13 := by
  apply FastRouting.sound _ _ [10,160,258,80,36] 13 (by decide) (choices 1) [1,4,64] r34283 c34283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17849
  · exact u17850
  · exact u17851

def b34284 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 162 262 88 81 37 101 165 293), lower := (rows 11 162 262 88 81 32 64 128 256), losses := [] }

theorem u34284 : Upper (D 6) (R 6) [10,160,258,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34285 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 162 262 88 84 37 101 165 293), lower := (rows 11 162 262 88 84 32 64 128 256), losses := [] }

theorem u34285 : Upper (D 6) (R 6) [10,160,258,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34286 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 162 262 88 112 37 69 133 261), lower := (rows 11 162 262 88 112 32 64 128 256), losses := [] }

theorem u34286 : Upper (D 6) (R 6) [10,160,258,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34287 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 104, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 262 104 21 117 85 213 341), lower := (rows 11 162 262 104 21 32 64 128 256), losses := [] }

theorem u34287 : Upper (D 6) (R 6) [10,160,258,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34288 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 162 262 104 81 53 85 149 277), lower := (rows 11 162 262 104 81 32 64 128 256), losses := [] }

theorem u34288 : Upper (D 6) (R 6) [10,160,258,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34289 : Route 9 := (fun mask => (mask,id))

def c34289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34289 : Upper (D 6) (R 6) [10,160,258,96,68] 13 := by
  apply FastRouting.sound _ _ [10,160,258,96,68] 13 (by decide) (choices 1) [1,4,16] r34289 c34289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17852
  · exact u17853
  · exact u17854

def b34290 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 276 13 19 100 100 228 356), lower := (rows 11 162 276 13 19 32 64 128 256), losses := [] }

theorem u34290 : Upper (D 6) (R 6) [10,160,272,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34291 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 162 276 13 21 98 98 226 354), lower := (rows 11 162 276 13 21 32 64 128 256), losses := [] }

theorem u34291 : Upper (D 6) (R 6) [10,160,272,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34292 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 276 13 22 97 97 225 353), lower := (rows 11 162 276 13 22 32 64 128 256), losses := [] }

theorem u34292 : Upper (D 6) (R 6) [10,160,272,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34293 : Route 9 := (fun mask => (mask,id))

def c34293 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34293 : Upper (D 6) (R 6) [10,160,272,5,33] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5,33] 13 (by decide) (choices 1) [2,4,64] r34293 c34293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17855
  · exact u17856
  · exact u17857

def b34294 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 276 13 50 101 69 197 325), lower := (rows 11 162 276 13 50 32 64 128 256), losses := [] }

theorem u34294 : Upper (D 6) (R 6) [10,160,272,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34295 : Route 9 := (fun mask => (mask,id))

def c34295 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34295 : Upper (D 6) (R 6) [10,160,272,5,36] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5,36] 13 (by decide) (choices 1) [1,2,64] r34295 c34295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17858
  · exact u17859
  · exact u17860

def r34296 : Route 9 := (fun mask => (mask,id))

def c34296 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34296 : Upper (D 6) (R 6) [10,160,272,5,65] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5,65] 13 (by decide) (choices 1) [2,4,64] r34296 c34296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17861
  · exact u17862
  · exact u17863

def r34297 : Route 9 := (fun mask => (mask,id))

def c34297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34297 : Upper (D 6) (R 6) [10,160,272,5,66] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5,66] 13 (by decide) (choices 1) [1,4,64] r34297 c34297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17864
  · exact u17865
  · exact u17866

def r34298 : Route 9 := (fun mask => (mask,id))

def c34298 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34298 : Upper (D 6) (R 6) [10,160,272,5,68] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5,68] 13 (by decide) (choices 1) [1,2,64] r34298 c34298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17867
  · exact u17868
  · exact u17869

def r34299 : Route 9 := (fun mask => (mask,id))

def c34299 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34299 : Upper (D 6) (R 6) [10,160,272,5,96] 13 := by
  apply FastRouting.sound _ _ [10,160,272,5,96] 13 (by decide) (choices 1) [1,2,4,64] r34299 c34299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17870
  · exact u17871
  · exact u17872
  · exact u17873

def b34300 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 162 276 44 19 101 69 197 325), lower := (rows 11 162 276 44 19 32 64 128 256), losses := [] }

theorem u34300 : Upper (D 6) (R 6) [10,160,272,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34301 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 276 44 21 99 67 195 323), lower := (rows 11 162 276 44 21 32 64 128 256), losses := [] }

theorem u34301 : Upper (D 6) (R 6) [10,160,272,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34302 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 276 44 22 97 65 193 321), lower := (rows 11 162 276 44 22 32 64 128 256), losses := [] }

theorem u34302 : Upper (D 6) (R 6) [10,160,272,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34303 : Route 9 := (fun mask => (mask,id))

def c34303 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34303 : Upper (D 6) (R 6) [10,160,272,36,65] 13 := by
  apply FastRouting.sound _ _ [10,160,272,36,65] 13 (by decide) (choices 1) [1,2,4,64] r34303 c34303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17874
  · exact u17875
  · exact u17876
  · exact u17877

def r34304 : Route 9 := (fun mask => (mask,id))

def c34304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34304 : Upper (D 6) (R 6) [10,160,272,36,66] 13 := by
  apply FastRouting.sound _ _ [10,160,272,36,66] 13 (by decide) (choices 1) [1,4,64] r34304 c34304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17878
  · exact u17879
  · exact u17880

def b34305 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 276 44 84 99 67 195 323), lower := (rows 11 162 276 44 84 32 64 128 256), losses := [] }

theorem u34305 : Upper (D 6) (R 6) [10,160,272,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34306 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 276 73 19 100 100 228 356), lower := (rows 11 162 276 73 19 32 64 128 256), losses := [] }

theorem u34306 : Upper (D 6) (R 6) [10,160,272,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34307 : Route 9 := (fun mask => (mask,id))

def c34307 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34307 : Upper (D 6) (R 6) [10,160,272,65,5] 13 := by
  apply FastRouting.sound _ _ [10,160,272,65,5] 13 (by decide) (choices 1) [2,4,64] r34307 c34307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17881
  · exact u17882
  · exact u17883

def r34308 : Route 9 := (fun mask => (mask,id))

def c34308 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34308 : Upper (D 6) (R 6) [10,160,272,65,6] 13 := by
  apply FastRouting.sound _ _ [10,160,272,65,6] 13 (by decide) (choices 1) [1,4,64] r34308 c34308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17884
  · exact u17885
  · exact u17886

def r34309 : Route 9 := (fun mask => (mask,id))

def c34309 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34309 : Upper (D 6) (R 6) [10,160,272,65,33] 13 := by
  apply FastRouting.sound _ _ [10,160,272,65,33] 13 (by decide) (choices 1) [2,4,64] r34309 c34309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17887
  · exact u17888
  · exact u17889

def b34310 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 162 276 73 50 101 69 197 325), lower := (rows 11 162 276 73 50 32 64 128 256), losses := [] }

theorem u34310 : Upper (D 6) (R 6) [10,160,272,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34311 : Route 9 := (fun mask => (mask,id))

def c34311 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34311 : Upper (D 6) (R 6) [10,160,272,65,36] 13 := by
  apply FastRouting.sound _ _ [10,160,272,65,36] 13 (by decide) (choices 1) [1,2,4,64] r34311 c34311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17890
  · exact u17891
  · exact u17892
  · exact u17893

def b34312 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 162 276 73 81 38 102 166 294), lower := (rows 11 162 276 73 81 32 64 128 256), losses := [] }

theorem u34312 : Upper (D 6) (R 6) [10,160,272,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34313 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 276 73 82 37 101 165 293), lower := (rows 11 162 276 73 82 32 64 128 256), losses := [] }

theorem u34313 : Upper (D 6) (R 6) [10,160,272,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34314 : Route 9 := (fun mask => (mask,id))

def c34314 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34314 : Upper (D 6) (R 6) [10,160,272,65,68] 13 := by
  apply FastRouting.sound _ _ [10,160,272,65,68] 13 (by decide) (choices 1) [1,2,4] r34314 c34314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17894
  · exact u17895
  · exact u17896

def r34315 : Route 9 := (fun mask => (mask,id))

def c34315 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34315 : Upper (D 6) (R 6) [10,160,272,65,96] 13 := by
  apply FastRouting.sound _ _ [10,160,272,65,96] 13 (by decide) (choices 1) [1,2,4] r34315 c34315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17897
  · exact u17898
  · exact u17899

def b34316 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 162 276 76 19 101 101 229 357), lower := (rows 11 162 276 76 19 32 64 128 256), losses := [] }

theorem u34316 : Upper (D 6) (R 6) [10,160,272,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34317 : Route 9 := (fun mask => (mask,id))

def c34317 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34317 : Upper (D 6) (R 6) [10,160,272,68,5] 13 := by
  apply FastRouting.sound _ _ [10,160,272,68,5] 13 (by decide) (choices 1) [1,2,64] r34317 c34317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17900
  · exact u17901
  · exact u17902

def r34318 : Route 9 := (fun mask => (mask,id))

def c34318 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34318 : Upper (D 6) (R 6) [10,160,272,68,6] 13 := by
  apply FastRouting.sound _ _ [10,160,272,68,6] 13 (by decide) (choices 1) [1,64] r34318 c34318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17903
  · exact u17904

def r34319 : Route 9 := (fun mask => (mask,id))

def c34319 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34319 : Upper (D 6) (R 6) [10,160,272,68,33] 13 := by
  apply FastRouting.sound _ _ [10,160,272,68,33] 13 (by decide) (choices 1) [1,2,4,64] r34319 c34319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17905
  · exact u17906
  · exact u17907
  · exact u17908

#print axioms u34319
end Delivery.IrregularNine14.P06
