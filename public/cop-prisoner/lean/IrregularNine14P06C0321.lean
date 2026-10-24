import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0096

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19260 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 134 292 74 112 33 71 135 263), lower := (rows 25 134 292 74 112 33 64 128 256), losses := [] }

theorem u19260 : Upper (D 6) (R 6) [24,132,288,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19261 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 422, targets := 64 },{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(1,6),(2,6)], upper := (rows 25 134 292 74 112 34 69 133 261), lower := (rows 25 134 292 74 112 34 64 128 256), losses := [] }

theorem u19261 : Upper (D 6) (R 6) [24,132,288,66,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19262 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 134 292 74 112 36 67 131 259), lower := (rows 25 134 292 74 112 36 64 128 256), losses := [] }

theorem u19262 : Upper (D 6) (R 6) [24,132,288,66,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19263 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 134 292 76 112 33 67 131 259), lower := (rows 25 134 292 76 112 33 64 128 256), losses := [] }

theorem u19263 : Upper (D 6) (R 6) [24,132,288,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19264 : Route 9 := (fun mask => (mask,id))

def c19264 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19264 : Upper (D 6) (R 6) [24,132,288,68,96,2] 13 := by
  apply FastRouting.sound _ _ [24,132,288,68,96,2] 13 (by decide) (choices 1) [1,2] r19264 c19264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5777
  · exact u5778

def b19265 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 7, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 162 292 11 21 34 68 196 324), lower := (rows 25 162 292 11 21 34 64 128 256), losses := [] }

theorem u19265 : Upper (D 6) (R 6) [24,160,288,3,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m19266_4 : Upper (D 6) (R 6) [24,160,288,3,5,64,4] 13 :=
  permutation_upper _ _ _ [24,160,288,3,5,64,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5779

def r19266 : Route 9 := (fun mask => (mask,id))

def c19266 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19266 : Upper (D 6) (R 6) [24,160,288,3,5,64] 13 := by
  apply FastRouting.sound _ _ [24,160,288,3,5,64] 13 (by decide) (choices 1) [2,4] r19266 c19266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5779
  · exact m19266_4

def b19267 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 7, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 162 292 11 81 34 68 196 324), lower := (rows 25 162 292 11 81 34 64 128 256), losses := [] }

theorem u19267 : Upper (D 6) (R 6) [24,160,288,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19268 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 8, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 162 292 11 81 36 70 198 326), lower := (rows 25 162 292 11 81 36 64 128 256), losses := [] }

theorem u19268 : Upper (D 6) (R 6) [24,160,288,3,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19269 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 5, region := 390, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 162 292 11 81 96 70 134 262), lower := (rows 25 162 292 11 81 96 64 128 256), losses := [] }

theorem u19269 : Upper (D 6) (R 6) [24,160,288,3,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19270 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 162 292 11 84 33 70 198 326), lower := (rows 25 162 292 11 84 33 64 128 256), losses := [] }

theorem u19270 : Upper (D 6) (R 6) [24,160,288,3,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19271 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 25 162 292 11 84 34 69 197 325), lower := (rows 25 162 292 11 84 34 64 128 256), losses := [] }

theorem u19271 : Upper (D 6) (R 6) [24,160,288,3,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19272 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 25 162 292 11 84 36 67 195 323), lower := (rows 25 162 292 11 84 36 64 128 256), losses := [] }

theorem u19272 : Upper (D 6) (R 6) [24,160,288,3,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19273 : Route 9 := (fun mask => (mask,id))

def c19273 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19273 : Upper (D 6) (R 6) [24,160,288,3,68,64] 13 := by
  apply FastRouting.sound _ _ [24,160,288,3,68,64] 13 (by decide) (choices 1) [1,2,4] r19273 c19273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5780
  · exact u5781
  · exact u5782

def b19274 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 162 292 14 81 33 70 198 326), lower := (rows 25 162 292 14 81 33 64 128 256), losses := [] }

theorem u19274 : Upper (D 6) (R 6) [24,160,288,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19275 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 81, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 162 292 14 81 34 69 197 325), lower := (rows 25 162 292 14 81 34 64 128 256), losses := [] }

theorem u19275 : Upper (D 6) (R 6) [24,160,288,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m19276_4 : Upper (D 6) (R 6) [24,160,288,6,65,64,4] 13 :=
  permutation_upper _ _ _ [24,160,288,6,65,64,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5784

def r19276 : Route 9 := (fun mask => (mask,id))

def c19276 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19276 : Upper (D 6) (R 6) [24,160,288,6,65,64] 13 := by
  apply FastRouting.sound _ _ [24,160,288,6,65,64] 13 (by decide) (choices 1) [1,2,4] r19276 c19276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5783
  · exact u5784
  · exact m19276_4

theorem m19277_4 : Upper (D 6) (R 6) [24,160,288,66,68,1,4] 13 :=
  permutation_upper _ _ _ [24,160,288,66,68,1,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5786

def r19277 : Route 9 := (fun mask => (mask,id))

def c19277 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19277 : Upper (D 6) (R 6) [24,160,288,66,68,1] 13 := by
  apply FastRouting.sound _ _ [24,160,288,66,68,1] 13 (by decide) (choices 1) [1,2,4] r19277 c19277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5785
  · exact u5786
  · exact m19277_4

def b19278 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 25 162 292 74 84 34 69 133 261), lower := (rows 25 162 292 74 84 34 64 128 256), losses := [] }

theorem u19278 : Upper (D 6) (R 6) [24,160,288,66,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19279 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 7, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 162 324 11 21 34 100 228 356), lower := (rows 25 162 324 11 21 34 64 128 256), losses := [] }

theorem u19279 : Upper (D 6) (R 6) [24,160,320,3,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19280 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 5, region := 194, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 162 324 11 21 36 98 226 354), lower := (rows 25 162 324 11 21 36 64 128 256), losses := [] }

theorem u19280 : Upper (D 6) (R 6) [24,160,320,3,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m19281_2 : Upper (D 6) (R 6) [24,160,320,3,5,64,2] 13 :=
  permutation_upper _ _ _ [24,160,320,3,5,4,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5788

theorem m19281_4 : Upper (D 6) (R 6) [24,160,320,3,5,64,4] 13 :=
  permutation_upper _ _ _ [24,160,320,3,5,2,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5787

def r19281 : Route 9 := (fun mask => (mask,id))

def c19281 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19281 : Upper (D 6) (R 6) [24,160,320,3,5,64] 13 := by
  apply FastRouting.sound _ _ [24,160,320,3,5,64] 13 (by decide) (choices 1) [2,4,32] r19281 c19281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m19281_2
  · exact m19281_4
  · exact u5789

def b19282 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 162 324 11 52 33 70 198 326), lower := (rows 25 162 324 11 52 33 64 128 256), losses := [] }

theorem u19282 : Upper (D 6) (R 6) [24,160,320,3,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19283 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 25 162 324 11 52 34 69 197 325), lower := (rows 25 162 324 11 52 34 64 128 256), losses := [] }

theorem u19283 : Upper (D 6) (R 6) [24,160,320,3,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19284 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 25 162 324 11 52 36 67 195 323), lower := (rows 25 162 324 11 52 36 64 128 256), losses := [] }

theorem u19284 : Upper (D 6) (R 6) [24,160,320,3,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19285 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 162 324 11 52 96 71 135 263), lower := (rows 25 162 324 11 52 96 64 128 256), losses := [] }

theorem u19285 : Upper (D 6) (R 6) [24,160,320,3,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19286 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 162 324 11 112 33 70 134 262), lower := (rows 25 162 324 11 112 33 64 128 256), losses := [] }

theorem u19286 : Upper (D 6) (R 6) [24,160,320,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19287 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 25 162 324 11 112 34 69 133 261), lower := (rows 25 162 324 11 112 34 64 128 256), losses := [] }

theorem u19287 : Upper (D 6) (R 6) [24,160,320,3,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19288 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 3, region := 324, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 25 162 324 11 112 36 71 135 263), lower := (rows 25 162 324 11 112 36 64 128 256), losses := [] }

theorem u19288 : Upper (D 6) (R 6) [24,160,320,3,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19289 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 49, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 162 324 14 49 33 70 198 326), lower := (rows 25 162 324 14 49 33 64 128 256), losses := [] }

theorem u19289 : Upper (D 6) (R 6) [24,160,320,6,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19290 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 25 162 324 14 49 34 69 197 325), lower := (rows 25 162 324 14 49 34 64 128 256), losses := [] }

theorem u19290 : Upper (D 6) (R 6) [24,160,320,6,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19291 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 25 162 324 14 49 36 67 195 323), lower := (rows 25 162 324 14 49 36 64 128 256), losses := [] }

theorem u19291 : Upper (D 6) (R 6) [24,160,320,6,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19292 : PairBound 9 := { available := 7, camps := [], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 162 324 14 49 96 71 135 263), lower := (rows 25 162 324 14 49 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 24 100 64 128 256), good := (rows 25 160 356 61 49 96 96 128 256) },{ target := 2, region := (rows 9 2 0 8 24 100 64 128 256), good := (rows 25 162 352 59 49 96 96 128 256) }] }

theorem u19292 : Upper (D 6) (R 6) [24,160,320,6,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19293 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 25 162 324 14 52 33 67 195 323), lower := (rows 25 162 324 14 52 33 64 128 256), losses := [] }

theorem u19293 : Upper (D 6) (R 6) [24,160,320,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19294 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 25 162 324 14 52 34 65 193 321), lower := (rows 25 162 324 14 52 34 64 128 256), losses := [] }

theorem u19294 : Upper (D 6) (R 6) [24,160,320,6,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19295 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 162 324 14 52 96 67 131 259), lower := (rows 25 162 324 14 52 96 64 128 256), losses := [] }

theorem u19295 : Upper (D 6) (R 6) [24,160,320,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19296 : Route 9 := (fun mask => (mask,id))

def c19296 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19296 : Upper (D 6) (R 6) [24,160,320,6,96,1] 13 := by
  apply FastRouting.sound _ _ [24,160,320,6,96,1] 13 (by decide) (choices 1) [1,2,4] r19296 c19296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5790
  · exact u5791
  · exact u5792

def b19297 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 25 162 324 14 112 34 69 133 261), lower := (rows 25 162 324 14 112 34 64 128 256), losses := [] }

theorem u19297 : Upper (D 6) (R 6) [24,160,320,6,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19298 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(0,1),(4,0),(4,1)], upper := (rows 25 162 324 14 112 36 67 131 259), lower := (rows 25 162 324 14 112 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 20 44 64 128 256), good := (rows 57 160 372 61 112 52 64 128 256) }] }

theorem u19298 : Upper (D 6) (R 6) [24,160,320,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19299 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 162 324 41 82 33 70 134 262), lower := (rows 25 162 324 41 82 33 64 128 256), losses := [] }

theorem u19299 : Upper (D 6) (R 6) [24,160,320,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19300 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 162 324 41 82 34 69 133 261), lower := (rows 25 162 324 41 82 34 64 128 256), losses := [] }

theorem u19300 : Upper (D 6) (R 6) [24,160,320,33,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19300 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19301 : Route 9 := (fun mask => (mask,id))

def c19301 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19301 : Upper (D 6) (R 6) [24,160,320,33,66,4] 13 := by
  apply FastRouting.sound _ _ [24,160,320,33,66,4] 13 (by decide) (choices 1) [1,2,4] r19301 c19301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5793
  · exact u5794
  · exact u5795

def r19302 : Route 9 := (fun mask => (mask,id))

def c19302 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19302 : Upper (D 6) (R 6) [24,160,320,36,66,1] 13 := by
  apply FastRouting.sound _ _ [24,160,320,36,66,1] 13 (by decide) (choices 1) [1,2,4] r19302 c19302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5796
  · exact u5797
  · exact u5798

def b19303 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 25 162 324 44 82 34 69 133 261), lower := (rows 25 162 324 44 82 34 64 128 256), losses := [] }

theorem u19303 : Upper (D 6) (R 6) [24,160,320,36,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19304 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 162 324 44 82 36 67 131 259), lower := (rows 25 162 324 44 82 36 64 128 256), losses := [] }

theorem u19304 : Upper (D 6) (R 6) [24,160,320,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19305 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 67 44 25 146 36 324 452 324), lower := (rows 35 67 44 25 146 36 64 128 256), losses := [] }

theorem u19305 : Upper (D 6) (R 6) [34,65,40,17,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19306 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 25 146 96 324 388 260), lower := (rows 35 67 44 25 146 96 64 128 256), losses := [] }

theorem u19306 : Upper (D 6) (R 6) [34,65,40,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19307 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 356, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 44 25 146 288 68 196 324), lower := (rows 35 67 44 25 146 288 64 128 256), losses := [] }

theorem u19307 : Upper (D 6) (R 6) [34,65,40,17,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19307 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19308 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 25 148 34 324 452 324), lower := (rows 35 67 44 25 148 34 64 128 256), losses := [] }

theorem u19308 : Upper (D 6) (R 6) [34,65,40,17,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19309 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 25 148 36 322 450 322), lower := (rows 35 67 44 25 148 36 64 128 256), losses := [] }

theorem u19309 : Upper (D 6) (R 6) [34,65,40,17,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19310 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 25 148 96 326 390 262), lower := (rows 35 67 44 25 148 96 64 128 256), losses := [] }

theorem u19310 : Upper (D 6) (R 6) [34,65,40,17,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19311 : Route 9 := (fun mask => (mask,id))

def c19311 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19311 : Upper (D 6) (R 6) [34,65,40,17,132,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,17,132,256] 13 (by decide) (choices 1) [2,4] r19311 c19311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5799
  · exact u5800

def b19312 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 25 208 34 324 388 260), lower := (rows 35 67 44 25 208 34 64 128 256), losses := [] }

theorem u19312 : Upper (D 6) (R 6) [34,65,40,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19313 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 25 208 36 326 390 262), lower := (rows 35 67 44 25 208 36 64 128 256), losses := [] }

theorem u19313 : Upper (D 6) (R 6) [34,65,40,17,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19314 : Route 9 := (fun mask => (mask,id))

def c19314 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19314 : Upper (D 6) (R 6) [34,65,40,17,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,17,192,256] 13 (by decide) (choices 1) [2,4] r19314 c19314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5801
  · exact u5802

def b19315 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 25 400 34 68 196 324), lower := (rows 35 67 44 25 400 34 64 128 256), losses := [] }

theorem u19315 : Upper (D 6) (R 6) [34,65,40,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19316 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 25 400 36 70 198 326), lower := (rows 35 67 44 25 400 36 64 128 256), losses := [] }

theorem u19316 : Upper (D 6) (R 6) [34,65,40,17,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19317 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 25 400 96 70 134 262), lower := (rows 35 67 44 25 400 96 64 128 256), losses := [] }

theorem u19317 : Upper (D 6) (R 6) [34,65,40,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19318 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 67 44 26 145 36 324 452 324), lower := (rows 35 67 44 26 145 36 64 128 256), losses := [] }

theorem u19318 : Upper (D 6) (R 6) [34,65,40,18,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19319 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 26 145 96 324 388 260), lower := (rows 35 67 44 26 145 96 64 128 256), losses := [] }

theorem u19319 : Upper (D 6) (R 6) [34,65,40,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u19319
end Delivery.IrregularNine14.P06
