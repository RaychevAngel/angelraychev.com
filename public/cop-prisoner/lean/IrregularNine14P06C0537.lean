import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0243
import IrregularNine14P06C0244

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b32220 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 19, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 50 388 104 19 101 69 197 325), lower := (rows 11 50 388 104 19 32 64 128 256), losses := [] }

theorem u32220 : Upper (D 6) (R 6) [10,48,384,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32221 : Route 9 := (fun mask => (mask,id))

def c32221 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32221 : Upper (D 6) (R 6) [10,48,384,96,5] 13 := by
  apply FastRouting.sound _ _ [10,48,384,96,5] 13 (by decide) (choices 1) [1,2,4,64] r32221 c32221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14594
  · exact u14595
  · exact u14596
  · exact u14597

def b32222 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 50 388 104 22 101 69 197 325), lower := (rows 11 50 388 104 22 32 64 128 256), losses := [] }

theorem u32222 : Upper (D 6) (R 6) [10,48,384,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32223 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 19, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 388 104 81 39 71 135 263), lower := (rows 11 50 388 104 81 32 64 128 256), losses := [] }

theorem u32223 : Upper (D 6) (R 6) [10,48,384,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32224 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 19, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 388 104 82 37 69 133 261), lower := (rows 11 50 388 104 82 32 64 128 256), losses := [] }

theorem u32224 : Upper (D 6) (R 6) [10,48,384,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32225 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 50 388 104 84 39 71 135 263), lower := (rows 11 50 388 104 84 32 64 128 256), losses := [] }

theorem u32225 : Upper (D 6) (R 6) [10,48,384,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32226 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 29, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 22 13 49 484 452 452 452), lower := (rows 11 98 22 13 49 32 64 128 256), losses := [] }

theorem u32226 : Upper (D 6) (R 6) [10,96,18,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32227 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 98 22 13 145 356 356 484 356), lower := (rows 11 98 22 13 145 32 64 128 256), losses := [] }

theorem u32227 : Upper (D 6) (R 6) [10,96,18,5,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32228 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 98 22 13 148 353 353 481 353), lower := (rows 11 98 22 13 148 32 64 128 256), losses := [] }

theorem u32228 : Upper (D 6) (R 6) [10,96,18,5,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32229 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 9, targets := 32 },{ cop := 2, region := 9, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 98 22 13 176 357 325 453 325), lower := (rows 11 98 22 13 176 32 64 128 256), losses := [] }

theorem u32229 : Upper (D 6) (R 6) [10,96,18,5,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32230 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 9, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 98 22 13 400 101 101 229 357), lower := (rows 11 98 22 13 400 32 64 128 256), losses := [] }

theorem u32230 : Upper (D 6) (R 6) [10,96,18,5,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32231 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 22 41 81 420 452 388 388), lower := (rows 11 98 22 41 81 32 64 128 256), losses := [] }

theorem u32231 : Upper (D 6) (R 6) [10,96,18,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32232 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 22 41 145 356 324 452 324), lower := (rows 11 98 22 41 145 32 64 128 256), losses := [] }

theorem u32232 : Upper (D 6) (R 6) [10,96,18,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32233 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 22 41 148 357 325 453 325), lower := (rows 11 98 22 41 148 32 64 128 256), losses := [] }

theorem u32233 : Upper (D 6) (R 6) [10,96,18,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32234 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 22 41 208 293 325 389 261), lower := (rows 11 98 22 41 208 32 64 128 256), losses := [] }

theorem u32234 : Upper (D 6) (R 6) [10,96,18,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32235 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 98 22 41 400 101 69 197 325), lower := (rows 11 98 22 41 400 32 64 128 256), losses := [] }

theorem u32235 : Upper (D 6) (R 6) [10,96,18,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32236 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 98 22 44 81 421 453 389 389), lower := (rows 11 98 22 44 81 32 64 128 256), losses := [] }

theorem u32236 : Upper (D 6) (R 6) [10,96,18,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32237 : Route 9 := (fun mask => (mask,id))

def c32237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32237 : Upper (D 6) (R 6) [10,96,18,36,129] 13 := by
  apply FastRouting.sound _ _ [10,96,18,36,129] 13 (by decide) (choices 1) [1,4,64,256] r32237 c32237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14598
  · exact u14599
  · exact u14600
  · exact u14601

def b32238 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 323, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 98 22 44 148 353 321 449 321), lower := (rows 11 98 22 44 148 32 64 128 256), losses := [] }

theorem u32238 : Upper (D 6) (R 6) [10,96,18,36,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32239 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 297, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 98 22 44 208 293 325 389 261), lower := (rows 11 98 22 44 208 32 64 128 256), losses := [] }

theorem u32239 : Upper (D 6) (R 6) [10,96,18,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32240 : Route 9 := (fun mask => (mask,id))

def c32240 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32240 : Upper (D 6) (R 6) [10,96,18,36,384] 13 := by
  apply FastRouting.sound _ _ [10,96,18,36,384] 13 (by decide) (choices 1) [1,4,64] r32240 c32240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14602
  · exact u14603
  · exact u14604

def b32241 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 98 22 104 145 293 325 389 261), lower := (rows 11 98 22 104 145 32 64 128 256), losses := [] }

theorem u32241 : Upper (D 6) (R 6) [10,96,18,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32242 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 98 22 104 148 293 325 389 261), lower := (rows 11 98 22 104 148 32 64 128 256), losses := [] }

theorem u32242 : Upper (D 6) (R 6) [10,96,18,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32243 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 98 22 104 400 37 69 133 261), lower := (rows 11 98 22 104 400 32 64 128 256), losses := [] }

theorem u32243 : Upper (D 6) (R 6) [10,96,18,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32244 : Route 9 := (fun mask => (mask,id))

def c32244 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32244 : Upper (D 6) (R 6) [10,96,18,129,257] 13 := by
  apply FastRouting.sound _ _ [10,96,18,129,257] 13 (by decide) (choices 1) [4,64] r32244 c32244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14605
  · exact u14606

theorem m32245_4 : Upper (D 6) (R 6) [10,96,18,129,260,4] 13 :=
  permutation_upper _ _ _ [10,96,18,129,260,1] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14607

def r32245 : Route 9 := (fun mask => (mask,id))

def c32245 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32245 : Upper (D 6) (R 6) [10,96,18,129,260] 13 := by
  apply FastRouting.sound _ _ [10,96,18,129,260] 13 (by decide) (choices 1) [1,4,64] r32245 c32245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14607
  · exact m32245_4
  · exact u14608

def r32246 : Route 9 := (fun mask => (mask,id))

def c32246 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32246 : Upper (D 6) (R 6) [10,96,18,129,288] 13 := by
  apply FastRouting.sound _ _ [10,96,18,129,288] 13 (by decide) (choices 1) [1,4,64] r32246 c32246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14609
  · exact u14610
  · exact u14611

theorem m32247_4 : Upper (D 6) (R 6) [10,96,18,132,257,4] 13 :=
  permutation_upper _ _ _ [10,96,18,132,257,1] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14612

def r32247 : Route 9 := (fun mask => (mask,id))

def c32247 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32247 : Upper (D 6) (R 6) [10,96,18,132,257] 13 := by
  apply FastRouting.sound _ _ [10,96,18,132,257] 13 (by decide) (choices 1) [1,4,64] r32247 c32247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14612
  · exact m32247_4
  · exact u14613

def r32248 : Route 9 := (fun mask => (mask,id))

def c32248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32248 : Upper (D 6) (R 6) [10,96,18,132,288] 13 := by
  apply FastRouting.sound _ _ [10,96,18,132,288] 13 (by decide) (choices 1) [1,4,64] r32248 c32248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14614
  · exact u14615
  · exact u14616

def b32249 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 169, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 98 22 168 336 37 69 133 261), lower := (rows 11 98 22 168 336 32 64 128 256), losses := [] }

theorem u32249 : Upper (D 6) (R 6) [10,96,18,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32250 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 29, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 25 22 484 452 452 452), lower := (rows 11 98 37 25 22 32 64 128 256), losses := [] }

theorem u32250 : Upper (D 6) (R 6) [10,96,33,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32251 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 25, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 37 25 82 420 452 388 388), lower := (rows 11 98 37 25 82 32 64 128 256), losses := [] }

theorem u32251 : Upper (D 6) (R 6) [10,96,33,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32252 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 0, region := 420, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 11 98 37 25 84 422 454 390 390), lower := (rows 11 98 37 25 84 32 64 128 256), losses := [] }

theorem u32252 : Upper (D 6) (R 6) [10,96,33,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32253 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 98 37 25 146 356 324 452 324), lower := (rows 11 98 37 25 146 32 64 128 256), losses := [] }

theorem u32253 : Upper (D 6) (R 6) [10,96,33,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32254 : Route 9 := (fun mask => (mask,id))

def c32254 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32254 : Upper (D 6) (R 6) [10,96,33,17,132] 13 := by
  apply FastRouting.sound _ _ [10,96,33,17,132] 13 (by decide) (choices 1) [2,4,64,256] r32254 c32254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14617
  · exact u14618
  · exact u14619
  · exact u14620

def b32255 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 0, region := 292, targets := 64 }], pairs := [(1,0),(2,6),(4,0)], upper := (rows 11 98 37 25 208 294 326 390 262), lower := (rows 11 98 37 25 208 32 64 128 256), losses := [] }

theorem u32255 : Upper (D 6) (R 6) [10,96,33,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32256 : Route 9 := (fun mask => (mask,id))

def c32256 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32256 : Upper (D 6) (R 6) [10,96,33,17,384] 13 := by
  apply FastRouting.sound _ _ [10,96,33,17,384] 13 (by decide) (choices 1) [2,4,64] r32256 c32256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14621
  · exact u14622
  · exact u14623

def b32257 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 29, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 28 19 484 452 452 452), lower := (rows 11 98 37 28 19 32 64 128 256), losses := [] }

theorem u32257 : Upper (D 6) (R 6) [10,96,33,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32258 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 11 98 37 28 21 482 450 450 450), lower := (rows 11 98 37 28 21 32 64 128 256), losses := [] }

theorem u32258 : Upper (D 6) (R 6) [10,96,33,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32259 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 29, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 28 22 481 449 449 449), lower := (rows 11 98 37 28 22 32 64 128 256), losses := [] }

theorem u32259 : Upper (D 6) (R 6) [10,96,33,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32260 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 420, targets := 64 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(2,6),(3,6)], upper := (rows 11 98 37 28 81 422 454 390 390), lower := (rows 11 98 37 28 81 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 21 24 16 33 0 129 257), good := (rows 431 34 421 28 445 32 0 128 256) }] }

theorem u32260 : Upper (D 6) (R 6) [10,96,33,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32261 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 11 98 37 28 82 421 453 389 389), lower := (rows 11 98 37 28 82 32 64 128 256), losses := [] }

theorem u32261 : Upper (D 6) (R 6) [10,96,33,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32262 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 98 37 28 84 419 451 387 387), lower := (rows 11 98 37 28 84 32 64 128 256), losses := [] }

theorem u32262 : Upper (D 6) (R 6) [10,96,33,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32263 : Route 9 := (fun mask => (mask,id))

def c32263 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32263 : Upper (D 6) (R 6) [10,96,33,20,129] 13 := by
  apply FastRouting.sound _ _ [10,96,33,20,129] 13 (by decide) (choices 1) [2,4,64,256] r32263 c32263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14624
  · exact u14625
  · exact u14626
  · exact u14627

def r32264 : Route 9 := (fun mask => (mask,id))

def c32264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u32264 : Upper (D 6) (R 6) [10,96,33,20,130] 13 := by
  apply FastRouting.sound _ _ [10,96,33,20,130] 13 (by decide) (choices 1) [1,4,64,256] r32264 c32264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14628
  · exact u14629
  · exact u14630
  · exact u14631

def b32265 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 98 37 28 148 355 323 451 323), lower := (rows 11 98 37 28 148 32 64 128 256), losses := [] }

theorem u32265 : Upper (D 6) (R 6) [10,96,33,20,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32266 : Route 9 := (fun mask => (mask,id))

def c32266 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32266 : Upper (D 6) (R 6) [10,96,33,20,192] 13 := by
  apply FastRouting.sound _ _ [10,96,33,20,192] 13 (by decide) (choices 1) [1,2,4,256] r32266 c32266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14632
  · exact u14633
  · exact u14634
  · exact u14635

def r32267 : Route 9 := (fun mask => (mask,id))

def c32267 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32267 : Upper (D 6) (R 6) [10,96,33,20,384] 13 := by
  apply FastRouting.sound _ _ [10,96,33,20,384] 13 (by decide) (choices 1) [1,2,4,64] r32267 c32267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14636
  · exact u14637
  · exact u14638
  · exact u14639

def b32268 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 16, targets := 36 },{ cop := 0, region := 436, targets := 64 }], pairs := [(2,6),(4,2),(4,5)], upper := (rows 11 98 37 76 19 436 468 404 404), lower := (rows 11 98 37 76 19 32 64 128 256), losses := [] }

theorem u32268 : Upper (D 6) (R 6) [10,96,33,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32269 : PairBound 9 := { available := 402, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 98 37 76 21 434 466 402 402), lower := (rows 11 98 37 76 21 32 64 128 256), losses := [] }

theorem u32269 : Upper (D 6) (R 6) [10,96,33,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32270 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 4, region := 457, targets := 32 }], pairs := [(0,5),(2,6),(4,6)], upper := (rows 11 98 37 76 22 433 465 401 401), lower := (rows 11 98 37 76 22 32 64 128 256), losses := [] }

theorem u32270 : Upper (D 6) (R 6) [10,96,33,68,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r32271 : Route 9 := (fun mask => (mask,id))

def c32271 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32271 : Upper (D 6) (R 6) [10,96,33,68,129] 13 := by
  apply FastRouting.sound _ _ [10,96,33,68,129] 13 (by decide) (choices 1) [2,4,16,256] r32271 c32271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14640
  · exact u14641
  · exact u14642
  · exact u14643

def r32272 : Route 9 := (fun mask => (mask,id))

def c32272 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32272 : Upper (D 6) (R 6) [10,96,33,68,130] 13 := by
  apply FastRouting.sound _ _ [10,96,33,68,130] 13 (by decide) (choices 1) [1,4,16,256] r32272 c32272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14644
  · exact u14645
  · exact u14646
  · exact u14647

def r32273 : Route 9 := (fun mask => (mask,id))

def c32273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32273 : Upper (D 6) (R 6) [10,96,33,68,132] 13 := by
  apply FastRouting.sound _ _ [10,96,33,68,132] 13 (by decide) (choices 1) [1,2,16,256] r32273 c32273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14648
  · exact u14649
  · exact u14650
  · exact u14651

def r32274 : Route 9 := (fun mask => (mask,id))

def c32274 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32274 : Upper (D 6) (R 6) [10,96,33,68,384] 13 := by
  apply FastRouting.sound _ _ [10,96,33,68,384] 13 (by decide) (choices 1) [1,2,4,16] r32274 c32274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14652
  · exact u14653
  · exact u14654
  · exact u14655

def b32275 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 25, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 98 37 88 19 420 452 388 388), lower := (rows 11 98 37 88 19 32 64 128 256), losses := [] }

theorem u32275 : Upper (D 6) (R 6) [10,96,33,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32276 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 98 37 88 21 422 454 390 390), lower := (rows 11 98 37 88 21 32 64 128 256), losses := [] }

theorem u32276 : Upper (D 6) (R 6) [10,96,33,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32277 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 4, region := 457, targets := 32 }], pairs := [(0,5),(2,6),(4,6)], upper := (rows 11 98 37 88 22 421 453 389 389), lower := (rows 11 98 37 88 22 32 64 128 256), losses := [] }

theorem u32277 : Upper (D 6) (R 6) [10,96,33,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32278 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 2, region := 322, targets := 1 }], pairs := [(1,0),(2,6),(4,6)], upper := (rows 11 98 37 88 145 294 326 390 262), lower := (rows 11 98 37 88 145 32 64 128 256), losses := [] }

theorem u32278 : Upper (D 6) (R 6) [10,96,33,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b32279 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 436, targets := 64 },{ cop := 0, region := 292, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 11 98 37 88 146 293 325 389 261), lower := (rows 11 98 37 88 146 32 64 128 256), losses := [] }

theorem u32279 : Upper (D 6) (R 6) [10,96,33,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b32279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u32279
end Delivery.IrregularNine14.P06
