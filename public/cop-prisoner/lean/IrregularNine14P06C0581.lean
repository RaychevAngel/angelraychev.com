import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0308
import IrregularNine14P06C0309

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34860 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 35 164 73 336 38 70 134 262), lower := (rows 25 35 164 73 336 32 64 128 256), losses := [] }

theorem u34860 : Upper (D 6) (R 6) [24,33,160,65,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34861 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 35 164 74 82 293 325 389 261), lower := (rows 25 35 164 74 82 32 64 128 256), losses := [] }

theorem u34861 : Upper (D 6) (R 6) [24,33,160,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34862 : Route 9 := (fun mask => (mask,id))

def c34862 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34862 : Upper (D 6) (R 6) [24,33,160,66,68] 13 := by
  apply FastRouting.sound _ _ [24,33,160,66,68] 13 (by decide) (choices 1) [1,2,4,256] r34862 c34862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18507
  · exact u18508
  · exact u18509
  · exact u18510

def r34863 : Route 9 := (fun mask => (mask,id))

def c34863 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34863 : Upper (D 6) (R 6) [24,33,160,66,257] 13 := by
  apply FastRouting.sound _ _ [24,33,160,66,257] 13 (by decide) (choices 1) [2,4,64] r34863 c34863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18511
  · exact u18512
  · exact u18513

def r34864 : Route 9 := (fun mask => (mask,id))

def c34864 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34864 : Upper (D 6) (R 6) [24,33,160,66,258] 13 := by
  apply FastRouting.sound _ _ [24,33,160,66,258] 13 (by decide) (choices 1) [1,4,64] r34864 c34864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18514
  · exact u18515
  · exact u18516

def r34865 : Route 9 := (fun mask => (mask,id))

def c34865 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34865 : Upper (D 6) (R 6) [24,33,160,66,260] 13 := by
  apply FastRouting.sound _ _ [24,33,160,66,260] 13 (by decide) (choices 1) [1,2,4,64] r34865 c34865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18517
  · exact u18518
  · exact u18519
  · exact u18520

def r34866 : Route 9 := (fun mask => (mask,id))

def c34866 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34866 : Upper (D 6) (R 6) [24,33,160,66,320] 13 := by
  apply FastRouting.sound _ _ [24,33,160,66,320] 13 (by decide) (choices 1) [1,2,4] r34866 c34866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18521
  · exact u18522
  · exact u18523

def b34867 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 17, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 35 164 76 84 291 323 387 259), lower := (rows 25 35 164 76 84 32 64 128 256), losses := [] }

theorem u34867 : Upper (D 6) (R 6) [24,33,160,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34868 : Route 9 := (fun mask => (mask,id))

def c34868 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34868 : Upper (D 6) (R 6) [24,33,160,68,257] 13 := by
  apply FastRouting.sound _ _ [24,33,160,68,257] 13 (by decide) (choices 1) [2,4,64] r34868 c34868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18524
  · exact u18525
  · exact u18526

def r34869 : Route 9 := (fun mask => (mask,id))

def c34869 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34869 : Upper (D 6) (R 6) [24,33,160,68,258] 13 := by
  apply FastRouting.sound _ _ [24,33,160,68,258] 13 (by decide) (choices 1) [1,2,4,64] r34869 c34869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18527
  · exact u18528
  · exact u18529
  · exact u18530

def r34870 : Route 9 := (fun mask => (mask,id))

def c34870 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34870 : Upper (D 6) (R 6) [24,33,160,68,260] 13 := by
  apply FastRouting.sound _ _ [24,33,160,68,260] 13 (by decide) (choices 1) [1,2,64] r34870 c34870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18531
  · exact u18532
  · exact u18533

def r34871 : Route 9 := (fun mask => (mask,id))

def c34871 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34871 : Upper (D 6) (R 6) [24,33,160,68,320] 13 := by
  apply FastRouting.sound _ _ [24,33,160,68,320] 13 (by decide) (choices 1) [1,2,4] r34871 c34871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18534
  · exact u18535
  · exact u18536

def b34872 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 35 196 11 22 356 356 484 356), lower := (rows 25 35 196 11 22 32 64 128 256), losses := [] }

theorem u34872 : Upper (D 6) (R 6) [24,33,192,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34873 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 25 35 196 11 52 358 326 454 326), lower := (rows 25 35 196 11 52 32 64 128 256), losses := [] }

theorem u34873 : Upper (D 6) (R 6) [24,33,192,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34874 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 35 196 11 82 292 356 420 292), lower := (rows 25 35 196 11 82 32 64 128 256), losses := [] }

theorem u34874 : Upper (D 6) (R 6) [24,33,192,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34875 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 25 35 196 11 112 294 326 390 262), lower := (rows 25 35 196 11 112 32 64 128 256), losses := [] }

theorem u34875 : Upper (D 6) (R 6) [24,33,192,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34876 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 35 196 11 274 100 100 228 356), lower := (rows 25 35 196 11 274 32 64 128 256), losses := [] }

theorem u34876 : Upper (D 6) (R 6) [24,33,192,3,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34877 : PairBound 9 := { available := 102, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 196 11 276 102 102 230 358), lower := (rows 25 35 196 11 276 32 64 128 256), losses := [] }

theorem u34877 : Upper (D 6) (R 6) [24,33,192,3,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34878 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 25 35 196 11 304 102 70 198 326), lower := (rows 25 35 196 11 304 32 64 128 256), losses := [] }

theorem u34878 : Upper (D 6) (R 6) [24,33,192,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34879 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 196 11 336 38 102 166 294), lower := (rows 25 35 196 11 336 32 64 128 256), losses := [] }

theorem u34879 : Upper (D 6) (R 6) [24,33,192,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34880 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 35 196 13 22 354 354 482 354), lower := (rows 25 35 196 13 22 32 64 128 256), losses := [] }

theorem u34880 : Upper (D 6) (R 6) [24,33,192,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34881 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 25 35 196 13 50 358 326 454 326), lower := (rows 25 35 196 13 50 32 64 128 256), losses := [] }

theorem u34881 : Upper (D 6) (R 6) [24,33,192,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34882 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 9, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 35 196 13 52 354 322 450 322), lower := (rows 25 35 196 13 52 32 64 128 256), losses := [] }

theorem u34882 : Upper (D 6) (R 6) [24,33,192,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34883 : PairBound 9 := { available := 294, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 290, targets := 64 }], pairs := [(1,6),(2,0),(4,0)], upper := (rows 25 35 196 13 82 294 358 422 294), lower := (rows 25 35 196 13 82 32 64 128 256), losses := [] }

theorem u34883 : Upper (D 6) (R 6) [24,33,192,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34884 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 25, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 35 196 13 84 290 354 418 290), lower := (rows 25 35 196 13 84 32 64 128 256), losses := [] }

theorem u34884 : Upper (D 6) (R 6) [24,33,192,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34885 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 452, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 35 196 13 112 294 326 390 262), lower := (rows 25 35 196 13 112 32 64 128 256), losses := [] }

theorem u34885 : Upper (D 6) (R 6) [24,33,192,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34886 : Route 9 := (fun mask => (mask,id))

def c34886 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34886 : Upper (D 6) (R 6) [24,33,192,5,258] 13 := by
  apply FastRouting.sound _ _ [24,33,192,5,258] 13 (by decide) (choices 1) [2,4,64] r34886 c34886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18537
  · exact u18538
  · exact u18539

def b34887 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 35 196 13 276 98 98 226 354), lower := (rows 25 35 196 13 276 32 64 128 256), losses := [] }

theorem u34887 : Upper (D 6) (R 6) [24,33,192,5,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34888 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 196, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 35 196 13 304 102 70 198 326), lower := (rows 25 35 196 13 304 32 64 128 256), losses := [] }

theorem u34888 : Upper (D 6) (R 6) [24,33,192,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34889 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(4,0)], upper := (rows 25 35 196 13 336 38 102 166 294), lower := (rows 25 35 196 13 336 32 64 128 256), losses := [] }

theorem u34889 : Upper (D 6) (R 6) [24,33,192,5,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34890 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 17, targets := 96 }], pairs := [(0,5),(0,6),(4,5)], upper := (rows 25 35 196 14 22 353 353 481 353), lower := (rows 25 35 196 14 22 32 64 128 256), losses := [] }

theorem u34890 : Upper (D 6) (R 6) [24,33,192,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34891 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 1, region := 16, targets := 4 }], pairs := [(2,0),(3,0),(4,2)], upper := (rows 25 35 196 14 49 358 326 454 326), lower := (rows 25 35 196 14 49 32 64 128 256), losses := [] }

theorem u34891 : Upper (D 6) (R 6) [24,33,192,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34892 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 25 35 196 14 50 357 325 453 325), lower := (rows 25 35 196 14 50 32 64 128 256), losses := [] }

theorem u34892 : Upper (D 6) (R 6) [24,33,192,6,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34893 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 196 14 52 355 323 451 323), lower := (rows 25 35 196 14 52 32 64 128 256), losses := [] }

theorem u34893 : Upper (D 6) (R 6) [24,33,192,6,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34894 : PairBound 9 := { available := 294, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 25 35 196 14 81 294 358 422 294), lower := (rows 25 35 196 14 81 32 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 8 16 40 0 136 264), good := (rows 443 35 132 430 19 32 0 128 256) }] }

theorem u34894 : Upper (D 6) (R 6) [24,33,192,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34895 : Route 9 := (fun mask => (mask,id))

def c34895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34895 : Upper (D 6) (R 6) [24,33,192,6,66] 13 := by
  apply FastRouting.sound _ _ [24,33,192,6,66] 13 (by decide) (choices 1) [1,4,256] r34895 c34895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18540
  · exact u18541
  · exact u18542

def b34896 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 25 35 196 14 84 291 355 419 291), lower := (rows 25 35 196 14 84 32 64 128 256), losses := [] }

theorem u34896 : Upper (D 6) (R 6) [24,33,192,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34897 : Route 9 := (fun mask => (mask,id))

def c34897 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34897 : Upper (D 6) (R 6) [24,33,192,6,96] 13 := by
  apply FastRouting.sound _ _ [24,33,192,6,96] 13 (by decide) (choices 1) [1,2,4,256] r34897 c34897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18543
  · exact u18544
  · exact u18545
  · exact u18546

def r34898 : Route 9 := (fun mask => (mask,id))

def c34898 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34898 : Upper (D 6) (R 6) [24,33,192,6,257] 13 := by
  apply FastRouting.sound _ _ [24,33,192,6,257] 13 (by decide) (choices 1) [2,4,64] r34898 c34898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18547
  · exact u18548
  · exact u18549

def r34899 : Route 9 := (fun mask => (mask,id))

def c34899 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34899 : Upper (D 6) (R 6) [24,33,192,6,258] 13 := by
  apply FastRouting.sound _ _ [24,33,192,6,258] 13 (by decide) (choices 1) [1,4,64] r34899 c34899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18550
  · exact u18551
  · exact u18552

def r34900 : Route 9 := (fun mask => (mask,id))

def c34900 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34900 : Upper (D 6) (R 6) [24,33,192,6,260] 13 := by
  apply FastRouting.sound _ _ [24,33,192,6,260] 13 (by decide) (choices 1) [1,2,64] r34900 c34900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18553
  · exact u18554
  · exact u18555

def r34901 : Route 9 := (fun mask => (mask,id))

def c34901 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34901 : Upper (D 6) (R 6) [24,33,192,6,288] 13 := by
  apply FastRouting.sound _ _ [24,33,192,6,288] 13 (by decide) (choices 1) [1,2,4,64] r34901 c34901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18556
  · exact u18557
  · exact u18558
  · exact u18559

def r34902 : Route 9 := (fun mask => (mask,id))

def c34902 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34902 : Upper (D 6) (R 6) [24,33,192,6,320] 13 := by
  apply FastRouting.sound _ _ [24,33,192,6,320] 13 (by decide) (choices 1) [1,2,4] r34902 c34902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18560
  · exact u18561
  · exact u18562

def b34903 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 196 41 82 294 326 390 262), lower := (rows 25 35 196 41 82 32 64 128 256), losses := [] }

theorem u34903 : Upper (D 6) (R 6) [24,33,192,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34904 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 196 41 274 102 70 198 326), lower := (rows 25 35 196 41 274 32 64 128 256), losses := [] }

theorem u34904 : Upper (D 6) (R 6) [24,33,192,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34905 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 196 41 276 102 70 198 326), lower := (rows 25 35 196 41 276 32 64 128 256), losses := [] }

theorem u34905 : Upper (D 6) (R 6) [24,33,192,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34906 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 196 41 336 38 70 134 262), lower := (rows 25 35 196 41 336 32 64 128 256), losses := [] }

theorem u34906 : Upper (D 6) (R 6) [24,33,192,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34907 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 196 42 81 294 326 390 262), lower := (rows 25 35 196 42 81 32 64 128 256), losses := [] }

theorem u34907 : Upper (D 6) (R 6) [24,33,192,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34908 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 196 42 82 293 325 389 261), lower := (rows 25 35 196 42 82 32 64 128 256), losses := [] }

theorem u34908 : Upper (D 6) (R 6) [24,33,192,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34909 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 196 42 273 102 70 198 326), lower := (rows 25 35 196 42 273 32 64 128 256), losses := [] }

theorem u34909 : Upper (D 6) (R 6) [24,33,192,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34910 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 196 42 274 101 69 197 325), lower := (rows 25 35 196 42 274 32 64 128 256), losses := [] }

theorem u34910 : Upper (D 6) (R 6) [24,33,192,34,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34911 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 196 42 276 103 71 199 327), lower := (rows 25 35 196 42 276 32 64 128 256), losses := [] }

theorem u34911 : Upper (D 6) (R 6) [24,33,192,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34912 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 196 42 336 39 71 135 263), lower := (rows 25 35 196 42 336 32 64 128 256), losses := [] }

theorem u34912 : Upper (D 6) (R 6) [24,33,192,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34913 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 1, region := 452, targets := 32 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 25 35 196 44 81 294 326 390 262), lower := (rows 25 35 196 44 81 32 64 128 256), losses := [] }

theorem u34913 : Upper (D 6) (R 6) [24,33,192,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34914 : Route 9 := (fun mask => (mask,id))

def c34914 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34914 : Upper (D 6) (R 6) [24,33,192,36,66] 13 := by
  apply FastRouting.sound _ _ [24,33,192,36,66] 13 (by decide) (choices 1) [1,2,4,256] r34914 c34914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18563
  · exact u18564
  · exact u18565
  · exact u18566

def b34915 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 25 35 196 44 84 291 323 387 259), lower := (rows 25 35 196 44 84 32 64 128 256), losses := [] }

theorem u34915 : Upper (D 6) (R 6) [24,33,192,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34916 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 1, region := 196, targets := 32 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 25 35 196 44 273 102 70 198 326), lower := (rows 25 35 196 44 273 32 64 128 256), losses := [] }

theorem u34916 : Upper (D 6) (R 6) [24,33,192,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34917 : Route 9 := (fun mask => (mask,id))

def c34917 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34917 : Upper (D 6) (R 6) [24,33,192,36,258] 13 := by
  apply FastRouting.sound _ _ [24,33,192,36,258] 13 (by decide) (choices 1) [1,2,4,64] r34917 c34917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18567
  · exact u18568
  · exact u18569
  · exact u18570

def b34918 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 25 35 196 44 276 99 67 195 323), lower := (rows 25 35 196 44 276 32 64 128 256), losses := [] }

theorem u34918 : Upper (D 6) (R 6) [24,33,192,36,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34919 : Route 9 := (fun mask => (mask,id))

def c34919 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34919 : Upper (D 6) (R 6) [24,33,192,36,320] 13 := by
  apply FastRouting.sound _ _ [24,33,192,36,320] 13 (by decide) (choices 1) [1,2,4] r34919 c34919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18571
  · exact u18572
  · exact u18573

#print axioms u34919
end Delivery.IrregularNine14.P06
