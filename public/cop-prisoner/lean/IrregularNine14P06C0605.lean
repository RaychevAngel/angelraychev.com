import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0344
import IrregularNine14P06C0345

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r36300 : Route 9 := (fun mask => (mask,id))

def c36300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36300 : Upper (D 6) (R 6) [34,68,160,65,258] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,258] 13 (by decide) (choices 1) [1,4,8,16] r36300 c36300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20679
  · exact u20680
  · exact u20681
  · exact u20682

def r36301 : Route 9 := (fun mask => (mask,id))

def c36301 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36301 : Upper (D 6) (R 6) [34,68,160,65,260] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,260] 13 (by decide) (choices 1) [1,2,8,16] r36301 c36301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20683
  · exact u20684
  · exact u20685
  · exact u20686

def r36302 : Route 9 := (fun mask => (mask,id))

def c36302 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36302 : Upper (D 6) (R 6) [34,68,160,65,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65,264] 13 (by decide) (choices 1) [1,2,4,16] r36302 c36302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20687
  · exact u20688
  · exact u20689
  · exact u20690

def b36303 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 70 164 74 273 61 93 157 285), lower := (rows 35 70 164 74 273 32 64 128 256), losses := [] }

theorem u36303 : Upper (D 6) (R 6) [34,68,160,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36304 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 70 164 74 276 57 89 153 281), lower := (rows 35 70 164 74 276 32 64 128 256), losses := [] }

theorem u36304 : Upper (D 6) (R 6) [34,68,160,66,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36305 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 70 164 74 280 53 85 149 277), lower := (rows 35 70 164 74 280 32 64 128 256), losses := [] }

theorem u36305 : Upper (D 6) (R 6) [34,68,160,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36306 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 35 70 164 76 273 59 91 155 283), lower := (rows 35 70 164 76 273 32 64 128 256), losses := [] }

theorem u36306 : Upper (D 6) (R 6) [34,68,160,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36307 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 35 70 164 76 274 57 89 153 281), lower := (rows 35 70 164 76 274 32 64 128 256), losses := [] }

theorem u36307 : Upper (D 6) (R 6) [34,68,160,68,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36308 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 8, targets := 33 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 35 70 164 76 280 51 83 147 275), lower := (rows 35 70 164 76 280 32 64 128 256), losses := [] }

theorem u36308 : Upper (D 6) (R 6) [34,68,160,68,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36309 : Route 9 := (fun mask => (mask,id))

def c36309 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36309 : Upper (D 6) (R 6) [34,68,160,80,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,257] 13 (by decide) (choices 1) [1,2,4,8] r36309 c36309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20691
  · exact u20692
  · exact u20693
  · exact u20694

def r36310 : Route 9 := (fun mask => (mask,id))

def c36310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36310 : Upper (D 6) (R 6) [34,68,160,80,258] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,258] 13 (by decide) (choices 1) [1,4,8] r36310 c36310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20695
  · exact u20696
  · exact u20697

def r36311 : Route 9 := (fun mask => (mask,id))

def c36311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36311 : Upper (D 6) (R 6) [34,68,160,80,260] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,260] 13 (by decide) (choices 1) [1,2,8] r36311 c36311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20698
  · exact u20699
  · exact u20700

def r36312 : Route 9 := (fun mask => (mask,id))

def c36312 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36312 : Upper (D 6) (R 6) [34,68,160,80,264] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80,264] 13 (by decide) (choices 1) [1,2,4] r36312 c36312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20701
  · exact u20702
  · exact u20703

def b36313 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 388 11 21 120 120 248 376), lower := (rows 35 70 388 11 21 32 64 128 256), losses := [] }

theorem u36313 : Upper (D 6) (R 6) [34,68,384,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36314 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 388 11 25 116 116 244 372), lower := (rows 35 70 388 11 25 32 64 128 256), losses := [] }

theorem u36314 : Upper (D 6) (R 6) [34,68,384,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36315 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 388 11 28 113 113 241 369), lower := (rows 35 70 388 11 28 32 64 128 256), losses := [] }

theorem u36315 : Upper (D 6) (R 6) [34,68,384,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36316 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 388 11 52 121 89 217 345), lower := (rows 35 70 388 11 52 32 64 128 256), losses := [] }

theorem u36316 : Upper (D 6) (R 6) [34,68,384,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36317 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 70 388 11 56 117 85 213 341), lower := (rows 35 70 388 11 56 32 64 128 256), losses := [] }

theorem u36317 : Upper (D 6) (R 6) [34,68,384,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36318 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 388 11 81 60 124 188 316), lower := (rows 35 70 388 11 81 32 64 128 256), losses := [] }

theorem u36318 : Upper (D 6) (R 6) [34,68,384,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36319 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 388 11 88 53 117 181 309), lower := (rows 35 70 388 11 88 32 64 128 256), losses := [] }

theorem u36319 : Upper (D 6) (R 6) [34,68,384,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36320 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 388 11 112 61 93 157 285), lower := (rows 35 70 388 11 112 32 64 128 256), losses := [] }

theorem u36320 : Upper (D 6) (R 6) [34,68,384,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36321 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 35 70 388 13 25 114 114 242 370), lower := (rows 35 70 388 13 25 32 64 128 256), losses := [] }

theorem u36321 : Upper (D 6) (R 6) [34,68,384,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36322 : Route 9 := (fun mask => (mask,id))

def c36322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36322 : Upper (D 6) (R 6) [34,68,384,5,10] 13 := by
  apply FastRouting.sound _ _ [34,68,384,5,10] 13 (by decide) (choices 1) [1,16,64] r36322 c36322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20704
  · exact u20705
  · exact u20706

def b36323 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 70 388 13 49 122 90 218 346), lower := (rows 35 70 388 13 49 32 64 128 256), losses := [] }

theorem u36323 : Upper (D 6) (R 6) [34,68,384,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36324 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 70 388 13 50 121 89 217 345), lower := (rows 35 70 388 13 50 32 64 128 256), losses := [] }

theorem u36324 : Upper (D 6) (R 6) [34,68,384,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36325 : Route 9 := (fun mask => (mask,id))

def c36325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36325 : Upper (D 6) (R 6) [34,68,384,5,40] 13 := by
  apply FastRouting.sound _ _ [34,68,384,5,40] 13 (by decide) (choices 1) [1,2,16,64] r36325 c36325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20707
  · exact u20708
  · exact u20709
  · exact u20710

def r36326 : Route 9 := (fun mask => (mask,id))

def c36326 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36326 : Upper (D 6) (R 6) [34,68,384,5,65] 13 := by
  apply FastRouting.sound _ _ [34,68,384,5,65] 13 (by decide) (choices 1) [2,8,16] r36326 c36326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20711
  · exact u20712
  · exact u20713

def b36327 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 388 13 82 57 121 185 313), lower := (rows 35 70 388 13 82 32 64 128 256), losses := [] }

theorem u36327 : Upper (D 6) (R 6) [34,68,384,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36328 : Route 9 := (fun mask => (mask,id))

def c36328 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36328 : Upper (D 6) (R 6) [34,68,384,5,72] 13 := by
  apply FastRouting.sound _ _ [34,68,384,5,72] 13 (by decide) (choices 1) [1,2,16] r36328 c36328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20714
  · exact u20715
  · exact u20716

def r36329 : Route 9 := (fun mask => (mask,id))

def c36329 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36329 : Upper (D 6) (R 6) [34,68,384,5,96] 13 := by
  apply FastRouting.sound _ _ [34,68,384,5,96] 13 (by decide) (choices 1) [1,2,8,16] r36329 c36329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20717
  · exact u20718
  · exact u20719
  · exact u20720

def b36330 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 388 14 25 113 113 241 369), lower := (rows 35 70 388 14 25 32 64 128 256), losses := [] }

theorem u36330 : Upper (D 6) (R 6) [34,68,384,6,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36331 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 388 14 56 113 81 209 337), lower := (rows 35 70 388 14 56 32 64 128 256), losses := [] }

theorem u36331 : Upper (D 6) (R 6) [34,68,384,6,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36332 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 388 14 81 57 121 185 313), lower := (rows 35 70 388 14 81 32 64 128 256), losses := [] }

theorem u36332 : Upper (D 6) (R 6) [34,68,384,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36333 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 388 14 88 49 113 177 305), lower := (rows 35 70 388 14 88 32 64 128 256), losses := [] }

theorem u36333 : Upper (D 6) (R 6) [34,68,384,6,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36334 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 388 14 112 57 89 153 281), lower := (rows 35 70 388 14 112 32 64 128 256), losses := [] }

theorem u36334 : Upper (D 6) (R 6) [34,68,384,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36335 : PairBound 9 := { available := 102, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 70 388 25 25 102 102 230 358), lower := (rows 35 70 388 25 25 32 64 128 256), losses := [] }

theorem u36335 : Upper (D 6) (R 6) [34,68,384,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36336 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 388 25 26 101 101 229 357), lower := (rows 35 70 388 25 26 32 64 128 256), losses := [] }

theorem u36336 : Upper (D 6) (R 6) [34,68,384,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36337 : Route 9 := (fun mask => (mask,id))

def c36337 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36337 : Upper (D 6) (R 6) [34,68,384,17,12] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,12] 13 (by decide) (choices 1) [1,2,64] r36337 c36337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20721
  · exact u20722
  · exact u20723

def b36338 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 388 25 49 110 78 206 334), lower := (rows 35 70 388 25 49 32 64 128 256), losses := [] }

theorem u36338 : Upper (D 6) (R 6) [34,68,384,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36339 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 70 388 25 50 109 77 205 333), lower := (rows 35 70 388 25 50 32 64 128 256), losses := [] }

theorem u36339 : Upper (D 6) (R 6) [34,68,384,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36340 : Route 9 := (fun mask => (mask,id))

def c36340 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36340 : Upper (D 6) (R 6) [34,68,384,17,36] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,36] 13 (by decide) (choices 1) [1,2,8,64] r36340 c36340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20724
  · exact u20725
  · exact u20726
  · exact u20727

def b36341 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 388 25 56 103 71 199 327), lower := (rows 35 70 388 25 56 32 64 128 256), losses := [] }

theorem u36341 : Upper (D 6) (R 6) [34,68,384,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36342 : PairBound 9 := { available := 46, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 70 388 25 81 46 110 174 302), lower := (rows 35 70 388 25 81 32 64 128 256), losses := [] }

theorem u36342 : Upper (D 6) (R 6) [34,68,384,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36343 : PairBound 9 := { available := 45, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 388 25 82 45 109 173 301), lower := (rows 35 70 388 25 82 32 64 128 256), losses := [] }

theorem u36343 : Upper (D 6) (R 6) [34,68,384,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36344 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 388 25 84 43 107 171 299), lower := (rows 35 70 388 25 84 32 64 128 256), losses := [] }

theorem u36344 : Upper (D 6) (R 6) [34,68,384,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36345 : Route 9 := (fun mask => (mask,id))

def c36345 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36345 : Upper (D 6) (R 6) [34,68,384,17,72] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,72] 13 (by decide) (choices 1) [1,2,4] r36345 c36345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20728
  · exact u20729
  · exact u20730

def r36346 : Route 9 := (fun mask => (mask,id))

def c36346 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36346 : Upper (D 6) (R 6) [34,68,384,17,96] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17,96] 13 (by decide) (choices 1) [1,2,4,8] r36346 c36346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20731
  · exact u20732
  · exact u20733
  · exact u20734

def b36347 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 70 388 26 28 97 97 225 353), lower := (rows 35 70 388 26 28 32 64 128 256), losses := [] }

theorem u36347 : Upper (D 6) (R 6) [34,68,384,18,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36348 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 70 388 26 49 109 77 205 333), lower := (rows 35 70 388 26 49 32 64 128 256), losses := [] }

theorem u36348 : Upper (D 6) (R 6) [34,68,384,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36349 : Route 9 := (fun mask => (mask,id))

def c36349 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36349 : Upper (D 6) (R 6) [34,68,384,18,36] 13 := by
  apply FastRouting.sound _ _ [34,68,384,18,36] 13 (by decide) (choices 1) [1,8,64] r36349 c36349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20735
  · exact u20736
  · exact u20737

def b36350 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 70 388 26 56 101 69 197 325), lower := (rows 35 70 388 26 56 32 64 128 256), losses := [] }

theorem u36350 : Upper (D 6) (R 6) [34,68,384,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36351 : Route 9 := (fun mask => (mask,id))

def c36351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36351 : Upper (D 6) (R 6) [34,68,384,18,65] 13 := by
  apply FastRouting.sound _ _ [34,68,384,18,65] 13 (by decide) (choices 1) [1,4,8] r36351 c36351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20738
  · exact u20739
  · exact u20740

def b36352 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 388 26 84 41 105 169 297), lower := (rows 35 70 388 26 84 32 64 128 256), losses := [] }

theorem u36352 : Upper (D 6) (R 6) [34,68,384,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36353 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 24, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 70 388 26 88 37 101 165 293), lower := (rows 35 70 388 26 88 32 64 128 256), losses := [] }

theorem u36353 : Upper (D 6) (R 6) [34,68,384,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36354 : Route 9 := (fun mask => (mask,id))

def c36354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36354 : Upper (D 6) (R 6) [34,68,384,18,96] 13 := by
  apply FastRouting.sound _ _ [34,68,384,18,96] 13 (by decide) (choices 1) [1,4,8] r36354 c36354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20741
  · exact u20742
  · exact u20743

def b36355 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 70 388 28 49 107 75 203 331), lower := (rows 35 70 388 28 49 32 64 128 256), losses := [] }

theorem u36355 : Upper (D 6) (R 6) [34,68,384,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36356 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 70 388 28 50 105 73 201 329), lower := (rows 35 70 388 28 50 32 64 128 256), losses := [] }

theorem u36356 : Upper (D 6) (R 6) [34,68,384,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36357 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 70 388 28 56 99 67 195 323), lower := (rows 35 70 388 28 56 32 64 128 256), losses := [] }

theorem u36357 : Upper (D 6) (R 6) [34,68,384,20,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36358 : Route 9 := (fun mask => (mask,id))

def c36358 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36358 : Upper (D 6) (R 6) [34,68,384,20,65] 13 := by
  apply FastRouting.sound _ _ [34,68,384,20,65] 13 (by decide) (choices 1) [1,2,8] r36358 c36358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20744
  · exact u20745
  · exact u20746

def b36359 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 388 28 82 41 105 169 297), lower := (rows 35 70 388 28 82 32 64 128 256), losses := [] }

theorem u36359 : Upper (D 6) (R 6) [34,68,384,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u36359
end Delivery.IrregularNine14.P06
