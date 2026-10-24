import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0228
import IrregularNine14P07C0229
import IrregularNine14P07C0230

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31260 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 13 152 112 419 451 387 387), lower := (rows 7 98 13 152 112 32 64 128 256), losses := [] }

theorem u31260 : Upper (D 7) (R 7) [6,96,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31261 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 12, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 7 98 13 152 145 354 354 482 354), lower := (rows 7 98 13 152 145 32 64 128 256), losses := [] }

theorem u31261 : Upper (D 7) (R 7) [6,96,9,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31262 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 13, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 7 98 13 152 146 353 353 481 353), lower := (rows 7 98 13 152 146 32 64 128 256), losses := [] }

theorem u31262 : Upper (D 7) (R 7) [6,96,9,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31263 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 98 13 152 176 355 323 451 323), lower := (rows 7 98 13 152 176 32 64 128 256), losses := [] }

theorem u31263 : Upper (D 7) (R 7) [6,96,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31264 : Route 9 := (fun mask => (mask,id))

def c31264 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31264 : Upper (D 7) (R 7) [6,96,9,144,257] 13 := by
  apply FastRouting.sound _ _ [6,96,9,144,257] 13 (by decide) (choices 1) [2,64,128] r31264 c31264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13706
  · exact u13707
  · exact u13708

def r31265 : Route 9 := (fun mask => (mask,id))

def c31265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31265 : Upper (D 7) (R 7) [6,96,9,144,258] 13 := by
  apply FastRouting.sound _ _ [6,96,9,144,258] 13 (by decide) (choices 1) [1,64,128] r31265 c31265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13709
  · exact u13710
  · exact u13711

def r31266 : Route 9 := (fun mask => (mask,id))

def c31266 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31266 : Upper (D 7) (R 7) [6,96,9,144,288] 13 := by
  apply FastRouting.sound _ _ [6,96,9,144,288] 13 (by decide) (choices 1) [1,2,64,128] r31266 c31266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13712
  · exact u13713
  · exact u13714
  · exact u13715

def b31267 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 98 13 152 400 99 99 227 355), lower := (rows 7 98 13 152 400 32 64 128 256), losses := [] }

theorem u31267 : Upper (D 7) (R 7) [6,96,9,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31268 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 7 98 13 168 19 496 464 464 464), lower := (rows 7 98 13 168 19 32 64 128 256), losses := [] }

theorem u31268 : Upper (D 7) (R 7) [6,96,9,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31269 : Route 9 := (fun mask => (mask,id))

def c31269 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u31269 : Upper (D 7) (R 7) [6,96,9,160,65] 13 := by
  apply FastRouting.sound _ _ [6,96,9,160,65] 13 (by decide) (choices 1) [2,16,128,256] r31269 c31269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13716
  · exact u13717
  · exact u13718
  · exact u13719

def b31270 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 13 168 82 433 465 401 401), lower := (rows 7 98 13 168 82 32 64 128 256), losses := [] }

theorem u31270 : Upper (D 7) (R 7) [6,96,9,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31271 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 464, targets := 32 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,5)], upper := (rows 7 98 13 168 145 370 338 466 338), lower := (rows 7 98 13 168 145 32 64 128 256), losses := [] }

theorem u31271 : Upper (D 7) (R 7) [6,96,9,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31272 : Route 9 := (fun mask => (mask,id))

def c31272 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u31272 : Upper (D 7) (R 7) [6,96,9,160,130] 13 := by
  apply FastRouting.sound _ _ [6,96,9,160,130] 13 (by decide) (choices 1) [1,16,64,256] r31272 c31272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13720
  · exact u13721
  · exact u13722
  · exact u13723

def r31273 : Route 9 := (fun mask => (mask,id))

def c31273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31273 : Upper (D 7) (R 7) [6,96,9,160,192] 13 := by
  apply FastRouting.sound _ _ [6,96,9,160,192] 13 (by decide) (choices 1) [1,2,16,256] r31273 c31273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13724
  · exact u13725
  · exact u13726
  · exact u13727

def r31274 : Route 9 := (fun mask => (mask,id))

def c31274 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31274 : Upper (D 7) (R 7) [6,96,9,160,257] 13 := by
  apply FastRouting.sound _ _ [6,96,9,160,257] 13 (by decide) (choices 1) [2,16,64,128] r31274 c31274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13728
  · exact u13729
  · exact u13730
  · exact u13731

def r31275 : Route 9 := (fun mask => (mask,id))

def c31275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31275 : Upper (D 7) (R 7) [6,96,9,160,258] 13 := by
  apply FastRouting.sound _ _ [6,96,9,160,258] 13 (by decide) (choices 1) [1,16,64,128] r31275 c31275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13732
  · exact u13733
  · exact u13734
  · exact u13735

def r31276 : Route 9 := (fun mask => (mask,id))

def c31276 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31276 : Upper (D 7) (R 7) [6,96,9,160,320] 13 := by
  apply FastRouting.sound _ _ [6,96,9,160,320] 13 (by decide) (choices 1) [1,2,16,128] r31276 c31276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13736
  · exact u13737
  · exact u13738
  · exact u13739

def r31277 : Route 9 := (fun mask => (mask,id))

def c31277 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31277 : Upper (D 7) (R 7) [6,96,9,160,384] 13 := by
  apply FastRouting.sound _ _ [6,96,9,160,384] 13 (by decide) (choices 1) [1,2,16,64] r31277 c31277
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13740
  · exact u13741
  · exact u13742
  · exact u13743

def b31278 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 226, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 7 98 13 280 19 224 224 224 480), lower := (rows 7 98 13 280 19 32 64 128 256), losses := [] }

theorem u31278 : Upper (D 7) (R 7) [6,96,9,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31278 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31279 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 7 98 13 280 49 226 194 194 450), lower := (rows 7 98 13 280 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 67 131 259), good := (rows 455 450 461 284 477 0 64 128 256) }] }

theorem u31279 : Upper (D 7) (R 7) [6,96,9,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31280 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 98 13 280 50 225 193 193 449), lower := (rows 7 98 13 280 50 32 64 128 256), losses := [] }

theorem u31280 : Upper (D 7) (R 7) [6,96,9,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31281 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 13 280 112 163 195 131 387), lower := (rows 7 98 13 280 112 32 64 128 256), losses := [] }

theorem u31281 : Upper (D 7) (R 7) [6,96,9,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31282 : Route 9 := (fun mask => (mask,id))

def c31282 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31282 : Upper (D 7) (R 7) [6,96,9,272,129] 13 := by
  apply FastRouting.sound _ _ [6,96,9,272,129] 13 (by decide) (choices 1) [2,64,128] r31282 c31282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13744
  · exact u13745
  · exact u13746

def r31283 : Route 9 := (fun mask => (mask,id))

def c31283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31283 : Upper (D 7) (R 7) [6,96,9,272,130] 13 := by
  apply FastRouting.sound _ _ [6,96,9,272,130] 13 (by decide) (choices 1) [1,64,128] r31283 c31283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13747
  · exact u13748
  · exact u13749

def r31284 : Route 9 := (fun mask => (mask,id))

def c31284 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31284 : Upper (D 7) (R 7) [6,96,9,272,160] 13 := by
  apply FastRouting.sound _ _ [6,96,9,272,160] 13 (by decide) (choices 1) [1,2,64,128] r31284 c31284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13750
  · exact u13751
  · exact u13752
  · exact u13753

def b31285 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 7 98 13 296 19 240 208 208 464), lower := (rows 7 98 13 296 19 32 64 128 256), losses := [] }

theorem u31285 : Upper (D 7) (R 7) [6,96,9,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31286 : Route 9 := (fun mask => (mask,id))

def c31286 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31286 : Upper (D 7) (R 7) [6,96,9,288,65] 13 := by
  apply FastRouting.sound _ _ [6,96,9,288,65] 13 (by decide) (choices 1) [2,16,128] r31286 c31286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13754
  · exact u13755
  · exact u13756

def b31287 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 7 98 13 296 82 177 209 145 401), lower := (rows 7 98 13 296 82 32 64 128 256), losses := [] }

theorem u31287 : Upper (D 7) (R 7) [6,96,9,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31287 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31288 : Route 9 := (fun mask => (mask,id))

def c31288 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31288 : Upper (D 7) (R 7) [6,96,9,288,129] 13 := by
  apply FastRouting.sound _ _ [6,96,9,288,129] 13 (by decide) (choices 1) [2,16,64,128] r31288 c31288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13757
  · exact u13758
  · exact u13759
  · exact u13760

def r31289 : Route 9 := (fun mask => (mask,id))

def c31289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31289 : Upper (D 7) (R 7) [6,96,9,288,130] 13 := by
  apply FastRouting.sound _ _ [6,96,9,288,130] 13 (by decide) (choices 1) [1,16,64,128] r31289 c31289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13761
  · exact u13762
  · exact u13763
  · exact u13764

def r31290 : Route 9 := (fun mask => (mask,id))

def c31290 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31290 : Upper (D 7) (R 7) [6,96,9,288,192] 13 := by
  apply FastRouting.sound _ _ [6,96,9,288,192] 13 (by decide) (choices 1) [1,2,16,128] r31290 c31290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13765
  · exact u13766
  · exact u13767
  · exact u13768

def b31291 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 226, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 7 98 13 392 19 240 240 240 496), lower := (rows 7 98 13 392 19 32 64 128 256), losses := [] }

theorem u31291 : Upper (D 7) (R 7) [6,96,9,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31292 : Route 9 := (fun mask => (mask,id))

def c31292 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u31292 : Upper (D 7) (R 7) [6,96,9,384,33] 13 := by
  apply FastRouting.sound _ _ [6,96,9,384,33] 13 (by decide) (choices 1) [2,16,64,128] r31292 c31292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13769
  · exact u13770
  · exact u13771
  · exact u13772

def b31293 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 98 13 392 50 241 209 209 465), lower := (rows 7 98 13 392 50 32 64 128 256), losses := [] }

theorem u31293 : Upper (D 7) (R 7) [6,96,9,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31294 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 98 13 392 112 179 211 147 403), lower := (rows 7 98 13 392 112 32 64 128 256), losses := [] }

theorem u31294 : Upper (D 7) (R 7) [6,96,9,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31295 : Route 9 := (fun mask => (mask,id))

def c31295 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31295 : Upper (D 7) (R 7) [6,96,9,384,129] 13 := by
  apply FastRouting.sound _ _ [6,96,9,384,129] 13 (by decide) (choices 1) [2,16,64] r31295 c31295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13773
  · exact u13774
  · exact u13775

def r31296 : Route 9 := (fun mask => (mask,id))

def c31296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31296 : Upper (D 7) (R 7) [6,96,9,384,130] 13 := by
  apply FastRouting.sound _ _ [6,96,9,384,130] 13 (by decide) (choices 1) [1,16,64] r31296 c31296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13776
  · exact u13777
  · exact u13778

def r31297 : Route 9 := (fun mask => (mask,id))

def c31297 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31297 : Upper (D 7) (R 7) [6,96,9,384,160] 13 := by
  apply FastRouting.sound _ _ [6,96,9,384,160] 13 (by decide) (choices 1) [1,2,16,64] r31297 c31297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13779
  · exact u13780
  · exact u13781
  · exact u13782

def b31298 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 29, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 28 11 49 480 448 448 448), lower := (rows 7 98 28 11 49 32 64 128 256), losses := [] }

theorem u31298 : Upper (D 7) (R 7) [6,96,24,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31299 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 28 11 145 480 480 480 480), lower := (rows 7 98 28 11 145 32 64 128 256), losses := [] }

theorem u31299 : Upper (D 7) (R 7) [6,96,24,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31300 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,6),(3,7),(4,1)], upper := (rows 7 98 28 11 176 481 449 449 449), lower := (rows 7 98 28 11 176 32 64 128 256), losses := [] }

theorem u31300 : Upper (D 7) (R 7) [6,96,24,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31301 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 28 11 273 224 224 224 480), lower := (rows 7 98 28 11 273 32 64 128 256), losses := [] }

theorem u31301 : Upper (D 7) (R 7) [6,96,24,3,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31302 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,6),(3,7),(4,1)], upper := (rows 7 98 28 11 304 225 193 193 449), lower := (rows 7 98 28 11 304 32 64 128 256), losses := [] }

theorem u31302 : Upper (D 7) (R 7) [6,96,24,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31303 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 7 98 28 11 400 225 225 225 481), lower := (rows 7 98 28 11 400 32 64 128 256), losses := [] }

theorem u31303 : Upper (D 7) (R 7) [6,96,24,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31304 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 28 41 81 418 450 386 386), lower := (rows 7 98 28 41 81 32 64 128 256), losses := [] }

theorem u31304 : Upper (D 7) (R 7) [6,96,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31305 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 7 98 28 41 82 417 449 385 385), lower := (rows 7 98 28 41 82 32 64 128 256), losses := [] }

theorem u31305 : Upper (D 7) (R 7) [6,96,24,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31305 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r31306 : Route 9 := (fun mask => (mask,id))

def c31306 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u31306 : Upper (D 7) (R 7) [6,96,24,33,129] 13 := by
  apply FastRouting.sound _ _ [6,96,24,33,129] 13 (by decide) (choices 1) [2,64,128,256] r31306 c31306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13783
  · exact u13784
  · exact u13785
  · exact u13786

def r31307 : Route 9 := (fun mask => (mask,id))

def c31307 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u31307 : Upper (D 7) (R 7) [6,96,24,33,130] 13 := by
  apply FastRouting.sound _ _ [6,96,24,33,130] 13 (by decide) (choices 1) [1,64,128,256] r31307 c31307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13787
  · exact u13788
  · exact u13789
  · exact u13790

def r31308 : Route 9 := (fun mask => (mask,id))

def c31308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u31308 : Upper (D 7) (R 7) [6,96,24,33,192] 13 := by
  apply FastRouting.sound _ _ [6,96,24,33,192] 13 (by decide) (choices 1) [1,2,128,256] r31308 c31308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13791
  · exact u13792
  · exact u13793
  · exact u13794

def r31309 : Route 9 := (fun mask => (mask,id))

def c31309 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31309 : Upper (D 7) (R 7) [6,96,24,33,257] 13 := by
  apply FastRouting.sound _ _ [6,96,24,33,257] 13 (by decide) (choices 1) [2,64,128] r31309 c31309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13795
  · exact u13796
  · exact u13797

def r31310 : Route 9 := (fun mask => (mask,id))

def c31310 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31310 : Upper (D 7) (R 7) [6,96,24,33,258] 13 := by
  apply FastRouting.sound _ _ [6,96,24,33,258] 13 (by decide) (choices 1) [1,64,128] r31310 c31310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13798
  · exact u13799
  · exact u13800

def r31311 : Route 9 := (fun mask => (mask,id))

def c31311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u31311 : Upper (D 7) (R 7) [6,96,24,33,320] 13 := by
  apply FastRouting.sound _ _ [6,96,24,33,320] 13 (by decide) (choices 1) [1,2,128] r31311 c31311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13801
  · exact u13802
  · exact u13803

def r31312 : Route 9 := (fun mask => (mask,id))

def c31312 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u31312 : Upper (D 7) (R 7) [6,96,24,33,384] 13 := by
  apply FastRouting.sound _ _ [6,96,24,33,384] 13 (by decide) (choices 1) [1,2,64,128] r31312 c31312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13804
  · exact u13805
  · exact u13806
  · exact u13807

def b31313 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 28 42 145 481 449 449 449), lower := (rows 7 98 28 42 145 32 64 128 256), losses := [] }

theorem u31313 : Upper (D 7) (R 7) [6,96,24,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31314 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 28 42 208 417 449 385 385), lower := (rows 7 98 28 42 208 32 64 128 256), losses := [] }

theorem u31314 : Upper (D 7) (R 7) [6,96,24,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31315 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 28 42 273 225 193 193 449), lower := (rows 7 98 28 42 273 32 64 128 256), losses := [] }

theorem u31315 : Upper (D 7) (R 7) [6,96,24,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31316 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 28 42 336 161 193 129 385), lower := (rows 7 98 28 42 336 32 64 128 256), losses := [] }

theorem u31316 : Upper (D 7) (R 7) [6,96,24,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31317 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 8, targets := 193 },{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(3,0),(3,6),(3,7)], upper := (rows 7 98 28 42 400 225 193 193 449), lower := (rows 7 98 28 42 400 32 64 128 256), losses := [] }

theorem u31317 : Upper (D 7) (R 7) [6,96,24,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31318 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 28 104 145 419 451 387 387), lower := (rows 7 98 28 104 145 32 64 128 256), losses := [] }

theorem u31318 : Upper (D 7) (R 7) [6,96,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31319 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 8, targets := 129 },{ cop := 3, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 28 104 146 417 449 385 385), lower := (rows 7 98 28 104 146 32 64 128 256), losses := [] }

theorem u31319 : Upper (D 7) (R 7) [6,96,24,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u31319
end Delivery.IrregularNine14.P07
