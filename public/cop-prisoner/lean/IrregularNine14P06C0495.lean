import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0187
import IrregularNine14P06C0188

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29700 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 7 138 292 28 49 99 67 195 323), lower := (rows 7 138 292 28 49 32 64 128 256), losses := [] }

theorem u29700 : Upper (D 6) (R 6) [6,136,288,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29700
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29701 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,5),(1,5),(2,1)], upper := (rows 7 138 292 28 50 97 65 193 321), lower := (rows 7 138 292 28 50 32 64 128 256), losses := [] }

theorem u29701 : Upper (D 6) (R 6) [6,136,288,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29701
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29702 : Route 9 := (fun mask => (mask,id))

def c29702 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29702 : Upper (D 6) (R 6) [6,136,288,20,65] 13 := by
  apply FastRouting.sound _ _ [6,136,288,20,65] 13 (by decide) (choices 1) [1,2,64] r29702 c29702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11239
  · exact u11240
  · exact u11241

def r29703 : Route 9 := (fun mask => (mask,id))

def c29703 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29703 : Upper (D 6) (R 6) [6,136,288,20,66] 13 := by
  apply FastRouting.sound _ _ [6,136,288,20,66] 13 (by decide) (choices 1) [1,64] r29703 c29703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11242
  · exact u11243

def b29704 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 7 138 292 28 112 99 67 195 323), lower := (rows 7 138 292 28 112 32 64 128 256), losses := [] }

theorem u29704 : Upper (D 6) (R 6) [6,136,288,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29704
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29705 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 7 138 292 41 19 116 84 212 340), lower := (rows 7 138 292 41 19 32 64 128 256), losses := [] }

theorem u29705 : Upper (D 6) (R 6) [6,136,288,33,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29705
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29706 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 4, region := 234, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 138 292 41 21 114 82 210 338), lower := (rows 7 138 292 41 21 32 64 128 256), losses := [] }

theorem u29706 : Upper (D 6) (R 6) [6,136,288,33,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29706
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29707 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 7 138 292 41 22 113 81 209 337), lower := (rows 7 138 292 41 22 32 64 128 256), losses := [] }

theorem u29707 : Upper (D 6) (R 6) [6,136,288,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29707
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29708 : Route 9 := (fun mask => (mask,id))

def c29708 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29708 : Upper (D 6) (R 6) [6,136,288,33,65] 13 := by
  apply FastRouting.sound _ _ [6,136,288,33,65] 13 (by decide) (choices 1) [2,4,16,64] r29708 c29708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11244
  · exact u11245
  · exact u11246
  · exact u11247

def r29709 : Route 9 := (fun mask => (mask,id))

def c29709 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29709 : Upper (D 6) (R 6) [6,136,288,33,66] 13 := by
  apply FastRouting.sound _ _ [6,136,288,33,66] 13 (by decide) (choices 1) [1,4,16,64] r29709 c29709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11248
  · exact u11249
  · exact u11250
  · exact u11251

def r29710 : Route 9 := (fun mask => (mask,id))

def c29710 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29710 : Upper (D 6) (R 6) [6,136,288,33,68] 13 := by
  apply FastRouting.sound _ _ [6,136,288,33,68] 13 (by decide) (choices 1) [1,2,16,64] r29710 c29710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11252
  · exact u11253
  · exact u11254
  · exact u11255

def b29711 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 7 138 292 56 19 101 69 197 325), lower := (rows 7 138 292 56 19 32 64 128 256), losses := [] }

theorem u29711 : Upper (D 6) (R 6) [6,136,288,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29711
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29712 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 4, region := 234, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 138 292 56 21 99 67 195 323), lower := (rows 7 138 292 56 21 32 64 128 256), losses := [] }

theorem u29712 : Upper (D 6) (R 6) [6,136,288,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29712
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29713 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 356, targets := 2 },{ cop := 0, region := 16, targets := 32 }], pairs := [(2,1),(4,0),(4,5)], upper := (rows 7 138 292 56 22 97 65 193 321), lower := (rows 7 138 292 56 22 32 64 128 256), losses := [] }

theorem u29713 : Upper (D 6) (R 6) [6,136,288,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29713
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29714 : Route 9 := (fun mask => (mask,id))

def c29714 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29714 : Upper (D 6) (R 6) [6,136,288,48,65] 13 := by
  apply FastRouting.sound _ _ [6,136,288,48,65] 13 (by decide) (choices 1) [1,2,4,64] r29714 c29714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11256
  · exact u11257
  · exact u11258
  · exact u11259

def r29715 : Route 9 := (fun mask => (mask,id))

def c29715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29715 : Upper (D 6) (R 6) [6,136,288,48,66] 13 := by
  apply FastRouting.sound _ _ [6,136,288,48,66] 13 (by decide) (choices 1) [1,4,64] r29715 c29715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11260
  · exact u11261
  · exact u11262

def r29716 : Route 9 := (fun mask => (mask,id))

def c29716 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29716 : Upper (D 6) (R 6) [6,136,288,48,68] 13 := by
  apply FastRouting.sound _ _ [6,136,288,48,68] 13 (by decide) (choices 1) [1,2,64] r29716 c29716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11263
  · exact u11264
  · exact u11265

def b29717 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 7 138 292 73 19 116 116 244 372), lower := (rows 7 138 292 73 19 32 64 128 256), losses := [] }

theorem u29717 : Upper (D 6) (R 6) [6,136,288,65,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29717
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29718 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 138 292 73 21 114 114 242 370), lower := (rows 7 138 292 73 21 32 64 128 256), losses := [] }

theorem u29718 : Upper (D 6) (R 6) [6,136,288,65,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29718
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29719 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 138 292 73 22 113 113 241 369), lower := (rows 7 138 292 73 22 32 64 128 256), losses := [] }

theorem u29719 : Upper (D 6) (R 6) [6,136,288,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29719
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29720 : Route 9 := (fun mask => (mask,id))

def c29720 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29720 : Upper (D 6) (R 6) [6,136,288,65,33] 13 := by
  apply FastRouting.sound _ _ [6,136,288,65,33] 13 (by decide) (choices 1) [2,4,16,64] r29720 c29720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11266
  · exact u11267
  · exact u11268
  · exact u11269

def r29721 : Route 9 := (fun mask => (mask,id))

def c29721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29721 : Upper (D 6) (R 6) [6,136,288,65,34] 13 := by
  apply FastRouting.sound _ _ [6,136,288,65,34] 13 (by decide) (choices 1) [1,4,16,64] r29721 c29721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11270
  · exact u11271
  · exact u11272
  · exact u11273

def b29722 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 138 292 73 52 115 83 211 339), lower := (rows 7 138 292 73 52 32 64 128 256), losses := [] }

theorem u29722 : Upper (D 6) (R 6) [6,136,288,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29722
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29723 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 7 138 292 73 81 54 118 182 310), lower := (rows 7 138 292 73 81 32 64 128 256), losses := [] }

theorem u29723 : Upper (D 6) (R 6) [6,136,288,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29723
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29724 : Route 9 := (fun mask => (mask,id))

def c29724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29724 : Upper (D 6) (R 6) [6,136,288,65,66] 13 := by
  apply FastRouting.sound _ _ [6,136,288,65,66] 13 (by decide) (choices 1) [1,4,16] r29724 c29724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11274
  · exact u11275
  · exact u11276

def r29725 : Route 9 := (fun mask => (mask,id))

def c29725 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29725 : Upper (D 6) (R 6) [6,136,288,65,68] 13 := by
  apply FastRouting.sound _ _ [6,136,288,65,68] 13 (by decide) (choices 1) [1,2,16] r29725 c29725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11277
  · exact u11278
  · exact u11279

def r29726 : Route 9 := (fun mask => (mask,id))

def c29726 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29726 : Upper (D 6) (R 6) [6,136,288,65,96] 13 := by
  apply FastRouting.sound _ _ [6,136,288,65,96] 13 (by decide) (choices 1) [1,2,4,16] r29726 c29726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11280
  · exact u11281
  · exact u11282
  · exact u11283

def b29727 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 16, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 138 292 74 21 113 113 241 369), lower := (rows 7 138 292 74 21 32 64 128 256), losses := [] }

theorem u29727 : Upper (D 6) (R 6) [6,136,288,66,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29727
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29728 : Route 9 := (fun mask => (mask,id))

def c29728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29728 : Upper (D 6) (R 6) [6,136,288,66,33] 13 := by
  apply FastRouting.sound _ _ [6,136,288,66,33] 13 (by decide) (choices 1) [1,4,16,64] r29728 c29728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11284
  · exact u11285
  · exact u11286
  · exact u11287

def b29729 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 138 292 74 52 113 81 209 337), lower := (rows 7 138 292 74 52 32 64 128 256), losses := [] }

theorem u29729 : Upper (D 6) (R 6) [6,136,288,66,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29729
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29730 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 4, region := 292, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 7 138 292 74 81 53 117 181 309), lower := (rows 7 138 292 74 81 32 64 128 256), losses := [] }

theorem u29730 : Upper (D 6) (R 6) [6,136,288,66,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29730
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29731 : Route 9 := (fun mask => (mask,id))

def c29731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29731 : Upper (D 6) (R 6) [6,136,288,66,68] 13 := by
  apply FastRouting.sound _ _ [6,136,288,66,68] 13 (by decide) (choices 1) [1,16] r29731 c29731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11288
  · exact u11289

def r29732 : Route 9 := (fun mask => (mask,id))

def c29732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29732 : Upper (D 6) (R 6) [6,136,288,66,96] 13 := by
  apply FastRouting.sound _ _ [6,136,288,66,96] 13 (by decide) (choices 1) [1,4,16] r29732 c29732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11290
  · exact u11291
  · exact u11292

def b29733 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 7 138 292 76 19 113 113 241 369), lower := (rows 7 138 292 76 19 32 64 128 256), losses := [] }

theorem u29733 : Upper (D 6) (R 6) [6,136,288,68,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29733
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29734 : Route 9 := (fun mask => (mask,id))

def c29734 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29734 : Upper (D 6) (R 6) [6,136,288,68,33] 13 := by
  apply FastRouting.sound _ _ [6,136,288,68,33] 13 (by decide) (choices 1) [1,2,16,64] r29734 c29734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11293
  · exact u11294
  · exact u11295
  · exact u11296

def r29735 : Route 9 := (fun mask => (mask,id))

def c29735 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29735 : Upper (D 6) (R 6) [6,136,288,68,34] 13 := by
  apply FastRouting.sound _ _ [6,136,288,68,34] 13 (by decide) (choices 1) [1,16,64] r29735 c29735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11297
  · exact u11298
  · exact u11299

def r29736 : Route 9 := (fun mask => (mask,id))

def c29736 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29736 : Upper (D 6) (R 6) [6,136,288,68,65] 13 := by
  apply FastRouting.sound _ _ [6,136,288,68,65] 13 (by decide) (choices 1) [1,2,16] r29736 c29736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11300
  · exact u11301
  · exact u11302

def b29737 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 293, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(2,6),(4,2)], upper := (rows 7 138 292 76 82 49 113 177 305), lower := (rows 7 138 292 76 82 32 64 128 256), losses := [] }

theorem u29737 : Upper (D 6) (R 6) [6,136,288,68,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29737
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29738 : Route 9 := (fun mask => (mask,id))

def c29738 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29738 : Upper (D 6) (R 6) [6,136,288,68,96] 13 := by
  apply FastRouting.sound _ _ [6,136,288,68,96] 13 (by decide) (choices 1) [1,2,16] r29738 c29738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11303
  · exact u11304
  · exact u11305

def b29739 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 7 138 292 88 19 101 101 229 357), lower := (rows 7 138 292 88 19 32 64 128 256), losses := [] }

theorem u29739 : Upper (D 6) (R 6) [6,136,288,80,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29739
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29740 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 7 138 292 88 21 99 99 227 355), lower := (rows 7 138 292 88 21 32 64 128 256), losses := [] }

theorem u29740 : Upper (D 6) (R 6) [6,136,288,80,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29740
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29741 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 1, targets := 32 }], pairs := [(0,5),(4,5),(4,6)], upper := (rows 7 138 292 88 22 97 97 225 353), lower := (rows 7 138 292 88 22 32 64 128 256), losses := [] }

theorem u29741 : Upper (D 6) (R 6) [6,136,288,80,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29741
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29742 : Route 9 := (fun mask => (mask,id))

def c29742 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29742 : Upper (D 6) (R 6) [6,136,288,80,33] 13 := by
  apply FastRouting.sound _ _ [6,136,288,80,33] 13 (by decide) (choices 1) [1,2,4,64] r29742 c29742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11306
  · exact u11307
  · exact u11308
  · exact u11309

def r29743 : Route 9 := (fun mask => (mask,id))

def c29743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29743 : Upper (D 6) (R 6) [6,136,288,80,34] 13 := by
  apply FastRouting.sound _ _ [6,136,288,80,34] 13 (by decide) (choices 1) [1,4,64] r29743 c29743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11310
  · exact u11311
  · exact u11312

def b29744 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 138 292 88 52 99 67 195 323), lower := (rows 7 138 292 88 52 32 64 128 256), losses := [] }

theorem u29744 : Upper (D 6) (R 6) [6,136,288,80,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29744
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29745 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 138 292 88 81 39 103 167 295), lower := (rows 7 138 292 88 81 32 64 128 256), losses := [] }

theorem u29745 : Upper (D 6) (R 6) [6,136,288,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29745
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29746 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 138 292 88 82 37 101 165 293), lower := (rows 7 138 292 88 82 32 64 128 256), losses := [] }

theorem u29746 : Upper (D 6) (R 6) [6,136,288,80,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29746
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29747 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 138 292 88 84 35 99 163 291), lower := (rows 7 138 292 88 84 32 64 128 256), losses := [] }

theorem u29747 : Upper (D 6) (R 6) [6,136,288,80,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29747
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29748 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 138 292 88 112 39 71 135 263), lower := (rows 7 138 292 88 112 32 64 128 256), losses := [] }

theorem u29748 : Upper (D 6) (R 6) [6,136,288,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29748
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29749 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 7 138 292 104 19 117 85 213 341), lower := (rows 7 138 292 104 19 32 64 128 256), losses := [] }

theorem u29749 : Upper (D 6) (R 6) [6,136,288,96,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29749
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29750 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 4, region := 234, targets := 4 }], pairs := [(1,2),(4,1),(4,6)], upper := (rows 7 138 292 104 21 115 83 211 339), lower := (rows 7 138 292 104 21 32 64 128 256), losses := [] }

theorem u29750 : Upper (D 6) (R 6) [6,136,288,96,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29750
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29751 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 16, targets := 1 },{ cop := 0, region := 16, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 7 138 292 104 22 113 81 209 337), lower := (rows 7 138 292 104 22 32 64 128 256), losses := [] }

theorem u29751 : Upper (D 6) (R 6) [6,136,288,96,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29751
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29752 : Route 9 := (fun mask => (mask,id))

def c29752 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29752 : Upper (D 6) (R 6) [6,136,288,96,65] 13 := by
  apply FastRouting.sound _ _ [6,136,288,96,65] 13 (by decide) (choices 1) [1,2,4,16] r29752 c29752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11313
  · exact u11314
  · exact u11315
  · exact u11316

def b29753 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 293, targets := 64 },{ cop := 0, region := 80, targets := 32 }], pairs := [(0,6),(2,6),(4,5)], upper := (rows 7 138 292 104 82 53 85 149 277), lower := (rows 7 138 292 104 82 32 64 128 256), losses := [] }

theorem u29753 : Upper (D 6) (R 6) [6,136,288,96,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29753
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29754 : Route 9 := (fun mask => (mask,id))

def c29754 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29754 : Upper (D 6) (R 6) [6,136,288,96,68] 13 := by
  apply FastRouting.sound _ _ [6,136,288,96,68] 13 (by decide) (choices 1) [1,2,16] r29754 c29754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11317
  · exact u11318
  · exact u11319

def b29755 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 162 292 11 25 116 84 212 340), lower := (rows 7 162 292 11 25 32 64 128 256), losses := [] }

theorem u29755 : Upper (D 6) (R 6) [6,160,288,3,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29755
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29756 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 24, targets := 32 },{ cop := 0, region := 8, targets := 64 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 162 292 11 28 113 81 209 337), lower := (rows 7 162 292 11 28 32 64 128 256), losses := [] }

theorem u29756 : Upper (D 6) (R 6) [6,160,288,3,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29756
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29757 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 162 292 11 81 124 92 220 348), lower := (rows 7 162 292 11 81 32 64 128 256), losses := [] }

theorem u29757 : Upper (D 6) (R 6) [6,160,288,3,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29757
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29758 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 162 292 11 84 121 89 217 345), lower := (rows 7 162 292 11 84 32 64 128 256), losses := [] }

theorem u29758 : Upper (D 6) (R 6) [6,160,288,3,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29758
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29759 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 0, region := 8, targets := 32 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 162 292 11 88 117 85 213 341), lower := (rows 7 162 292 11 88 32 64 128 256), losses := [] }

theorem u29759 : Upper (D 6) (R 6) [6,160,288,3,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29759
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u29759
end Delivery.IrregularNine14.P06
