import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0396
import IrregularNine14P06C0397

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38100 : Route 9 := (fun mask => (mask,id))

def c38100 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38100 : Upper (D 6) (R 6) [34,136,66,36,320] 13 := by
  apply FastRouting.sound _ _ [34,136,66,36,320] 13 (by decide) (choices 1) [1,4,16] r38100 c38100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23779
  · exact u23780
  · exact u23781

def b38101 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 35 138 70 56 21 357 325 453 325), lower := (rows 35 138 70 56 21 32 64 128 256), losses := [] }

theorem u38101 : Upper (D 6) (R 6) [34,136,66,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38102 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 289, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 138 70 56 81 293 325 389 261), lower := (rows 35 138 70 56 81 32 64 128 256), losses := [] }

theorem u38102 : Upper (D 6) (R 6) [34,136,66,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38102 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38103 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 70 56 84 293 325 389 261), lower := (rows 35 138 70 56 84 32 64 128 256), losses := [] }

theorem u38103 : Upper (D 6) (R 6) [34,136,66,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38104 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 138 70 56 273 101 69 197 325), lower := (rows 35 138 70 56 273 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 13 8 17 0 81 145 273), good := (rows 471 142 70 478 469 0 64 128 256) }] }

theorem u38104 : Upper (D 6) (R 6) [34,136,66,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38105 : Route 9 := (fun mask => (mask,id))

def c38105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38105 : Upper (D 6) (R 6) [34,136,66,48,260] 13 := by
  apply FastRouting.sound _ _ [34,136,66,48,260] 13 (by decide) (choices 1) [1,4,64] r38105 c38105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23782
  · exact u23783
  · exact u23784

def b38106 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 138 70 56 336 37 69 133 261), lower := (rows 35 138 70 56 336 32 64 128 256), losses := [] }

theorem u38106 : Upper (D 6) (R 6) [34,136,66,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38107 : Route 9 := (fun mask => (mask,id))

def c38107 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38107 : Upper (D 6) (R 6) [34,136,66,257,5] 13 := by
  apply FastRouting.sound _ _ [34,136,66,257,5] 13 (by decide) (choices 1) [4,16,64] r38107 c38107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23785
  · exact u23786
  · exact u23787

def b38108 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 70 265 49 116 84 212 340), lower := (rows 35 138 70 265 49 32 64 128 256), losses := [] }

theorem u38108 : Upper (D 6) (R 6) [34,136,66,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38109 : Route 9 := (fun mask => (mask,id))

def c38109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38109 : Upper (D 6) (R 6) [34,136,66,257,36] 13 := by
  apply FastRouting.sound _ _ [34,136,66,257,36] 13 (by decide) (choices 1) [1,4,16,64] r38109 c38109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23788
  · exact u23789
  · exact u23790
  · exact u23791

def r38110 : Route 9 := (fun mask => (mask,id))

def c38110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38110 : Upper (D 6) (R 6) [34,136,66,257,65] 13 := by
  apply FastRouting.sound _ _ [34,136,66,257,65] 13 (by decide) (choices 1) [4,16] r38110 c38110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23792
  · exact u23793

def b38111 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 70 265 84 53 117 181 309), lower := (rows 35 138 70 265 84 32 64 128 256), losses := [] }

theorem u38111 : Upper (D 6) (R 6) [34,136,66,257,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38112 : Route 9 := (fun mask => (mask,id))

def c38112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38112 : Upper (D 6) (R 6) [34,136,66,257,96] 13 := by
  apply FastRouting.sound _ _ [34,136,66,257,96] 13 (by decide) (choices 1) [1,4,16] r38112 c38112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23794
  · exact u23795
  · exact u23796

def r38113 : Route 9 := (fun mask => (mask,id))

def c38113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38113 : Upper (D 6) (R 6) [34,136,66,272,5] 13 := by
  apply FastRouting.sound _ _ [34,136,66,272,5] 13 (by decide) (choices 1) [1,4,64] r38113 c38113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23797
  · exact u23798
  · exact u23799

def b38114 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 70 280 49 101 69 197 325), lower := (rows 35 138 70 280 49 32 64 128 256), losses := [] }

theorem u38114 : Upper (D 6) (R 6) [34,136,66,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38115 : Route 9 := (fun mask => (mask,id))

def c38115 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38115 : Upper (D 6) (R 6) [34,136,66,272,36] 13 := by
  apply FastRouting.sound _ _ [34,136,66,272,36] 13 (by decide) (choices 1) [1,4,64] r38115 c38115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23800
  · exact u23801
  · exact u23802

def r38116 : Route 9 := (fun mask => (mask,id))

def c38116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38116 : Upper (D 6) (R 6) [34,136,66,272,96] 13 := by
  apply FastRouting.sound _ _ [34,136,66,272,96] 13 (by decide) (choices 1) [1,4] r38116 c38116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u23803
  · exact u23804

def b38117 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 35 138 70 296 21 117 85 213 341), lower := (rows 35 138 70 296 21 32 64 128 256), losses := [] }

theorem u38117 : Upper (D 6) (R 6) [34,136,66,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38118 : Route 9 := (fun mask => (mask,id))

def c38118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38118 : Upper (D 6) (R 6) [34,136,66,288,65] 13 := by
  apply FastRouting.sound _ _ [34,136,66,288,65] 13 (by decide) (choices 1) [1,4,16] r38118 c38118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23805
  · exact u23806
  · exact u23807

def b38119 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 70 296 84 53 85 149 277), lower := (rows 35 138 70 296 84 32 64 128 256), losses := [] }

theorem u38119 : Upper (D 6) (R 6) [34,136,66,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38120 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 84 13 19 356 356 484 356), lower := (rows 35 138 84 13 19 32 64 128 256), losses := [] }

theorem u38120 : Upper (D 6) (R 6) [34,136,80,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38121 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 138 84 13 21 354 354 482 354), lower := (rows 35 138 84 13 21 32 64 128 256), losses := [] }

theorem u38121 : Upper (D 6) (R 6) [34,136,80,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38122 : Route 9 := (fun mask => (mask,id))

def c38122 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u38122 : Upper (D 6) (R 6) [34,136,80,5,6] 13 := by
  apply FastRouting.sound _ _ [34,136,80,5,6] 13 (by decide) (choices 1) [1,64,256] r38122 c38122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23808
  · exact u23809
  · exact u23810

def b38123 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 84 13 49 358 326 454 326), lower := (rows 35 138 84 13 49 32 64 128 256), losses := [] }

theorem u38123 : Upper (D 6) (R 6) [34,136,80,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38124 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 84 13 50 357 325 453 325), lower := (rows 35 138 84 13 50 32 64 128 256), losses := [] }

theorem u38124 : Upper (D 6) (R 6) [34,136,80,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38125 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 483, targets := 4 },{ cop := 3, region := 450, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 138 84 13 52 355 323 451 323), lower := (rows 35 138 84 13 52 32 64 128 256), losses := [] }

theorem u38125 : Upper (D 6) (R 6) [34,136,80,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38126 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 12, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 35 138 84 13 81 294 358 422 294), lower := (rows 35 138 84 13 81 32 64 128 256), losses := [] }

theorem u38126 : Upper (D 6) (R 6) [34,136,80,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38126 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38127 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 13 82 293 357 421 293), lower := (rows 35 138 84 13 82 32 64 128 256), losses := [] }

theorem u38127 : Upper (D 6) (R 6) [34,136,80,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38128 : PairBound 9 := { available := 291, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 138 84 13 84 291 355 419 291), lower := (rows 35 138 84 13 84 32 64 128 256), losses := [] }

theorem u38128 : Upper (D 6) (R 6) [34,136,80,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38129 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 13 112 295 327 391 263), lower := (rows 35 138 84 13 112 32 64 128 256), losses := [] }

theorem u38129 : Upper (D 6) (R 6) [34,136,80,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38130 : Route 9 := (fun mask => (mask,id))

def c38130 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38130 : Upper (D 6) (R 6) [34,136,80,5,257] 13 := by
  apply FastRouting.sound _ _ [34,136,80,5,257] 13 (by decide) (choices 1) [2,4,64] r38130 c38130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23811
  · exact u23812
  · exact u23813

def r38131 : Route 9 := (fun mask => (mask,id))

def c38131 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38131 : Upper (D 6) (R 6) [34,136,80,5,258] 13 := by
  apply FastRouting.sound _ _ [34,136,80,5,258] 13 (by decide) (choices 1) [1,4,64] r38131 c38131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23814
  · exact u23815
  · exact u23816

def r38132 : Route 9 := (fun mask => (mask,id))

def c38132 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38132 : Upper (D 6) (R 6) [34,136,80,5,260] 13 := by
  apply FastRouting.sound _ _ [34,136,80,5,260] 13 (by decide) (choices 1) [1,2,64] r38132 c38132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23817
  · exact u23818
  · exact u23819

def r38133 : Route 9 := (fun mask => (mask,id))

def c38133 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38133 : Upper (D 6) (R 6) [34,136,80,5,288] 13 := by
  apply FastRouting.sound _ _ [34,136,80,5,288] 13 (by decide) (choices 1) [1,2,4,64] r38133 c38133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23820
  · exact u23821
  · exact u23822
  · exact u23823

def b38134 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 13 336 39 103 167 295), lower := (rows 35 138 84 13 336 32 64 128 256), losses := [] }

theorem u38134 : Upper (D 6) (R 6) [34,136,80,5,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38135 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 353, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 84 14 21 353 353 481 353), lower := (rows 35 138 84 14 21 32 64 128 256), losses := [] }

theorem u38135 : Upper (D 6) (R 6) [34,136,80,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38136 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 138 84 14 49 357 325 453 325), lower := (rows 35 138 84 14 49 32 64 128 256), losses := [] }

theorem u38136 : Upper (D 6) (R 6) [34,136,80,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38137 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 353, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 84 14 52 353 321 449 321), lower := (rows 35 138 84 14 52 32 64 128 256), losses := [] }

theorem u38137 : Upper (D 6) (R 6) [34,136,80,6,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38138 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 14 81 293 357 421 293), lower := (rows 35 138 84 14 81 32 64 128 256), losses := [] }

theorem u38138 : Upper (D 6) (R 6) [34,136,80,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38139 : PairBound 9 := { available := 289, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 138 84 14 84 289 353 417 289), lower := (rows 35 138 84 14 84 32 64 128 256), losses := [] }

theorem u38139 : Upper (D 6) (R 6) [34,136,80,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38140 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 14 112 293 325 389 261), lower := (rows 35 138 84 14 112 32 64 128 256), losses := [] }

theorem u38140 : Upper (D 6) (R 6) [34,136,80,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38141 : Route 9 := (fun mask => (mask,id))

def c38141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38141 : Upper (D 6) (R 6) [34,136,80,6,257] 13 := by
  apply FastRouting.sound _ _ [34,136,80,6,257] 13 (by decide) (choices 1) [1,4,64] r38141 c38141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23824
  · exact u23825
  · exact u23826

def b38142 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 84 14 276 97 97 225 353), lower := (rows 35 138 84 14 276 32 64 128 256), losses := [] }

theorem u38142 : Upper (D 6) (R 6) [34,136,80,6,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38143 : Route 9 := (fun mask => (mask,id))

def c38143 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38143 : Upper (D 6) (R 6) [34,136,80,6,288] 13 := by
  apply FastRouting.sound _ _ [34,136,80,6,288] 13 (by decide) (choices 1) [1,4,64] r38143 c38143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23827
  · exact u23828
  · exact u23829

def b38144 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 14 336 37 101 165 293), lower := (rows 35 138 84 14 336 32 64 128 256), losses := [] }

theorem u38144 : Upper (D 6) (R 6) [34,136,80,6,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38145 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 138 84 44 19 357 325 453 325), lower := (rows 35 138 84 44 19 32 64 128 256), losses := [] }

theorem u38145 : Upper (D 6) (R 6) [34,136,80,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38146 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 451, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 44 21 355 323 451 323), lower := (rows 35 138 84 44 21 32 64 128 256), losses := [] }

theorem u38146 : Upper (D 6) (R 6) [34,136,80,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38147 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 451, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 44 22 353 321 449 321), lower := (rows 35 138 84 44 22 32 64 128 256), losses := [] }

theorem u38147 : Upper (D 6) (R 6) [34,136,80,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38148 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 44 81 295 327 391 263), lower := (rows 35 138 84 44 81 32 64 128 256), losses := [] }

theorem u38148 : Upper (D 6) (R 6) [34,136,80,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38149 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 44 82 293 325 389 261), lower := (rows 35 138 84 44 82 32 64 128 256), losses := [] }

theorem u38149 : Upper (D 6) (R 6) [34,136,80,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38150 : PairBound 9 := { available := 259, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 138 84 44 84 291 323 387 259), lower := (rows 35 138 84 44 84 32 64 128 256), losses := [] }

theorem u38150 : Upper (D 6) (R 6) [34,136,80,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38151 : Route 9 := (fun mask => (mask,id))

def c38151 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38151 : Upper (D 6) (R 6) [34,136,80,36,257] 13 := by
  apply FastRouting.sound _ _ [34,136,80,36,257] 13 (by decide) (choices 1) [1,2,4,64] r38151 c38151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u23830
  · exact u23831
  · exact u23832
  · exact u23833

def r38152 : Route 9 := (fun mask => (mask,id))

def c38152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38152 : Upper (D 6) (R 6) [34,136,80,36,258] 13 := by
  apply FastRouting.sound _ _ [34,136,80,36,258] 13 (by decide) (choices 1) [1,4,64] r38152 c38152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23834
  · exact u23835
  · exact u23836

def b38153 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 195, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 44 276 99 67 195 323), lower := (rows 35 138 84 44 276 32 64 128 256), losses := [] }

theorem u38153 : Upper (D 6) (R 6) [34,136,80,36,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38154 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 84 44 336 39 71 135 263), lower := (rows 35 138 84 44 336 32 64 128 256), losses := [] }

theorem u38154 : Upper (D 6) (R 6) [34,136,80,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38155 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 84 73 19 292 356 420 292), lower := (rows 35 138 84 73 19 32 64 128 256), losses := [] }

theorem u38155 : Upper (D 6) (R 6) [34,136,80,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38156 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 20, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 35 138 84 73 21 294 358 422 294), lower := (rows 35 138 84 73 21 32 64 128 256), losses := [] }

theorem u38156 : Upper (D 6) (R 6) [34,136,80,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38157 : Route 9 := (fun mask => (mask,id))

def c38157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u38157 : Upper (D 6) (R 6) [34,136,80,65,6] 13 := by
  apply FastRouting.sound _ _ [34,136,80,65,6] 13 (by decide) (choices 1) [1,4,256] r38157 c38157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u23837
  · exact u23838
  · exact u23839

def b38158 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 84 73 49 294 326 390 262), lower := (rows 35 138 84 73 49 32 64 128 256), losses := [] }

theorem u38158 : Upper (D 6) (R 6) [34,136,80,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38159 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 84 73 50 293 325 389 261), lower := (rows 35 138 84 73 50 32 64 128 256), losses := [] }

theorem u38159 : Upper (D 6) (R 6) [34,136,80,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u38159
end Delivery.IrregularNine14.P06
