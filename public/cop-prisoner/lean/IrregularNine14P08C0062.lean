import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0008

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3720 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 200 280 33 116 180 308), lower := (rows 67 162 37 200 280 33 64 128 256), losses := [] }

theorem u3720 : Upper (D 8) (R 8) [66,160,33,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3720 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3721 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 162 37 200 280 36 113 177 305), lower := (rows 67 162 37 200 280 36 64 128 256), losses := [] }

theorem u3721 : Upper (D 8) (R 8) [66,160,33,192,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3721 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3722 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 162 37 200 280 48 101 165 293), lower := (rows 67 162 37 200 280 48 64 128 256), losses := [] }

theorem u3722 : Upper (D 8) (R 8) [66,160,33,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3722 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3723 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 200 304 33 92 156 284), lower := (rows 67 162 37 200 304 33 64 128 256), losses := [] }

theorem u3723 : Upper (D 8) (R 8) [66,160,33,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3724 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 67 162 37 200 304 36 89 153 281), lower := (rows 67 162 37 200 304 36 64 128 256), losses := [] }

theorem u3724 : Upper (D 8) (R 8) [66,160,33,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3724 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3725 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 67 162 37 200 304 40 85 149 277), lower := (rows 67 162 37 200 304 40 64 128 256), losses := [] }

theorem u3725 : Upper (D 8) (R 8) [66,160,33,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3725 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3726 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 67 162 37 200 304 48 77 141 269), lower := (rows 67 162 37 200 304 48 64 128 256), losses := [] }

theorem u3726 : Upper (D 8) (R 8) [66,160,33,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3726 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3727 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 130, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 44 88 273 33 228 164 420), lower := (rows 67 162 44 88 273 33 64 128 256), losses := [] }

theorem u3727 : Upper (D 8) (R 8) [66,160,40,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3728 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 162 44 88 273 36 225 161 417), lower := (rows 67 162 44 88 273 36 64 128 256), losses := [] }

theorem u3728 : Upper (D 8) (R 8) [66,160,40,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3728 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3729 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 44 88 273 160 101 165 293), lower := (rows 67 162 44 88 273 160 64 128 256), losses := [] }

theorem u3729 : Upper (D 8) (R 8) [66,160,40,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3730 : Route 9 := (fun mask => (mask,id))

def c3730 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3730 : Upper (D 8) (R 8) [66,160,40,80,288,1] 13 := by
  apply FastRouting.sound _ _ [66,160,40,80,288,1] 13 (by decide) (choices 1) [1,4,128] r3730 c3730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u481
  · exact u482
  · exact u483

def b3731 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 162 44 88 304 36 193 129 385), lower := (rows 67 162 44 88 304 36 64 128 256), losses := [] }

theorem u3731 : Upper (D 8) (R 8) [66,160,40,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3731 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3732 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 44 88 304 160 69 133 261), lower := (rows 67 162 44 88 304 160 64 128 256), losses := [] }

theorem u3732 : Upper (D 8) (R 8) [66,160,40,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3732 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3733 : Route 9 := (fun mask => (mask,id))

def c3733 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3733 : Upper (D 8) (R 8) [66,160,40,80,384,1] 13 := by
  apply FastRouting.sound _ _ [66,160,40,80,384,1] 13 (by decide) (choices 1) [1,4,32] r3733 c3733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u484
  · exact u485
  · exact u486

def b3734 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 44 88 400 36 97 161 289), lower := (rows 67 162 44 88 400 36 64 128 256), losses := [] }

theorem u3734 : Upper (D 8) (R 8) [66,160,40,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3734 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3735 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 162 44 152 112 33 325 389 261), lower := (rows 67 162 44 152 112 33 64 128 256), losses := [] }

theorem u3735 : Upper (D 8) (R 8) [66,160,40,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3736 : PairBound 9 := { available := 257, camps := [], pairs := [], upper := (rows 67 162 44 152 112 36 321 385 257), lower := (rows 67 162 44 152 112 36 64 128 256), losses := [] }

theorem u3736 : Upper (D 8) (R 8) [66,160,40,144,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3736 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3737 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 67 162 44 152 112 288 69 133 261), lower := (rows 67 162 44 152 112 288 64 128 256), losses := [] }

theorem u3737 : Upper (D 8) (R 8) [66,160,40,144,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3737 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3738 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 44 152 273 33 100 228 356), lower := (rows 67 162 44 152 273 33 64 128 256), losses := [] }

theorem u3738 : Upper (D 8) (R 8) [66,160,40,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3739 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 162 44 152 273 36 97 225 353), lower := (rows 67 162 44 152 273 36 64 128 256), losses := [] }

theorem u3739 : Upper (D 8) (R 8) [66,160,40,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3739 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3740 : Route 9 := (fun mask => (mask,id))

def c3740 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3740 : Upper (D 8) (R 8) [66,160,40,144,257,64] 13 := by
  apply FastRouting.sound _ _ [66,160,40,144,257,64] 13 (by decide) (choices 1) [1,4,32] r3740 c3740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u487
  · exact u488
  · exact u489

def r3741 : Route 9 := (fun mask => (mask,id))

def c3741 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3741 : Upper (D 8) (R 8) [66,160,40,144,288,1] 13 := by
  apply FastRouting.sound _ _ [66,160,40,144,288,1] 13 (by decide) (choices 1) [1,4] r3741 c3741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u490
  · exact u491

def b3742 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 67 162 44 152 304 36 65 193 321), lower := (rows 67 162 44 152 304 36 64 128 256), losses := [] }

theorem u3742 : Upper (D 8) (R 8) [66,160,40,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3742 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3743 : Route 9 := (fun mask => (mask,id))

def c3743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3743 : Upper (D 8) (R 8) [66,160,40,144,288,64] 13 := by
  apply FastRouting.sound _ _ [66,160,40,144,288,64] 13 (by decide) (choices 1) [1,4] r3743 c3743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u492
  · exact u493

def r3744 : Route 9 := (fun mask => (mask,id))

def c3744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3744 : Upper (D 8) (R 8) [66,160,40,144,320,1] 13 := by
  apply FastRouting.sound _ _ [66,160,40,144,320,1] 13 (by decide) (choices 1) [1,4,32] r3744 c3744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u494
  · exact u495
  · exact u496

def b3745 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 44 152 336 36 97 161 289), lower := (rows 67 162 44 152 336 36 64 128 256), losses := [] }

theorem u3745 : Upper (D 8) (R 8) [66,160,40,144,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3745 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3746 : Route 9 := (fun mask => (mask,id))

def c3746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3746 : Upper (D 8) (R 8) [66,160,40,192,257,1] 13 := by
  apply FastRouting.sound _ _ [66,160,40,192,257,1] 13 (by decide) (choices 1) [4,16,32] r3746 c3746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u497
  · exact u498
  · exact u499

def b3747 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 162 44 200 273 36 113 177 305), lower := (rows 67 162 44 200 273 36 64 128 256), losses := [] }

theorem u3747 : Upper (D 8) (R 8) [66,160,40,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3747 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3748 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 162 44 200 273 48 101 165 293), lower := (rows 67 162 44 200 273 48 64 128 256), losses := [] }

theorem u3748 : Upper (D 8) (R 8) [66,160,40,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3748 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3749 : Route 9 := (fun mask => (mask,id))

def c3749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3749 : Upper (D 8) (R 8) [66,160,40,192,260,1] 13 := by
  apply FastRouting.sound _ _ [66,160,40,192,260,1] 13 (by decide) (choices 1) [1,16,32] r3749 c3749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u500
  · exact u501
  · exact u502

def b3750 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 44 200 276 48 97 161 289), lower := (rows 67 162 44 200 276 48 64 128 256), losses := [] }

theorem u3750 : Upper (D 8) (R 8) [66,160,40,192,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3750 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3751 : Route 9 := (fun mask => (mask,id))

def c3751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3751 : Upper (D 8) (R 8) [66,160,40,192,288,1] 13 := by
  apply FastRouting.sound _ _ [66,160,40,192,288,1] 13 (by decide) (choices 1) [1,4,16] r3751 c3751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u503
  · exact u504
  · exact u505

def b3752 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 67 162 44 200 304 36 81 145 273), lower := (rows 67 162 44 200 304 36 64 128 256), losses := [] }

theorem u3752 : Upper (D 8) (R 8) [66,160,40,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3752 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3753 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 67 162 44 200 304 48 69 133 261), lower := (rows 67 162 44 200 304 48 64 128 256), losses := [] }

theorem u3753 : Upper (D 8) (R 8) [66,160,40,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3753 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3754 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 44 265 84 33 240 176 432), lower := (rows 67 162 44 265 84 33 64 128 256), losses := [] }

theorem u3754 : Upper (D 8) (R 8) [66,160,40,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3755 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 162 44 265 84 48 225 161 417), lower := (rows 67 162 44 265 84 48 64 128 256), losses := [] }

theorem u3755 : Upper (D 8) (R 8) [66,160,40,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3755 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3756 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 44 265 84 160 113 177 305), lower := (rows 67 162 44 265 84 160 64 128 256), losses := [] }

theorem u3756 : Upper (D 8) (R 8) [66,160,40,257,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3757 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 44 265 112 33 212 148 404), lower := (rows 67 162 44 265 112 33 64 128 256), losses := [] }

theorem u3757 : Upper (D 8) (R 8) [66,160,40,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3757 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3758 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 162 44 265 112 36 209 145 401), lower := (rows 67 162 44 265 112 36 64 128 256), losses := [] }

theorem u3758 : Upper (D 8) (R 8) [66,160,40,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3758 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3759 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 162 44 265 112 48 197 133 389), lower := (rows 67 162 44 265 112 48 64 128 256), losses := [] }

theorem u3759 : Upper (D 8) (R 8) [66,160,40,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3759 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3760 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 44 265 112 160 85 149 277), lower := (rows 67 162 44 265 112 160 64 128 256), losses := [] }

theorem u3760 : Upper (D 8) (R 8) [66,160,40,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3760 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3761 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 44 265 148 33 112 240 368), lower := (rows 67 162 44 265 148 33 64 128 256), losses := [] }

theorem u3761 : Upper (D 8) (R 8) [66,160,40,257,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3761 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3762 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 162 44 265 148 48 97 225 353), lower := (rows 67 162 44 265 148 48 64 128 256), losses := [] }

theorem u3762 : Upper (D 8) (R 8) [66,160,40,257,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3762 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3763 : PairBound 9 := { available := 49, camps := [], pairs := [(2,0)], upper := (rows 67 162 44 265 148 96 113 177 305), lower := (rows 67 162 44 265 148 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 97 64 128 256), good := (rows 98 162 44 300 148 96 96 128 256) }] }

theorem u3763 : Upper (D 8) (R 8) [66,160,40,257,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3764 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 44 265 208 33 116 180 308), lower := (rows 67 162 44 265 208 33 64 128 256), losses := [] }

theorem u3764 : Upper (D 8) (R 8) [66,160,40,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3764 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3765 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 162 44 265 208 36 113 177 305), lower := (rows 67 162 44 265 208 36 64 128 256), losses := [] }

theorem u3765 : Upper (D 8) (R 8) [66,160,40,257,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3765 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3766 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 162 44 265 208 48 101 165 293), lower := (rows 67 162 44 265 208 48 64 128 256), losses := [] }

theorem u3766 : Upper (D 8) (R 8) [66,160,40,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3766 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3767 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 162 44 268 112 33 209 145 401), lower := (rows 67 162 44 268 112 33 64 128 256), losses := [] }

theorem u3767 : Upper (D 8) (R 8) [66,160,40,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3767 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3768 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 162 44 268 112 48 193 129 385), lower := (rows 67 162 44 268 112 48 64 128 256), losses := [] }

theorem u3768 : Upper (D 8) (R 8) [66,160,40,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3768 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3769 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 44 268 112 160 81 145 273), lower := (rows 67 162 44 268 112 160 64 128 256), losses := [] }

theorem u3769 : Upper (D 8) (R 8) [66,160,40,260,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3769 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3770 : Route 9 := (fun mask => (mask,id))

def c3770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3770 : Upper (D 8) (R 8) [66,160,40,260,192,1] 13 := by
  apply FastRouting.sound _ _ [66,160,40,260,192,1] 13 (by decide) (choices 1) [1,16,32] r3770 c3770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u506
  · exact u507
  · exact u508

def b3771 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 44 268 208 48 97 161 289), lower := (rows 67 162 44 268 208 48 64 128 256), losses := [] }

theorem u3771 : Upper (D 8) (R 8) [66,160,40,260,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3771 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3772 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 162 44 280 112 33 197 133 389), lower := (rows 67 162 44 280 112 33 64 128 256), losses := [] }

theorem u3772 : Upper (D 8) (R 8) [66,160,40,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3772 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3773 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 162 44 280 112 36 193 129 385), lower := (rows 67 162 44 280 112 36 64 128 256), losses := [] }

theorem u3773 : Upper (D 8) (R 8) [66,160,40,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3773 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3774 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 44 280 112 160 69 133 261), lower := (rows 67 162 44 280 112 160 64 128 256), losses := [] }

theorem u3774 : Upper (D 8) (R 8) [66,160,40,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3774 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3775 : Route 9 := (fun mask => (mask,id))

def c3775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3775 : Upper (D 8) (R 8) [66,160,40,272,192,1] 13 := by
  apply FastRouting.sound _ _ [66,160,40,272,192,1] 13 (by decide) (choices 1) [1,4,32] r3775 c3775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u509
  · exact u510
  · exact u511

def b3776 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 44 280 208 36 97 161 289), lower := (rows 67 162 44 280 208 36 64 128 256), losses := [] }

theorem u3776 : Upper (D 8) (R 8) [66,160,40,272,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3776 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3777 : Route 9 := (fun mask => (mask,id))

def c3777 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3777 : Upper (D 8) (R 8) [66,160,40,320,132,1] 13 := by
  apply FastRouting.sound _ _ [66,160,40,320,132,1] 13 (by decide) (choices 1) [1,16,32] r3777 c3777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u512
  · exact u513
  · exact u514

def b3778 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 44 328 148 48 97 161 289), lower := (rows 67 162 44 328 148 48 64 128 256), losses := [] }

theorem u3778 : Upper (D 8) (R 8) [66,160,40,320,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3778 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3779 : Route 9 := (fun mask => (mask,id))

def c3779 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3779 : Upper (D 8) (R 8) [66,160,40,384,68,1] 13 := by
  apply FastRouting.sound _ _ [66,160,40,384,68,1] 13 (by decide) (choices 1) [1,16,32] r3779 c3779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u515
  · exact u516
  · exact u517

#print axioms u3779
end Delivery.IrregularNine14.P08
