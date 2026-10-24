import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0012
import IrregularNine14P09C0013

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3720 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 35 7 196 296 336 33 216 152 408), lower := (rows 35 7 196 296 336 33 64 128 256), losses := [] }

theorem u3720 : Upper (D 9) (R 9) [34,5,192,288,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3720 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3721 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 470, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 35 7 196 296 336 40 209 145 401), lower := (rows 35 7 196 296 336 40 64 128 256), losses := [] }

theorem u3721 : Upper (D 9) (R 9) [34,5,192,288,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3721 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3722 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 7 196 296 336 48 201 137 393), lower := (rows 35 7 196 296 336 48 64 128 256), losses := [] }

theorem u3722 : Upper (D 9) (R 9) [34,5,192,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3722 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3723 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 35, targets := 320 },{ cop := 0, region := 344, targets := 128 }], pairs := [(0,6),(0,8),(1,6),(1,8),(3,7)], upper := (rows 35 7 196 296 336 160 89 153 281), lower := (rows 35 7 196 296 336 160 64 128 256), losses := [] }

theorem u3723 : Upper (D 9) (R 9) [34,5,192,288,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3723 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3724 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 35, targets := 448 }], pairs := [(0,6),(0,7),(0,8),(1,6),(1,7)], upper := (rows 35 7 196 328 400 33 120 184 312), lower := (rows 35 7 196 328 400 33 64 128 256), losses := [] }

theorem u3724 : Upper (D 9) (R 9) [34,5,192,320,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3724 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3725 : Route 9 := (fun mask => (mask,id))

def c3725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3725 : Upper (D 9) (R 9) [34,5,192,320,384,8] 13 := by
  apply FastRouting.sound _ _ [34,5,192,320,384,8] 13 (by decide) (choices 1) [1,16,32] r3725 c3725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u779
  · exact u780
  · exact u781

def b3726 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 2, region := 458, targets := 32 },{ cop := 0, region := 400, targets := 1 }], pairs := [(1,5),(2,6),(3,5),(4,0),(4,6)], upper := (rows 35 14 21 73 176 96 448 384 384), lower := (rows 35 14 21 73 176 96 64 128 256), losses := [] }

theorem u3726 : Upper (D 9) (R 9) [34,12,17,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3726 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3727 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 335, targets := 128 },{ cop := 2, region := 330, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,7),(3,7)], upper := (rows 35 14 21 73 176 160 320 448 320), lower := (rows 35 14 21 73 176 160 64 128 256), losses := [] }

theorem u3727 : Upper (D 9) (R 9) [34,12,17,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3727 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3728 : Route 9 := (fun mask => (mask,id))

def c3728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3728 : Upper (D 9) (R 9) [34,12,17,65,160,256] 13 := by
  apply FastRouting.sound _ _ [34,12,17,65,160,256] 13 (by decide) (choices 1) [128,256] r3728 c3728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u782
  · exact u783

def b3729 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 14 21 73 208 160 352 416 288), lower := (rows 35 14 21 73 208 160 64 128 256), losses := [] }

theorem u3729 : Upper (D 9) (R 9) [34,12,17,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3729 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3730 : Route 9 := (fun mask => (mask,id))

def c3730 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3730 : Upper (D 9) (R 9) [34,12,17,65,192,256] 13 := by
  apply FastRouting.sound _ _ [34,12,17,65,192,256] 13 (by decide) (choices 1) [32,128,256] r3730 c3730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u784
  · exact u785
  · exact u786

def b3731 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(1,6),(2,6),(4,0),(4,6)], upper := (rows 35 14 21 73 400 96 480 416 416), lower := (rows 35 14 21 73 400 96 64 128 256), losses := [{ target := 6, region := (rows 1 10 13 8 61 32 0 161 289), good := (rows 439 30 405 415 400 432 0 128 256) },{ target := 7, region := (rows 3 2 4 8 16 104 64 0 256), good := (rows 35 47 21 105 272 96 96 0 256) }] }

theorem u3731 : Upper (D 9) (R 9) [34,12,17,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3731 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3732 : Route 9 := (fun mask => (mask,id))

def c3732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3732 : Upper (D 9) (R 9) [34,12,17,65,384,128] 13 := by
  apply FastRouting.sound _ _ [34,12,17,65,384,128] 13 (by decide) (choices 1) [32,256] r3732 c3732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u787
  · exact u788

def b3733 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 14 21 104 208 33 448 384 384), lower := (rows 35 14 21 104 208 33 64 128 256), losses := [] }

theorem u3733 : Upper (D 9) (R 9) [34,12,17,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3733 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3734 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 0, region := 468, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8),(3,8)], upper := (rows 35 14 21 104 208 160 321 385 257), lower := (rows 35 14 21 104 208 160 64 128 256), losses := [] }

theorem u3734 : Upper (D 9) (R 9) [34,12,17,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3734 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3735 : Route 9 := (fun mask => (mask,id))

def c3735 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3735 : Upper (D 9) (R 9) [34,12,17,96,192,256] 13 := by
  apply FastRouting.sound _ _ [34,12,17,96,192,256] 13 (by decide) (choices 1) [1,128,256] r3735 c3735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u789
  · exact u790
  · exact u791

def b3736 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 14 21 104 400 33 448 448 448), lower := (rows 35 14 21 104 400 33 64 128 256), losses := [] }

theorem u3736 : Upper (D 9) (R 9) [34,12,17,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3736 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3737 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 407, targets := 64 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0),(4,6)], upper := (rows 35 14 21 104 400 96 449 385 385), lower := (rows 35 14 21 104 400 96 64 128 256), losses := [] }

theorem u3737 : Upper (D 9) (R 9) [34,12,17,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3737 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3738 : Route 9 := (fun mask => (mask,id))

def c3738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3738 : Upper (D 9) (R 9) [34,12,17,96,384,128] 13 := by
  apply FastRouting.sound _ _ [34,12,17,96,384,128] 13 (by decide) (choices 1) [1,256] r3738 c3738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u792
  · exact u793

def b3739 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 55, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 14 21 200 112 33 448 384 384), lower := (rows 35 14 21 200 112 33 64 128 256), losses := [] }

theorem u3739 : Upper (D 9) (R 9) [34,12,17,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3739 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3740 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 55, targets := 256 },{ cop := 0, region := 340, targets := 128 }], pairs := [(0,8),(1,8),(2,7),(2,8),(4,8)], upper := (rows 35 14 21 200 112 160 321 385 257), lower := (rows 35 14 21 200 112 160 64 128 256), losses := [] }

theorem u3740 : Upper (D 9) (R 9) [34,12,17,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3740 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3741 : Route 9 := (fun mask => (mask,id))

def c3741 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3741 : Upper (D 9) (R 9) [34,12,17,192,96,256] 13 := by
  apply FastRouting.sound _ _ [34,12,17,192,96,256] 13 (by decide) (choices 1) [1,128,256] r3741 c3741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u794
  · exact u795
  · exact u796

def b3742 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 458, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 14 21 200 304 33 448 448 448), lower := (rows 35 14 21 200 304 33 64 128 256), losses := [] }

theorem u3742 : Upper (D 9) (R 9) [34,12,17,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3742 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3743 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 404, targets := 64 },{ cop := 2, region := 458, targets := 32 }], pairs := [(0,7),(1,5),(2,6),(3,5),(4,6)], upper := (rows 35 14 21 200 304 96 449 385 385), lower := (rows 35 14 21 200 304 96 64 128 256), losses := [{ target := 7, region := (rows 3 2 4 8 16 104 64 0 256), good := (rows 35 47 21 104 304 96 96 0 256) }] }

theorem u3743 : Upper (D 9) (R 9) [34,12,17,192,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3743 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3744 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 14 21 200 304 288 193 193 449), lower := (rows 35 14 21 200 304 288 64 128 256), losses := [] }

theorem u3744 : Upper (D 9) (R 9) [34,12,17,192,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3744 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3745 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 14 21 200 336 33 480 416 416), lower := (rows 35 14 21 200 336 33 64 128 256), losses := [] }

theorem u3745 : Upper (D 9) (R 9) [34,12,17,192,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3745 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3746 : Route 9 := (fun mask => (mask,id))

def c3746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3746 : Upper (D 9) (R 9) [34,12,17,192,320,128] 13 := by
  apply FastRouting.sound _ _ [34,12,17,192,320,128] 13 (by decide) (choices 1) [1,32,256] r3746 c3746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u797
  · exact u798
  · exact u799

def r3747 : Route 9 := (fun mask => (mask,id))

def c3747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3747 : Upper (D 9) (R 9) [34,12,17,192,320,256] 13 := by
  apply FastRouting.sound _ _ [34,12,17,192,320,256] 13 (by decide) (choices 1) [1,32,128] r3747 c3747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u800
  · exact u801
  · exact u802

def b3748 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 404, targets := 64 },{ cop := 4, region := 356, targets := 1 }], pairs := [(2,0),(2,6),(3,5),(4,5),(4,6)], upper := (rows 35 14 52 73 145 96 448 384 384), lower := (rows 35 14 52 73 145 96 64 128 256), losses := [] }

theorem u3748 : Upper (D 9) (R 9) [34,12,48,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3748 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3749 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(3,7),(4,5)], upper := (rows 35 14 52 73 145 160 320 448 320), lower := (rows 35 14 52 73 145 160 64 128 256), losses := [] }

theorem u3749 : Upper (D 9) (R 9) [34,12,48,65,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3749 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3750 : Route 9 := (fun mask => (mask,id))

def c3750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3750 : Upper (D 9) (R 9) [34,12,48,65,129,256] 13 := by
  apply FastRouting.sound _ _ [34,12,48,65,129,256] 13 (by decide) (choices 1) [128,256] r3750 c3750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u803
  · exact u804

def b3751 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 14 52 73 208 33 448 384 384), lower := (rows 35 14 52 73 208 33 64 128 256), losses := [] }

theorem u3751 : Upper (D 9) (R 9) [34,12,48,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3751 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3752 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 14 52 73 208 160 321 385 257), lower := (rows 35 14 52 73 208 160 64 128 256), losses := [] }

theorem u3752 : Upper (D 9) (R 9) [34,12,48,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3752 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3753 : Route 9 := (fun mask => (mask,id))

def c3753 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3753 : Upper (D 9) (R 9) [34,12,48,65,192,256] 13 := by
  apply FastRouting.sound _ _ [34,12,48,65,192,256] 13 (by decide) (choices 1) [1,128,256] r3753 c3753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u805
  · exact u806
  · exact u807

def b3754 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 468, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(2,0),(4,0)], upper := (rows 35 14 52 73 400 33 448 448 448), lower := (rows 35 14 52 73 400 33 64 128 256), losses := [] }

theorem u3754 : Upper (D 9) (R 9) [34,12,48,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3754 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3755 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,5),(4,6)], upper := (rows 35 14 52 73 400 96 449 385 385), lower := (rows 35 14 52 73 400 96 64 128 256), losses := [{ target := 6, region := (rows 1 10 5 8 27 32 0 137 265), good := (rows 439 414 52 415 400 32 0 128 256) }] }

theorem u3755 : Upper (D 9) (R 9) [34,12,48,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3755 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3756 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(3,7)], upper := (rows 35 14 52 73 400 160 321 449 321), lower := (rows 35 14 52 73 400 160 64 128 256), losses := [] }

theorem u3756 : Upper (D 9) (R 9) [34,12,48,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3756 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3757 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 458, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 14 52 200 273 33 448 448 448), lower := (rows 35 14 52 200 273 33 64 128 256), losses := [] }

theorem u3757 : Upper (D 9) (R 9) [34,12,48,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3757 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3758 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(1,5),(2,6),(3,5),(4,5),(4,6)], upper := (rows 35 14 52 200 273 96 449 385 385), lower := (rows 35 14 52 200 273 96 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 29 17 0 81 145 273), good := (rows 475 14 478 200 473 64 64 128 256) }] }

theorem u3758 : Upper (D 9) (R 9) [34,12,48,192,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3758 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3759 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 203, targets := 256 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(3,8)], upper := (rows 35 14 52 200 273 288 193 193 449), lower := (rows 35 14 52 200 273 288 64 128 256), losses := [] }

theorem u3759 : Upper (D 9) (R 9) [34,12,48,192,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3759 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3760 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,5),(4,5)], upper := (rows 35 14 52 200 336 33 449 385 385), lower := (rows 35 14 52 200 336 33 64 128 256), losses := [] }

theorem u3760 : Upper (D 9) (R 9) [34,12,48,192,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3760 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3761 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 340, targets := 128 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(2,7),(3,5),(4,5),(4,7)], upper := (rows 35 14 52 200 336 160 321 385 257), lower := (rows 35 14 52 200 336 160 64 128 256), losses := [] }

theorem u3761 : Upper (D 9) (R 9) [34,12,48,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3761 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3762 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 203, targets := 256 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(3,8)], upper := (rows 35 14 52 200 336 288 193 129 385), lower := (rows 35 14 52 200 336 288 64 128 256), losses := [] }

theorem u3762 : Upper (D 9) (R 9) [34,12,48,192,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3762 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3763 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 324, targets := 128 },{ cop := 4, region := 360, targets := 1 }], pairs := [(0,6),(1,7),(2,7),(3,0),(4,6)], upper := (rows 35 14 69 88 145 160 352 416 288), lower := (rows 35 14 69 88 145 160 64 128 256), losses := [{ target := 7, region := (rows 1 26 21 24 16 32 97 0 289), good := (rows 359 14 325 94 351 352 64 0 256) }] }

theorem u3763 : Upper (D 9) (R 9) [34,12,65,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3763 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3764 : Route 9 := (fun mask => (mask,id))

def c3764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3764 : Upper (D 9) (R 9) [34,12,65,80,129,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,80,129,256] 13 (by decide) (choices 1) [32,128,256] r3764 c3764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u808
  · exact u809
  · exact u810

def b3765 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 14 69 88 176 33 448 384 384), lower := (rows 35 14 69 88 176 33 64 128 256), losses := [] }

theorem u3765 : Upper (D 9) (R 9) [34,12,65,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3765 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3766 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 335, targets := 128 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 35 14 69 88 176 160 321 385 257), lower := (rows 35 14 69 88 176 160 64 128 256), losses := [] }

theorem u3766 : Upper (D 9) (R 9) [34,12,65,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3766 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3767 : Route 9 := (fun mask => (mask,id))

def c3767 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3767 : Upper (D 9) (R 9) [34,12,65,80,160,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,80,160,256] 13 (by decide) (choices 1) [1,128,256] r3767 c3767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u811
  · exact u812
  · exact u813

def b3768 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 14 69 88 400 33 480 416 416), lower := (rows 35 14 69 88 400 33 64 128 256), losses := [] }

theorem u3768 : Upper (D 9) (R 9) [34,12,65,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3768 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3769 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 324, targets := 128 }], pairs := [(0,6),(0,8),(1,8),(2,7),(4,6)], upper := (rows 35 14 69 88 400 160 353 417 289), lower := (rows 35 14 69 88 400 160 64 128 256), losses := [{ target := 8, region := (rows 9 10 12 8 16 176 64 128 0), good := (rows 35 15 69 127 176 160 64 160 0) }] }

theorem u3769 : Upper (D 9) (R 9) [34,12,65,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3769 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3770 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 2, region := 394, targets := 64 }], pairs := [(1,5),(1,6),(2,5),(3,5)], upper := (rows 35 14 69 137 112 48 448 384 384), lower := (rows 35 14 69 137 112 48 64 128 256), losses := [] }

theorem u3770 : Upper (D 9) (R 9) [34,12,65,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3770 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3771 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 0, region := 336, targets := 1 }], pairs := [(0,6),(1,7),(2,7),(4,0),(4,7)], upper := (rows 35 14 69 137 112 160 336 400 272), lower := (rows 35 14 69 137 112 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 184 0 144 272), good := (rows 35 47 5 169 432 160 0 160 256) },{ target := 7, region := (rows 1 10 13 8 49 32 125 0 317), good := (rows 375 334 341 351 368 368 64 0 256) }] }

theorem u3771 : Upper (D 9) (R 9) [34,12,65,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3771 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3772 : Route 9 := (fun mask => (mask,id))

def c3772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u3772 : Upper (D 9) (R 9) [34,12,65,129,96,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,129,96,256] 13 (by decide) (choices 1) [16,128,256] r3772 c3772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u814
  · exact u815
  · exact u816

def b3773 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 14 69 137 208 48 352 416 288), lower := (rows 35 14 69 137 208 48 64 128 256), losses := [] }

theorem u3773 : Upper (D 9) (R 9) [34,12,65,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3773 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3774 : Route 9 := (fun mask => (mask,id))

def c3774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u3774 : Upper (D 9) (R 9) [34,12,65,129,192,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,129,192,256] 13 (by decide) (choices 1) [16,32,256] r3774 c3774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u817
  · exact u818
  · exact u819

def b3775 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 35 14 69 137 304 48 448 448 448), lower := (rows 35 14 69 137 304 48 64 128 256), losses := [] }

theorem u3775 : Upper (D 9) (R 9) [34,12,65,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3775 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3776 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(1,6),(3,6),(4,0),(4,6)], upper := (rows 35 14 69 137 304 96 464 400 400), lower := (rows 35 14 69 137 304 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 13 49 32 0 189 317), good := (rows 443 398 415 409 432 432 0 128 256) },{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 47 101 9 304 96 96 0 256) }] }

theorem u3776 : Upper (D 9) (R 9) [34,12,65,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3776 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3777 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 64 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,6)], upper := (rows 35 14 69 137 304 288 208 208 464), lower := (rows 35 14 69 137 304 288 64 128 256), losses := [] }

theorem u3777 : Upper (D 9) (R 9) [34,12,65,129,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3777 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3778 : Route 9 := (fun mask => (mask,id))

def c3778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3778 : Upper (D 9) (R 9) [34,12,65,129,320,16] 13 := by
  apply FastRouting.sound _ _ [34,12,65,129,320,16] 13 (by decide) (choices 1) [32,128,256] r3778 c3778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u820
  · exact u821
  · exact u822

def b3779 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 0, region := 336, targets := 1 }], pairs := [(0,6),(1,7),(2,7),(4,0),(4,7)], upper := (rows 35 14 69 137 336 160 368 432 304), lower := (rows 35 14 69 137 336 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 184 0 144 272), good := (rows 35 47 5 169 432 160 0 160 256) },{ target := 7, region := (rows 1 10 13 8 61 32 97 0 289), good := (rows 375 30 341 351 336 368 64 0 256) }] }

theorem u3779 : Upper (D 9) (R 9) [34,12,65,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3779 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u3779
end Delivery.IrregularNine14.P09
