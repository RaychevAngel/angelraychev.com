import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0003
import IrregularNine14P07C0004

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3720 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 50 100 328 19 160 192 131 259), lower := (rows 13 50 100 328 19 160 192 128 256), losses := [] }

theorem u3720 : Upper (D 7) (R 7) [12,48,96,320,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3721 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 13 50 100 392 81 160 65 130 258), lower := (rows 13 50 100 392 81 160 65 128 256), losses := [] }

theorem u3721 : Upper (D 7) (R 7) [12,48,96,384,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3722 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 68, targets := 129 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,0),(2,7),(3,6)], upper := (rows 13 50 100 392 81 160 66 131 259), lower := (rows 13 50 100 392 81 160 66 128 256), losses := [] }

theorem u3722 : Upper (D 7) (R 7) [12,48,96,384,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3723 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 100 392 146 33 65 194 322), lower := (rows 13 50 100 392 146 33 65 128 256), losses := [] }

theorem u3723 : Upper (D 7) (R 7) [12,48,96,384,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3724 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 429, targets := 2 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(2,1),(3,1)], upper := (rows 13 50 100 392 146 33 66 193 321), lower := (rows 13 50 100 392 146 33 66 128 256), losses := [] }

theorem u3724 : Upper (D 7) (R 7) [12,48,96,384,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3725 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 392, targets := 97 },{ cop := 3, region := 101, targets := 2 }], pairs := [(0,1),(3,0),(3,5),(3,6)], upper := (rows 13 50 100 392 208 33 65 130 258), lower := (rows 13 50 100 392 208 33 65 128 256), losses := [] }

theorem u3725 : Upper (D 7) (R 7) [12,48,96,384,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3726 : Route 9 := (fun mask => (mask,id))

def c3726 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3726 : Upper (D 7) (R 7) [12,48,96,384,192,1,2] 13 := by
  apply FastRouting.sound _ _ [12,48,96,384,192,1,2] 13 (by decide) (choices 1) [1,2] r3726 c3726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u238
  · exact u239

def b3727 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 297, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 50 196 265 82 33 66 160 416), lower := (rows 13 50 196 265 82 33 66 128 256), losses := [] }

theorem u3727 : Upper (D 7) (R 7) [12,48,192,257,66,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3728 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 5, region := 82, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 196 265 82 33 96 130 386), lower := (rows 13 50 196 265 82 33 96 128 256), losses := [] }

theorem u3728 : Upper (D 7) (R 7) [12,48,192,257,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3729 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 50 196 265 82 33 192 162 290), lower := (rows 13 50 196 265 82 33 192 128 256), losses := [] }

theorem u3729 : Upper (D 7) (R 7) [12,48,192,257,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3730 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 182, targets := 1 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(2,0),(4,0)], upper := (rows 13 50 196 265 82 160 65 162 290), lower := (rows 13 50 196 265 82 160 65 128 256), losses := [] }

theorem u3730 : Upper (D 7) (R 7) [12,48,192,257,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3731 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 297, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 50 196 265 82 160 66 161 289), lower := (rows 13 50 196 265 82 160 66 128 256), losses := [] }

theorem u3731 : Upper (D 7) (R 7) [12,48,192,257,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3732 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 18, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 196 265 82 160 96 131 259), lower := (rows 13 50 196 265 82 160 96 128 256), losses := [] }

theorem u3732 : Upper (D 7) (R 7) [12,48,192,257,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3733 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 13 50 196 266 81 160 65 162 290), lower := (rows 13 50 196 266 81 160 65 128 256), losses := [] }

theorem u3733 : Upper (D 7) (R 7) [12,48,192,258,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3734 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 4, region := 164, targets := 2 }], pairs := [(1,6),(2,1),(3,6),(4,5)], upper := (rows 13 50 196 266 81 160 66 161 289), lower := (rows 13 50 196 266 81 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 74 128 256), good := (rows 93 82 196 330 81 128 66 128 256) }] }

theorem u3734 : Upper (D 7) (R 7) [12,48,192,258,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3735 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 5, region := 68, targets := 3 }], pairs := [(1,6),(2,0),(2,1),(3,6)], upper := (rows 13 50 196 266 81 160 96 131 259), lower := (rows 13 50 196 266 81 160 96 128 256), losses := [] }

theorem u3735 : Upper (D 7) (R 7) [12,48,192,258,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3736 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 1, region := 392, targets := 65 }], pairs := [(1,7),(3,0),(3,6),(4,7)], upper := (rows 13 50 196 266 82 33 65 160 416), lower := (rows 13 50 196 266 82 33 65 128 256), losses := [] }

theorem u3736 : Upper (D 7) (R 7) [12,48,192,258,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3737 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 82, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 196 266 82 33 96 129 385), lower := (rows 13 50 196 266 82 33 96 128 256), losses := [] }

theorem u3737 : Upper (D 7) (R 7) [12,48,192,258,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3738 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 50 196 266 82 33 192 161 289), lower := (rows 13 50 196 266 82 33 192 128 256), losses := [] }

theorem u3738 : Upper (D 7) (R 7) [12,48,192,258,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3739 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 13 50 196 296 81 160 65 130 258), lower := (rows 13 50 196 296 81 160 65 128 256), losses := [] }

theorem u3739 : Upper (D 7) (R 7) [12,48,192,288,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3740 : Route 9 := (fun mask => (mask,id))

def c3740 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3740 : Upper (D 7) (R 7) [12,48,192,288,65,128,2] 13 := by
  apply FastRouting.sound _ _ [12,48,192,288,65,128,2] 13 (by decide) (choices 1) [1,2] r3740 c3740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u240
  · exact u241

def b3741 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 1, region := 392, targets := 65 }], pairs := [(1,7),(3,0),(3,6),(4,7)], upper := (rows 13 50 196 296 82 33 65 130 386), lower := (rows 13 50 196 296 82 33 65 128 256), losses := [] }

theorem u3741 : Upper (D 7) (R 7) [12,48,192,288,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3742 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 297, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 50 196 296 82 33 66 129 385), lower := (rows 13 50 196 296 82 33 66 128 256), losses := [] }

theorem u3742 : Upper (D 7) (R 7) [12,48,192,288,66,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3743 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 13 50 196 296 82 33 192 131 259), lower := (rows 13 50 196 296 82 33 192 128 256), losses := [] }

theorem u3743 : Upper (D 7) (R 7) [12,48,192,288,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3744 : Route 9 := (fun mask => (mask,id))

def c3744 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3744 : Upper (D 7) (R 7) [12,48,192,288,66,128,1] 13 := by
  apply FastRouting.sound _ _ [12,48,192,288,66,128,1] 13 (by decide) (choices 1) [1,2] r3744 c3744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u242
  · exact u243

def b3745 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 297, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 13 50 196 296 82 160 66 129 257), lower := (rows 13 50 196 296 82 160 66 128 256), losses := [] }

theorem u3745 : Upper (D 7) (R 7) [12,48,192,288,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3746 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(1,6),(3,7),(4,6)], upper := (rows 13 50 196 328 19 160 65 162 290), lower := (rows 13 50 196 328 19 160 65 128 256), losses := [{ target := 7, region := (rows 1 2 4 26 16 32 81 0 258), good := (rows 77 378 68 328 347 32 65 0 256) }] }

theorem u3746 : Upper (D 7) (R 7) [12,48,192,320,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3747 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 429, targets := 2 },{ cop := 0, region := 178, targets := 64 }], pairs := [(0,1),(1,6),(2,1),(3,1)], upper := (rows 13 50 196 328 19 160 66 161 289), lower := (rows 13 50 196 328 19 160 66 128 256), losses := [] }

theorem u3747 : Upper (D 7) (R 7) [12,48,192,320,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3748 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 5, region := 68, targets := 3 }], pairs := [(1,6),(2,0),(2,1),(4,6)], upper := (rows 13 50 196 328 19 160 96 131 259), lower := (rows 13 50 196 328 19 160 96 128 256), losses := [] }

theorem u3748 : Upper (D 7) (R 7) [12,48,192,320,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3749 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 146, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 196 328 146 33 65 162 290), lower := (rows 13 50 196 328 146 33 65 128 256), losses := [] }

theorem u3749 : Upper (D 7) (R 7) [12,48,192,320,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3750 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 429, targets := 2 },{ cop := 0, region := 178, targets := 64 }], pairs := [(0,1),(1,6),(2,1),(3,1)], upper := (rows 13 50 196 328 146 33 66 161 289), lower := (rows 13 50 196 328 146 33 66 128 256), losses := [] }

theorem u3750 : Upper (D 7) (R 7) [12,48,192,320,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3751 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 178, targets := 64 }], pairs := [(1,6),(2,0),(2,1),(4,6)], upper := (rows 13 50 196 328 146 33 96 131 259), lower := (rows 13 50 196 328 146 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 98 128 256), good := (rows 12 118 196 328 214 96 96 128 256) },{ target := 1, region := (rows 1 0 20 8 16 33 99 128 256), good := (rows 109 116 196 328 212 97 96 128 256) }] }

theorem u3751 : Upper (D 7) (R 7) [12,48,192,320,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3752 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 7 25 176 288 66 192 448), lower := (rows 13 98 7 25 176 288 66 128 256), losses := [] }

theorem u3752 : Upper (D 7) (R 7) [12,96,3,17,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3752 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3753 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 6, region := 290, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 98 7 25 176 288 192 194 322), lower := (rows 13 98 7 25 176 288 192 128 256), losses := [] }

theorem u3753 : Upper (D 7) (R 7) [12,96,3,17,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3753 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3754 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 7 25 304 160 66 192 448), lower := (rows 13 98 7 25 304 160 66 128 256), losses := [] }

theorem u3754 : Upper (D 7) (R 7) [12,96,3,17,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3755 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 7 25 304 160 192 194 322), lower := (rows 13 98 7 25 304 160 192 128 256), losses := [] }

theorem u3755 : Upper (D 7) (R 7) [12,96,3,17,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3756 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 2 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,1)], upper := (rows 13 98 7 25 400 34 192 224 352), lower := (rows 13 98 7 25 400 34 192 128 256), losses := [] }

theorem u3756 : Upper (D 7) (R 7) [12,96,3,17,384,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3757 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 25 400 96 192 162 290), lower := (rows 13 98 7 25 400 96 192 128 256), losses := [] }

theorem u3757 : Upper (D 7) (R 7) [12,96,3,17,384,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3758 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 7 56 146 288 65 192 448), lower := (rows 13 98 7 56 146 288 65 128 256), losses := [] }

theorem u3758 : Upper (D 7) (R 7) [12,96,3,48,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3758 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3759 : Route 9 := (fun mask => (mask,id))

def c3759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3759 : Upper (D 7) (R 7) [12,96,3,48,130,256,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,48,130,256,128] 13 (by decide) (choices 1) [1,64] r3759 c3759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u244
  · exact u245

def b3760 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 7 56 208 288 65 130 386), lower := (rows 13 98 7 56 208 288 65 128 256), losses := [] }

theorem u3760 : Upper (D 7) (R 7) [12,96,3,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3760 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3761 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 7 56 208 288 66 129 385), lower := (rows 13 98 7 56 208 288 66 128 256), losses := [] }

theorem u3761 : Upper (D 7) (R 7) [12,96,3,48,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3761 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3762 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 7 56 208 288 192 131 259), lower := (rows 13 98 7 56 208 288 192 128 256), losses := [] }

theorem u3762 : Upper (D 7) (R 7) [12,96,3,48,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3762 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3763 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 7 56 273 160 66 192 448), lower := (rows 13 98 7 56 273 160 66 128 256), losses := [] }

theorem u3763 : Upper (D 7) (R 7) [12,96,3,48,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3764 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 7 56 273 160 192 194 322), lower := (rows 13 98 7 56 273 160 192 128 256), losses := [] }

theorem u3764 : Upper (D 7) (R 7) [12,96,3,48,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3765 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 6, region := 162, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 7 56 274 160 65 192 448), lower := (rows 13 98 7 56 274 160 65 128 256), losses := [] }

theorem u3765 : Upper (D 7) (R 7) [12,96,3,48,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3766 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 7 56 274 160 192 193 321), lower := (rows 13 98 7 56 274 160 192 128 256), losses := [] }

theorem u3766 : Upper (D 7) (R 7) [12,96,3,48,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3767 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 6, region := 162, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 7 56 336 160 65 130 386), lower := (rows 13 98 7 56 336 160 65 128 256), losses := [] }

theorem u3767 : Upper (D 7) (R 7) [12,96,3,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3768 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 2, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(4,5)], upper := (rows 13 98 7 56 336 160 66 129 385), lower := (rows 13 98 7 56 336 160 66 128 256), losses := [] }

theorem u3768 : Upper (D 7) (R 7) [12,96,3,48,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3769 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 7 56 336 160 192 131 259), lower := (rows 13 98 7 56 336 160 192 128 256), losses := [] }

theorem u3769 : Upper (D 7) (R 7) [12,96,3,48,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3770 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 202, targets := 1 },{ cop := 4, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 13 98 7 152 49 288 66 192 448), lower := (rows 13 98 7 152 49 288 66 128 256), losses := [] }

theorem u3770 : Upper (D 7) (R 7) [12,96,3,144,33,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3770 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3771 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 202, targets := 1 },{ cop := 6, region := 290, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 13 98 7 152 49 288 192 194 322), lower := (rows 13 98 7 152 49 288 192 128 256), losses := [] }

theorem u3771 : Upper (D 7) (R 7) [12,96,3,144,33,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3771 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3772 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,0),(3,0),(4,0),(4,7)], upper := (rows 13 98 7 152 274 33 192 224 352), lower := (rows 13 98 7 152 274 33 192 128 256), losses := [] }

theorem u3772 : Upper (D 7) (R 7) [12,96,3,144,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3773 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 152 274 96 192 161 289), lower := (rows 13 98 7 152 274 96 192 128 256), losses := [] }

theorem u3773 : Upper (D 7) (R 7) [12,96,3,144,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3774 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 7 152 304 33 66 192 448), lower := (rows 13 98 7 152 304 33 66 128 256), losses := [] }

theorem u3774 : Upper (D 7) (R 7) [12,96,3,144,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3775 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,0),(3,0),(4,0),(4,7)], upper := (rows 13 98 7 152 304 33 192 194 322), lower := (rows 13 98 7 152 304 33 192 128 256), losses := [] }

theorem u3775 : Upper (D 7) (R 7) [12,96,3,144,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3776 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 7 152 304 34 65 192 448), lower := (rows 13 98 7 152 304 34 65 128 256), losses := [] }

theorem u3776 : Upper (D 7) (R 7) [12,96,3,144,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3777 : Route 9 := (fun mask => (mask,id))

def c3777 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3777 : Upper (D 7) (R 7) [12,96,3,144,288,2,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,144,288,2,128] 13 (by decide) (choices 1) [1,64] r3777 c3777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u246
  · exact u247

def b3778 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,0),(3,0),(4,0),(4,7)], upper := (rows 13 98 7 152 304 160 65 194 322), lower := (rows 13 98 7 152 304 160 65 128 256), losses := [] }

theorem u3778 : Upper (D 7) (R 7) [12,96,3,144,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3779 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 66, targets := 129 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 7 152 304 160 66 193 321), lower := (rows 13 98 7 152 304 160 66 128 256), losses := [{ target := 7, region := (rows 9 50 12 8 16 32 126 0 269), good := (rows 333 98 327 351 370 98 66 0 256) }] }

theorem u3779 : Upper (D 7) (R 7) [12,96,3,144,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u3779
end Delivery.IrregularNine14.P07
