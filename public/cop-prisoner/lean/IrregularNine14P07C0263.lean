import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0056

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r15780 : Route 9 := (fun mask => (mask,id))

def c15780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15780 : Upper (D 7) (R 7) [12,33,66,130,192,256] 13 := by
  apply FastRouting.sound _ _ [12,33,66,130,192,256] 13 (by decide) (choices 1) [1,16,32] r15780 c15780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3382
  · exact u3383
  · exact u3384

def b15781 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 13 35 70 138 273 48 224 224 480), lower := (rows 13 35 70 138 273 48 64 128 256), losses := [] }

theorem u15781 : Upper (D 7) (R 7) [12,33,66,130,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15781 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15782 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,6),(3,6),(4,1),(4,6)], upper := (rows 13 35 70 138 273 96 240 176 432), lower := (rows 13 35 70 138 273 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 14 22 32 0 130 258), good := (rows 29 443 415 410 273 32 0 128 256) }] }

theorem u15782 : Upper (D 7) (R 7) [12,33,66,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15783 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 138 304 33 208 208 464), lower := (rows 13 35 70 138 304 33 64 128 256), losses := [] }

theorem u15783 : Upper (D 7) (R 7) [12,33,66,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15784 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 13 35 70 138 304 48 193 193 449), lower := (rows 13 35 70 138 304 48 64 128 256), losses := [] }

theorem u15784 : Upper (D 7) (R 7) [12,33,66,130,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15784 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15785 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,6),(3,6),(4,1),(4,6)], upper := (rows 13 35 70 138 304 96 209 145 401), lower := (rows 13 35 70 138 304 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 14 18 32 0 134 262), good := (rows 397 443 415 410 304 32 0 128 256) }] }

theorem u15785 : Upper (D 7) (R 7) [12,33,66,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15786 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 138 336 33 240 176 432), lower := (rows 13 35 70 138 336 33 64 128 256), losses := [] }

theorem u15786 : Upper (D 7) (R 7) [12,33,66,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15787 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 1, region := 136, targets := 64 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 13 35 70 138 336 48 225 161 417), lower := (rows 13 35 70 138 336 48 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 14 16 48 0 130 258), good := (rows 13 427 399 394 304 48 0 128 256) }] }

theorem u15787 : Upper (D 7) (R 7) [12,33,66,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15787 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15788 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 340, targets := 128 },{ cop := 0, region := 496, targets := 2 }], pairs := [(1,6),(2,7),(4,1),(4,7)], upper := (rows 13 35 70 138 336 160 113 177 305), lower := (rows 13 35 70 138 336 160 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 8 16 168 0 128 256), good := (rows 47 35 6 170 272 160 0 160 256) }] }

theorem u15788 : Upper (D 7) (R 7) [12,33,66,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15789 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 472, targets := 2 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,1),(3,6),(4,1)], upper := (rows 13 35 70 152 81 34 480 416 416), lower := (rows 13 35 70 152 81 34 64 128 256), losses := [] }

theorem u15789 : Upper (D 7) (R 7) [12,33,66,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15790 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 340, targets := 128 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,7),(3,6),(4,7)], upper := (rows 13 35 70 152 81 160 354 418 290), lower := (rows 13 35 70 152 81 160 64 128 256), losses := [] }

theorem u15790 : Upper (D 7) (R 7) [12,33,66,144,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15791 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,6),(2,0),(3,6)], upper := (rows 13 35 70 152 81 288 226 162 418), lower := (rows 13 35 70 152 81 288 64 128 256), losses := [] }

theorem u15791 : Upper (D 7) (R 7) [12,33,66,144,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15791 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15792 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 152 112 33 450 386 386), lower := (rows 13 35 70 152 112 33 64 128 256), losses := [] }

theorem u15792 : Upper (D 7) (R 7) [12,33,66,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15793 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 472, targets := 2 },{ cop := 2, region := 48, targets := 129 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 13 35 70 152 112 34 449 385 385), lower := (rows 13 35 70 152 112 34 64 128 256), losses := [] }

theorem u15793 : Upper (D 7) (R 7) [12,33,66,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15794 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 340, targets := 128 },{ cop := 0, region := 418, targets := 64 },{ cop := 1, region := 324, targets := 32 }], pairs := [(1,6),(2,5),(2,7),(4,7)], upper := (rows 13 35 70 152 112 160 323 387 259), lower := (rows 13 35 70 152 112 160 64 128 256), losses := [] }

theorem u15794 : Upper (D 7) (R 7) [12,33,66,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15795 : Route 9 := (fun mask => (mask,id))

def c15795 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15795 : Upper (D 7) (R 7) [12,33,66,144,96,256] 13 := by
  apply FastRouting.sound _ _ [12,33,66,144,96,256] 13 (by decide) (choices 1) [1,2,128] r15795 c15795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3385
  · exact u3386
  · exact u3387

def b15796 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 2 }], pairs := [(1,6),(1,7),(3,1),(4,1)], upper := (rows 13 35 70 152 273 34 224 224 480), lower := (rows 13 35 70 152 273 34 64 128 256), losses := [] }

theorem u15796 : Upper (D 7) (R 7) [12,33,66,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15797 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 1, region := 196, targets := 1 }], pairs := [(0,6),(2,0),(3,6),(4,6)], upper := (rows 13 35 70 152 273 96 226 162 418), lower := (rows 13 35 70 152 273 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 14 22 32 0 130 258), good := (rows 29 443 415 152 273 32 0 128 256) }] }

theorem u15797 : Upper (D 7) (R 7) [12,33,66,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15798 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 340, targets := 128 },{ cop := 1, region := 68, targets := 1 }], pairs := [(1,6),(2,0),(2,7),(4,7)], upper := (rows 13 35 70 152 273 160 98 226 354), lower := (rows 13 35 70 152 273 160 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 8 16 168 0 128 256), good := (rows 47 35 6 184 275 160 0 160 256) }] }

theorem u15798 : Upper (D 7) (R 7) [12,33,66,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15799 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 152 274 33 224 224 480), lower := (rows 13 35 70 152 274 33 64 128 256), losses := [] }

theorem u15799 : Upper (D 7) (R 7) [12,33,66,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15800 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(0,6),(3,1),(3,6),(4,6)], upper := (rows 13 35 70 152 274 96 225 161 417), lower := (rows 13 35 70 152 274 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 119 67 131 259), good := (rows 493 481 484 184 504 96 96 128 256) },{ target := 6, region := (rows 5 2 4 30 22 32 0 130 258), good := (rows 29 443 415 152 410 32 0 128 256) }] }

theorem u15800 : Upper (D 7) (R 7) [12,33,66,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15801 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 340, targets := 128 }], pairs := [(1,6),(2,7),(3,1),(4,7)], upper := (rows 13 35 70 152 274 160 97 225 353), lower := (rows 13 35 70 152 274 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 191 67 131 259), good := (rows 493 481 484 184 504 160 64 160 256) },{ target := 6, region := (rows 1 3 4 8 16 168 0 128 256), good := (rows 47 35 6 184 274 160 0 160 256) }] }

theorem u15801 : Upper (D 7) (R 7) [12,33,66,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15802 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 152 304 33 194 194 450), lower := (rows 13 35 70 152 304 33 64 128 256), losses := [] }

theorem u15802 : Upper (D 7) (R 7) [12,33,66,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15803 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 2 }], pairs := [(1,6),(1,7),(3,1),(4,1)], upper := (rows 13 35 70 152 304 34 193 193 449), lower := (rows 13 35 70 152 304 34 64 128 256), losses := [] }

theorem u15803 : Upper (D 7) (R 7) [12,33,66,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15804 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 1, region := 196, targets := 32 }], pairs := [(0,6),(2,5),(3,6),(4,6)], upper := (rows 13 35 70 152 304 96 195 131 387), lower := (rows 13 35 70 152 304 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 14 18 32 0 134 262), good := (rows 397 443 415 152 304 32 0 128 256) }] }

theorem u15804 : Upper (D 7) (R 7) [12,33,66,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15805 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 340, targets := 128 },{ cop := 1, region := 68, targets := 32 }], pairs := [(1,6),(2,5),(2,7),(4,7)], upper := (rows 13 35 70 152 304 160 67 195 323), lower := (rows 13 35 70 152 304 160 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 8 16 168 0 128 256), good := (rows 47 35 6 184 304 160 0 160 256) }] }

theorem u15805 : Upper (D 7) (R 7) [12,33,66,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15805 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15806 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 152 336 33 226 162 418), lower := (rows 13 35 70 152 336 33 64 128 256), losses := [] }

theorem u15806 : Upper (D 7) (R 7) [12,33,66,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15807 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 472, targets := 2 },{ cop := 0, region := 34, targets := 64 },{ cop := 0, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(3,1),(4,1)], upper := (rows 13 35 70 152 336 34 225 161 417), lower := (rows 13 35 70 152 336 34 64 128 256), losses := [] }

theorem u15807 : Upper (D 7) (R 7) [12,33,66,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15808 : Route 9 := (fun mask => (mask,id))

def c15808 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15808 : Upper (D 7) (R 7) [12,33,66,144,320,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,144,320,128] 13 (by decide) (choices 1) [1,2,32] r15808 c15808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3388
  · exact u3389
  · exact u3390

def b15809 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 168 146 33 336 464 336), lower := (rows 13 35 70 168 146 33 64 128 256), losses := [] }

theorem u15809 : Upper (D 7) (R 7) [12,33,66,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15810 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 35 70 168 146 48 321 449 321), lower := (rows 13 35 70 168 146 48 64 128 256), losses := [] }

theorem u15810 : Upper (D 7) (R 7) [12,33,66,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15810 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15811 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 408, targets := 64 }], pairs := [(2,5),(3,6),(4,5),(4,6)], upper := (rows 13 35 70 168 146 96 337 401 273), lower := (rows 13 35 70 168 146 96 64 128 256), losses := [] }

theorem u15811 : Upper (D 7) (R 7) [12,33,66,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15812 : Route 9 := (fun mask => (mask,id))

def c15812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15812 : Upper (D 7) (R 7) [12,33,66,160,130,256] 13 := by
  apply FastRouting.sound _ _ [12,33,66,160,130,256] 13 (by decide) (choices 1) [1,16] r15812 c15812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3391
  · exact u3392

def b15813 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 168 208 33 338 402 274), lower := (rows 13 35 70 168 208 33 64 128 256), losses := [] }

theorem u15813 : Upper (D 7) (R 7) [12,33,66,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15814 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(4,1),(4,5)], upper := (rows 13 35 70 168 208 34 337 401 273), lower := (rows 13 35 70 168 208 34 64 128 256), losses := [] }

theorem u15814 : Upper (D 7) (R 7) [12,33,66,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15815 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 35 70 168 208 48 323 387 259), lower := (rows 13 35 70 168 208 48 64 128 256), losses := [] }

theorem u15815 : Upper (D 7) (R 7) [12,33,66,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15815 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15816 : Route 9 := (fun mask => (mask,id))

def c15816 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15816 : Upper (D 7) (R 7) [12,33,66,160,192,256] 13 := by
  apply FastRouting.sound _ _ [12,33,66,160,192,256] 13 (by decide) (choices 1) [1,2,16] r15816 c15816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3393
  · exact u3394
  · exact u3395

def b15817 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(4,1),(4,5)], upper := (rows 13 35 70 168 273 34 208 208 464), lower := (rows 13 35 70 168 273 34 64 128 256), losses := [] }

theorem u15817 : Upper (D 7) (R 7) [12,33,66,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15818 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 1, region := 196, targets := 32 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 13 35 70 168 273 48 194 194 450), lower := (rows 13 35 70 168 273 48 64 128 256), losses := [] }

theorem u15818 : Upper (D 7) (R 7) [12,33,66,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15818 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15819 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 408, targets := 64 }], pairs := [(2,5),(3,6),(4,5),(4,6)], upper := (rows 13 35 70 168 273 96 210 146 402), lower := (rows 13 35 70 168 273 96 64 128 256), losses := [] }

theorem u15819 : Upper (D 7) (R 7) [12,33,66,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15820 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 70 168 273 160 82 210 338), lower := (rows 13 35 70 168 273 160 64 128 256), losses := [] }

theorem u15820 : Upper (D 7) (R 7) [12,33,66,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15821 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 168 274 33 208 208 464), lower := (rows 13 35 70 168 274 33 64 128 256), losses := [] }

theorem u15821 : Upper (D 7) (R 7) [12,33,66,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15822 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 200, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 13 35 70 168 274 48 193 193 449), lower := (rows 13 35 70 168 274 48 64 128 256), losses := [] }

theorem u15822 : Upper (D 7) (R 7) [12,33,66,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15822 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15823 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 408, targets := 64 }], pairs := [(2,5),(3,6),(4,5),(4,6)], upper := (rows 13 35 70 168 274 96 209 145 401), lower := (rows 13 35 70 168 274 96 64 128 256), losses := [] }

theorem u15823 : Upper (D 7) (R 7) [12,33,66,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15824 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 70 168 274 160 81 209 337), lower := (rows 13 35 70 168 274 160 64 128 256), losses := [] }

theorem u15824 : Upper (D 7) (R 7) [12,33,66,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15825 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 168 336 33 210 146 402), lower := (rows 13 35 70 168 336 33 64 128 256), losses := [] }

theorem u15825 : Upper (D 7) (R 7) [12,33,66,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15826 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(4,1),(4,5)], upper := (rows 13 35 70 168 336 34 209 145 401), lower := (rows 13 35 70 168 336 34 64 128 256), losses := [] }

theorem u15826 : Upper (D 7) (R 7) [12,33,66,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15827 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 136, targets := 64 }], pairs := [(2,5),(3,6),(4,5)], upper := (rows 13 35 70 168 336 48 195 131 387), lower := (rows 13 35 70 168 336 48 64 128 256), losses := [] }

theorem u15827 : Upper (D 7) (R 7) [12,33,66,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15827 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15828 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 70 168 336 160 83 147 275), lower := (rows 13 35 70 168 336 160 64 128 256), losses := [] }

theorem u15828 : Upper (D 7) (R 7) [12,33,66,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15829 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 168 400 33 82 210 338), lower := (rows 13 35 70 168 400 33 64 128 256), losses := [] }

theorem u15829 : Upper (D 7) (R 7) [12,33,66,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15830 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 0, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(4,1),(4,5)], upper := (rows 13 35 70 168 400 34 81 209 337), lower := (rows 13 35 70 168 400 34 64 128 256), losses := [] }

theorem u15830 : Upper (D 7) (R 7) [12,33,66,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15831 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 35 70 168 400 48 67 195 323), lower := (rows 13 35 70 168 400 48 64 128 256), losses := [] }

theorem u15831 : Upper (D 7) (R 7) [12,33,66,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15831 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15832 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 408, targets := 64 }], pairs := [(2,5),(3,6),(4,5),(4,6)], upper := (rows 13 35 70 168 400 96 83 147 275), lower := (rows 13 35 70 168 400 96 64 128 256), losses := [] }

theorem u15832 : Upper (D 7) (R 7) [12,33,66,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15833 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 200 146 33 368 432 304), lower := (rows 13 35 70 200 146 33 64 128 256), losses := [] }

theorem u15833 : Upper (D 7) (R 7) [12,33,66,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15834 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 456, targets := 2 }], pairs := [(1,6),(3,1),(4,6)], upper := (rows 13 35 70 200 146 48 353 417 289), lower := (rows 13 35 70 200 146 48 64 128 256), losses := [] }

theorem u15834 : Upper (D 7) (R 7) [12,33,66,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15834 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15835 : Route 9 := (fun mask => (mask,id))

def c15835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15835 : Upper (D 7) (R 7) [12,33,66,192,130,256] 13 := by
  apply FastRouting.sound _ _ [12,33,66,192,130,256] 13 (by decide) (choices 1) [1,16,32] r15835 c15835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3396
  · exact u3397
  · exact u3398

def b15836 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 200 176 33 338 402 274), lower := (rows 13 35 70 200 176 33 64 128 256), losses := [] }

theorem u15836 : Upper (D 7) (R 7) [12,33,66,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15837 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(2,7)], upper := (rows 13 35 70 200 176 34 337 401 273), lower := (rows 13 35 70 200 176 34 64 128 256), losses := [] }

theorem u15837 : Upper (D 7) (R 7) [12,33,66,192,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15838 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 70 200 176 48 323 387 259), lower := (rows 13 35 70 200 176 48 64 128 256), losses := [] }

theorem u15838 : Upper (D 7) (R 7) [12,33,66,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15838 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15839 : Route 9 := (fun mask => (mask,id))

def c15839 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15839 : Upper (D 7) (R 7) [12,33,66,192,160,256] 13 := by
  apply FastRouting.sound _ _ [12,33,66,192,160,256] 13 (by decide) (choices 1) [1,2,16] r15839 c15839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3399
  · exact u3400
  · exact u3401

#print axioms u15839
end Delivery.IrregularNine14.P07
