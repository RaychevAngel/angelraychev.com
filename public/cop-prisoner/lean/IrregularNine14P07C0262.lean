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

def b15720 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 408, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 69 266 146 96 240 176 432), lower := (rows 13 35 69 266 146 96 64 128 256), losses := [] }

theorem u15720 : Upper (D 7) (R 7) [12,33,65,258,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15721 : Route 9 := (fun mask => (mask,id))

def c15721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15721 : Upper (D 7) (R 7) [12,33,65,258,130,128] 13 := by
  apply FastRouting.sound _ _ [12,33,65,258,130,128] 13 (by decide) (choices 1) [16,32] r15721 c15721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3362
  · exact u3363

def b15722 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 266 176 34 208 208 464), lower := (rows 13 35 69 266 176 34 64 128 256), losses := [] }

theorem u15722 : Upper (D 7) (R 7) [12,33,65,258,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15723 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 69 266 176 48 194 194 450), lower := (rows 13 35 69 266 176 48 64 128 256), losses := [] }

theorem u15723 : Upper (D 7) (R 7) [12,33,65,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15723 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15724 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 408, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 69 266 176 96 210 146 402), lower := (rows 13 35 69 266 176 96 64 128 256), losses := [] }

theorem u15724 : Upper (D 7) (R 7) [12,33,65,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15725 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 69 266 176 160 82 210 338), lower := (rows 13 35 69 266 176 160 64 128 256), losses := [] }

theorem u15725 : Upper (D 7) (R 7) [12,33,65,258,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15726 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 266 208 34 240 176 432), lower := (rows 13 35 69 266 208 34 64 128 256), losses := [] }

theorem u15726 : Upper (D 7) (R 7) [12,33,65,258,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15727 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 392, targets := 64 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 13 35 69 266 208 48 226 162 418), lower := (rows 13 35 69 266 208 48 64 128 256), losses := [] }

theorem u15727 : Upper (D 7) (R 7) [12,33,65,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15727 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15728 : Route 9 := (fun mask => (mask,id))

def c15728 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15728 : Upper (D 7) (R 7) [12,33,65,258,192,128] 13 := by
  apply FastRouting.sound _ _ [12,33,65,258,192,128] 13 (by decide) (choices 1) [2,16,32] r15728 c15728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3364
  · exact u3365
  · exact u3366

def b15729 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 280 146 34 224 224 480), lower := (rows 13 35 69 280 146 34 64 128 256), losses := [] }

theorem u15729 : Upper (D 7) (R 7) [12,33,65,272,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15730 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 408, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 69 280 146 96 226 162 418), lower := (rows 13 35 69 280 146 96 64 128 256), losses := [] }

theorem u15730 : Upper (D 7) (R 7) [12,33,65,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15731 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 68, targets := 128 }], pairs := [(0,7),(2,7),(3,0),(4,0)], upper := (rows 13 35 69 280 146 160 98 226 354), lower := (rows 13 35 69 280 146 160 64 128 256), losses := [{ target := 7, region := (rows 25 2 22 24 16 32 66 0 258), good := (rows 13 359 69 285 351 32 64 0 256) }] }

theorem u15731 : Upper (D 7) (R 7) [12,33,65,272,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15732 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 280 176 34 194 194 450), lower := (rows 13 35 69 280 176 34 64 128 256), losses := [] }

theorem u15732 : Upper (D 7) (R 7) [12,33,65,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15733 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 408, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 69 280 176 96 194 130 386), lower := (rows 13 35 69 280 176 96 64 128 256), losses := [] }

theorem u15733 : Upper (D 7) (R 7) [12,33,65,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15734 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 69 280 176 160 66 194 322), lower := (rows 13 35 69 280 176 160 64 128 256), losses := [] }

theorem u15734 : Upper (D 7) (R 7) [12,33,65,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15735 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 34, targets := 64 },{ cop := 0, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 280 208 34 226 162 418), lower := (rows 13 35 69 280 208 34 64 128 256), losses := [] }

theorem u15735 : Upper (D 7) (R 7) [12,33,65,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15736 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 162, targets := 64 },{ cop := 1, region := 68, targets := 128 }], pairs := [(1,6),(2,7),(3,0),(4,0)], upper := (rows 13 35 69 280 208 160 98 162 290), lower := (rows 13 35 69 280 208 160 64 128 256), losses := [] }

theorem u15736 : Upper (D 7) (R 7) [12,33,65,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15737 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 392 82 34 240 176 432), lower := (rows 13 35 69 392 82 34 64 128 256), losses := [] }

theorem u15737 : Upper (D 7) (R 7) [12,33,65,384,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15738 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 2, region := 50, targets := 128 }], pairs := [(1,7),(3,0),(4,0)], upper := (rows 13 35 69 392 82 48 226 162 418), lower := (rows 13 35 69 392 82 48 64 128 256), losses := [] }

theorem u15738 : Upper (D 7) (R 7) [12,33,65,384,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15738 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15739 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 84, targets := 128 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 69 392 82 160 114 178 306), lower := (rows 13 35 69 392 82 160 64 128 256), losses := [] }

theorem u15739 : Upper (D 7) (R 7) [12,33,65,384,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15740 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 392 112 34 210 146 402), lower := (rows 13 35 69 392 112 34 64 128 256), losses := [] }

theorem u15740 : Upper (D 7) (R 7) [12,33,65,384,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15741 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 69 392 112 48 194 130 386), lower := (rows 13 35 69 392 112 48 64 128 256), losses := [] }

theorem u15741 : Upper (D 7) (R 7) [12,33,65,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15741 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15742 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 84, targets := 128 }], pairs := [(2,7),(3,0),(4,0),(4,7)], upper := (rows 13 35 69 392 112 160 82 146 274), lower := (rows 13 35 69 392 112 160 64 128 256), losses := [] }

theorem u15742 : Upper (D 7) (R 7) [12,33,65,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15743 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 392 146 34 112 240 368), lower := (rows 13 35 69 392 146 34 64 128 256), losses := [] }

theorem u15743 : Upper (D 7) (R 7) [12,33,65,384,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15744 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 68, targets := 128 }], pairs := [(2,7),(3,0),(4,0)], upper := (rows 13 35 69 392 146 48 98 226 354), lower := (rows 13 35 69 392 146 48 64 128 256), losses := [] }

theorem u15744 : Upper (D 7) (R 7) [12,33,65,384,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15744 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15745 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 408, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 69 392 146 96 114 178 306), lower := (rows 13 35 69 392 146 96 64 128 256), losses := [] }

theorem u15745 : Upper (D 7) (R 7) [12,33,65,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15746 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 392 176 34 82 210 338), lower := (rows 13 35 69 392 176 34 64 128 256), losses := [] }

theorem u15746 : Upper (D 7) (R 7) [12,33,65,384,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15747 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 69 392 176 48 66 194 322), lower := (rows 13 35 69 392 176 48 64 128 256), losses := [] }

theorem u15747 : Upper (D 7) (R 7) [12,33,65,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15747 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15748 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 408, targets := 1 },{ cop := 1, region := 408, targets := 64 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 13 35 69 392 176 96 82 146 274), lower := (rows 13 35 69 392 176 96 64 128 256), losses := [] }

theorem u15748 : Upper (D 7) (R 7) [12,33,65,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15749 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 34, targets := 192 },{ cop := 1, region := 472, targets := 1 }], pairs := [(1,6),(1,7),(3,0),(4,0)], upper := (rows 13 35 69 392 208 34 114 178 306), lower := (rows 13 35 69 392 208 34 64 128 256), losses := [] }

theorem u15749 : Upper (D 7) (R 7) [12,33,65,384,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15750 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 1, region := 392, targets := 64 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 13 35 69 392 208 48 98 162 290), lower := (rows 13 35 69 392 208 48 64 128 256), losses := [] }

theorem u15750 : Upper (D 7) (R 7) [12,33,65,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15750 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15751 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(2,7)], upper := (rows 13 35 70 88 145 34 480 416 416), lower := (rows 13 35 70 88 145 34 64 128 256), losses := [] }

theorem u15751 : Upper (D 7) (R 7) [12,33,66,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15752 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 324, targets := 1 },{ cop := 1, region := 324, targets := 128 }], pairs := [(1,6),(2,0),(2,7),(4,6)], upper := (rows 13 35 70 88 145 160 354 418 290), lower := (rows 13 35 70 88 145 160 64 128 256), losses := [] }

theorem u15752 : Upper (D 7) (R 7) [12,33,66,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15753 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,6),(2,0),(4,6)], upper := (rows 13 35 70 88 145 288 226 162 418), lower := (rows 13 35 70 88 145 288 64 128 256), losses := [] }

theorem u15753 : Upper (D 7) (R 7) [12,33,66,80,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15753 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15754 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 88 146 33 480 416 416), lower := (rows 13 35 70 88 146 33 64 128 256), losses := [] }

theorem u15754 : Upper (D 7) (R 7) [12,33,66,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15755 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 324, targets := 128 }], pairs := [(1,6),(2,7),(3,1),(4,6)], upper := (rows 13 35 70 88 146 160 353 417 289), lower := (rows 13 35 70 88 146 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 183 67 131 259), good := (rows 493 481 484 120 504 160 64 160 256) }] }

theorem u15755 : Upper (D 7) (R 7) [12,33,66,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15756 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6),(3,1),(4,6)], upper := (rows 13 35 70 88 146 288 225 161 417), lower := (rows 13 35 70 88 146 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 311 67 131 259), good := (rows 493 481 484 120 504 288 64 128 288) }] }

theorem u15756 : Upper (D 7) (R 7) [12,33,66,80,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15756 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15757 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 88 176 33 450 386 386), lower := (rows 13 35 70 88 176 33 64 128 256), losses := [] }

theorem u15757 : Upper (D 7) (R 7) [12,33,66,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15758 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(2,7)], upper := (rows 13 35 70 88 176 34 449 385 385), lower := (rows 13 35 70 88 176 34 64 128 256), losses := [] }

theorem u15758 : Upper (D 7) (R 7) [12,33,66,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15759 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 70 88 176 160 323 387 259), lower := (rows 13 35 70 88 176 160 64 128 256), losses := [] }

theorem u15759 : Upper (D 7) (R 7) [12,33,66,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15760 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 1, region := 196, targets := 32 }], pairs := [(1,6),(2,5),(4,6)], upper := (rows 13 35 70 88 176 288 195 131 387), lower := (rows 13 35 70 88 176 288 64 128 256), losses := [] }

theorem u15760 : Upper (D 7) (R 7) [12,33,66,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15760 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15761 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(2,7)], upper := (rows 13 35 70 88 273 34 224 160 416), lower := (rows 13 35 70 88 273 34 64 128 256), losses := [] }

theorem u15761 : Upper (D 7) (R 7) [12,33,66,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15762 : Route 9 := (fun mask => (mask,id))

def c15762 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15762 : Upper (D 7) (R 7) [12,33,66,80,257,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,80,257,128] 13 (by decide) (choices 1) [2,32,128] r15762 c15762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3367
  · exact u3368
  · exact u3369

def b15763 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 88 274 33 224 160 416), lower := (rows 13 35 70 88 274 33 64 128 256), losses := [] }

theorem u15763 : Upper (D 7) (R 7) [12,33,66,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15764 : Route 9 := (fun mask => (mask,id))

def c15764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15764 : Upper (D 7) (R 7) [12,33,66,80,258,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,80,258,128] 13 (by decide) (choices 1) [1,32,128] r15764 c15764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3370
  · exact u3371
  · exact u3372

def b15765 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 88 304 33 194 130 386), lower := (rows 13 35 70 88 304 33 64 128 256), losses := [] }

theorem u15765 : Upper (D 7) (R 7) [12,33,66,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15766 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(2,7)], upper := (rows 13 35 70 88 304 34 193 129 385), lower := (rows 13 35 70 88 304 34 64 128 256), losses := [] }

theorem u15766 : Upper (D 7) (R 7) [12,33,66,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15767 : Route 9 := (fun mask => (mask,id))

def c15767 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15767 : Upper (D 7) (R 7) [12,33,66,80,288,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,80,288,128] 13 (by decide) (choices 1) [1,2,128] r15767 c15767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3373
  · exact u3374
  · exact u3375

def b15768 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 88 400 33 226 162 418), lower := (rows 13 35 70 88 400 33 64 128 256), losses := [] }

theorem u15768 : Upper (D 7) (R 7) [12,33,66,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15769 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(2,7)], upper := (rows 13 35 70 88 400 34 225 161 417), lower := (rows 13 35 70 88 400 34 64 128 256), losses := [] }

theorem u15769 : Upper (D 7) (R 7) [12,33,66,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15770 : Route 9 := (fun mask => (mask,id))

def c15770 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15770 : Upper (D 7) (R 7) [12,33,66,80,384,128] 13 := by
  apply FastRouting.sound _ _ [12,33,66,80,384,128] 13 (by decide) (choices 1) [1,2,32] r15770 c15770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3376
  · exact u3377
  · exact u3378

def b15771 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 13 35 70 138 81 48 480 416 416), lower := (rows 13 35 70 138 81 48 64 128 256), losses := [] }

theorem u15771 : Upper (D 7) (R 7) [12,33,66,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15771 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15772 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 340, targets := 128 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,7),(3,6),(4,7)], upper := (rows 13 35 70 138 81 160 368 432 304), lower := (rows 13 35 70 138 81 160 64 128 256), losses := [] }

theorem u15772 : Upper (D 7) (R 7) [12,33,66,130,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15773 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 496, targets := 2 }], pairs := [(1,6),(3,6),(4,1)], upper := (rows 13 35 70 138 81 288 240 176 432), lower := (rows 13 35 70 138 81 288 64 128 256), losses := [] }

theorem u15773 : Upper (D 7) (R 7) [12,33,66,130,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15773 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15774 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 138 112 33 464 400 400), lower := (rows 13 35 70 138 112 33 64 128 256), losses := [] }

theorem u15774 : Upper (D 7) (R 7) [12,33,66,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15775 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 35 70 138 112 48 449 385 385), lower := (rows 13 35 70 138 112 48 64 128 256), losses := [] }

theorem u15775 : Upper (D 7) (R 7) [12,33,66,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15775 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15776 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 340, targets := 128 },{ cop := 0, region := 496, targets := 2 }], pairs := [(1,6),(2,7),(4,1),(4,7)], upper := (rows 13 35 70 138 112 160 337 401 273), lower := (rows 13 35 70 138 112 160 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 8 16 168 0 128 256), good := (rows 47 35 6 170 48 160 0 160 256) }] }

theorem u15776 : Upper (D 7) (R 7) [12,33,66,130,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r15777 : Route 9 := (fun mask => (mask,id))

def c15777 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u15777 : Upper (D 7) (R 7) [12,33,66,130,96,256] 13 := by
  apply FastRouting.sound _ _ [12,33,66,130,96,256] 13 (by decide) (choices 1) [1,16,128] r15777 c15777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3379
  · exact u3380
  · exact u3381

def b15778 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(4,0)], upper := (rows 13 35 70 138 208 33 368 432 304), lower := (rows 13 35 70 138 208 33 64 128 256), losses := [] }

theorem u15778 : Upper (D 7) (R 7) [12,33,66,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15779 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 1, region := 392, targets := 64 },{ cop := 1, region := 324, targets := 128 }], pairs := [(2,7),(3,6),(4,1)], upper := (rows 13 35 70 138 208 48 353 417 289), lower := (rows 13 35 70 138 208 48 64 128 256), losses := [] }

theorem u15779 : Upper (D 7) (R 7) [12,33,66,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15779 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u15779
end Delivery.IrregularNine14.P07
