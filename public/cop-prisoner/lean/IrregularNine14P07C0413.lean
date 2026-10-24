import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0139

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24780 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 98 388 26 81 34 201 137 393), lower := (rows 37 98 388 26 81 34 64 128 256), losses := [] }

theorem u24780 : Upper (D 7) (R 7) [36,96,384,18,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24781 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 388 26 81 40 195 131 387), lower := (rows 37 98 388 26 81 40 64 128 256), losses := [] }

theorem u24781 : Upper (D 7) (R 7) [36,96,384,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24781 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24782 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 90, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 388 26 81 160 75 139 267), lower := (rows 37 98 388 26 81 160 64 128 256), losses := [] }

theorem u24782 : Upper (D 7) (R 7) [36,96,384,18,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24783 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 98 388 26 145 33 74 202 330), lower := (rows 37 98 388 26 145 33 64 128 256), losses := [] }

theorem u24783 : Upper (D 7) (R 7) [36,96,384,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24784 : Route 9 := (fun mask => (mask,id))

def c24784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24784 : Upper (D 7) (R 7) [36,96,384,18,129,2] 13 := by
  apply FastRouting.sound _ _ [36,96,384,18,129,2] 13 (by decide) (choices 1) [1,8] r24784 c24784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8372
  · exact u8373

def r24785 : Route 9 := (fun mask => (mask,id))

def c24785 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24785 : Upper (D 7) (R 7) [36,96,384,18,129,8] 13 := by
  apply FastRouting.sound _ _ [36,96,384,18,129,8] 13 (by decide) (choices 1) [1,2] r24785 c24785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8374
  · exact u8375

def b24786 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 388 26 145 96 75 139 267), lower := (rows 37 98 388 26 145 96 64 128 256), losses := [] }

theorem u24786 : Upper (D 7) (R 7) [36,96,384,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24787 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 388 26 152 33 67 195 323), lower := (rows 37 98 388 26 152 33 64 128 256), losses := [] }

theorem u24787 : Upper (D 7) (R 7) [36,96,384,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24788 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(2,1),(2,5)], upper := (rows 37 98 388 26 152 34 65 193 321), lower := (rows 37 98 388 26 152 34 64 128 256), losses := [] }

theorem u24788 : Upper (D 7) (R 7) [36,96,384,18,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24789 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 388 26 152 96 67 131 259), lower := (rows 37 98 388 26 152 96 64 128 256), losses := [] }

theorem u24789 : Upper (D 7) (R 7) [36,96,384,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24790 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 98 388 26 208 33 75 139 267), lower := (rows 37 98 388 26 208 33 64 128 256), losses := [] }

theorem u24790 : Upper (D 7) (R 7) [36,96,384,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24791 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 98 388 26 208 34 73 137 265), lower := (rows 37 98 388 26 208 34 64 128 256), losses := [] }

theorem u24791 : Upper (D 7) (R 7) [36,96,384,18,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24792 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 388 26 208 40 67 131 259), lower := (rows 37 98 388 26 208 40 64 128 256), losses := [] }

theorem u24792 : Upper (D 7) (R 7) [36,96,384,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24792 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24793 : Route 9 := (fun mask => (mask,id))

def c24793 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24793 : Upper (D 7) (R 7) [36,96,384,65,129,2] 13 := by
  apply FastRouting.sound _ _ [36,96,384,65,129,2] 13 (by decide) (choices 1) [2,8,16] r24793 c24793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8376
  · exact u8377
  · exact u8378

def b24794 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 388 73 145 40 82 146 274), lower := (rows 37 98 388 73 145 40 64 128 256), losses := [] }

theorem u24794 : Upper (D 7) (R 7) [36,96,384,65,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24794 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24795 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 388 73 145 48 74 138 266), lower := (rows 37 98 388 73 145 48 64 128 256), losses := [] }

theorem u24795 : Upper (D 7) (R 7) [36,96,384,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24795 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24796 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 34, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 388 73 146 33 90 154 282), lower := (rows 37 98 388 73 146 33 64 128 256), losses := [] }

theorem u24796 : Upper (D 7) (R 7) [36,96,384,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24797 : Route 9 := (fun mask => (mask,id))

def c24797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24797 : Upper (D 7) (R 7) [36,96,384,65,130,2] 13 := by
  apply FastRouting.sound _ _ [36,96,384,65,130,2] 13 (by decide) (choices 1) [1,8,16] r24797 c24797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8379
  · exact u8380
  · exact u8381

def b24798 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 388 73 146 40 83 147 275), lower := (rows 37 98 388 73 146 40 64 128 256), losses := [] }

theorem u24798 : Upper (D 7) (R 7) [36,96,384,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24798 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24799 : Route 9 := (fun mask => (mask,id))

def c24799 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24799 : Upper (D 7) (R 7) [36,96,384,65,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,384,65,130,16] 13 (by decide) (choices 1) [1,2,8] r24799 c24799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8382
  · exact u8383
  · exact u8384

def b24800 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 34, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 388 73 152 33 82 146 274), lower := (rows 37 98 388 73 152 33 64 128 256), losses := [] }

theorem u24800 : Upper (D 7) (R 7) [36,96,384,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24800 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24801 : Route 9 := (fun mask => (mask,id))

def c24801 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24801 : Upper (D 7) (R 7) [36,96,384,65,136,2] 13 := by
  apply FastRouting.sound _ _ [36,96,384,65,136,2] 13 (by decide) (choices 1) [1,2,16] r24801 c24801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8385
  · exact u8386
  · exact u8387

def b24802 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(1,7),(3,7)], upper := (rows 37 98 388 73 152 48 67 131 259), lower := (rows 37 98 388 73 152 48 64 128 256), losses := [] }

theorem u24802 : Upper (D 7) (R 7) [36,96,384,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24802 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24803 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 98 388 88 145 33 74 138 266), lower := (rows 37 98 388 88 145 33 64 128 256), losses := [] }

theorem u24803 : Upper (D 7) (R 7) [36,96,384,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24804 : Route 9 := (fun mask => (mask,id))

def c24804 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24804 : Upper (D 7) (R 7) [36,96,384,80,129,2] 13 := by
  apply FastRouting.sound _ _ [36,96,384,80,129,2] 13 (by decide) (choices 1) [1,2,8] r24804 c24804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8388
  · exact u8389
  · exact u8390

def b24805 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 388 88 145 40 67 131 259), lower := (rows 37 98 388 88 145 40 64 128 256), losses := [] }

theorem u24805 : Upper (D 7) (R 7) [36,96,384,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24805 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24806 : Route 9 := (fun mask => (mask,id))

def c24806 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24806 : Upper (D 7) (R 7) [36,96,384,80,130,1] 13 := by
  apply FastRouting.sound _ _ [36,96,384,80,130,1] 13 (by decide) (choices 1) [1,2,8] r24806 c24806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8391
  · exact u8392
  · exact u8393

def b24807 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 98 388 88 146 34 73 137 265), lower := (rows 37 98 388 88 146 34 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 136 264), good := (rows 37 34 388 445 178 34 0 128 256) }] }

theorem u24807 : Upper (D 7) (R 7) [36,96,384,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24808 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 388 88 146 40 67 131 259), lower := (rows 37 98 388 88 146 40 64 128 256), losses := [] }

theorem u24808 : Upper (D 7) (R 7) [36,96,384,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24808 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24809 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 194 7 25 274 40 224 224 480), lower := (rows 37 194 7 25 274 40 64 128 256), losses := [] }

theorem u24809 : Upper (D 7) (R 7) [36,192,3,17,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24809 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24810 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 194 7 25 274 96 232 168 424), lower := (rows 37 194 7 25 274 96 64 128 256), losses := [] }

theorem u24810 : Upper (D 7) (R 7) [36,192,3,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24811 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 25 280 34 224 224 480), lower := (rows 37 194 7 25 280 34 64 128 256), losses := [] }

theorem u24811 : Upper (D 7) (R 7) [36,192,3,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24812 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 194 7 25 280 96 226 162 418), lower := (rows 37 194 7 25 280 96 64 128 256), losses := [] }

theorem u24812 : Upper (D 7) (R 7) [36,192,3,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24813 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 25 336 34 232 168 424), lower := (rows 37 194 7 25 336 34 64 128 256), losses := [] }

theorem u24813 : Upper (D 7) (R 7) [36,192,3,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24814 : Route 9 := (fun mask => (mask,id))

def c24814 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u24814 : Upper (D 7) (R 7) [36,192,3,17,320,8] 13 := by
  apply FastRouting.sound _ _ [36,192,3,17,320,8] 13 (by decide) (choices 1) [2,32,128] r24814 c24814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8394
  · exact u8395
  · exact u8396

def b24815 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 194 7 25 336 160 106 170 298), lower := (rows 37 194 7 25 336 160 64 128 256), losses := [] }

theorem u24815 : Upper (D 7) (R 7) [36,192,3,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24816 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 7 26 112 33 456 392 392), lower := (rows 37 194 7 26 112 33 64 128 256), losses := [] }

theorem u24816 : Upper (D 7) (R 7) [36,192,3,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24817 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 7 26 112 40 449 385 385), lower := (rows 37 194 7 26 112 40 64 128 256), losses := [] }

theorem u24817 : Upper (D 7) (R 7) [36,192,3,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24817 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24818 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 56, targets := 1 },{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(4,0)], upper := (rows 37 194 7 26 112 160 329 393 265), lower := (rows 37 194 7 26 112 160 64 128 256), losses := [] }

theorem u24818 : Upper (D 7) (R 7) [36,192,3,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24819 : Route 9 := (fun mask => (mask,id))

def c24819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24819 : Upper (D 7) (R 7) [36,192,3,18,96,256] 13 := by
  apply FastRouting.sound _ _ [36,192,3,18,96,256] 13 (by decide) (choices 1) [1,8,128] r24819 c24819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8397
  · exact u8398
  · exact u8399

def b24820 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 194 7 26 273 40 224 224 480), lower := (rows 37 194 7 26 273 40 64 128 256), losses := [] }

theorem u24820 : Upper (D 7) (R 7) [36,192,3,18,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24820 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24821 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 194 7 26 273 96 232 168 424), lower := (rows 37 194 7 26 273 96 64 128 256), losses := [] }

theorem u24821 : Upper (D 7) (R 7) [36,192,3,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24822 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 26 280 33 224 224 480), lower := (rows 37 194 7 26 280 33 64 128 256), losses := [] }

theorem u24822 : Upper (D 7) (R 7) [36,192,3,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24823 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,6)], upper := (rows 37 194 7 26 280 96 225 161 417), lower := (rows 37 194 7 26 280 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 12 21 32 0 129 257), good := (rows 445 130 415 26 280 32 0 128 256) }] }

theorem u24823 : Upper (D 7) (R 7) [36,192,3,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24824 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 26 304 33 200 200 456), lower := (rows 37 194 7 26 304 33 64 128 256), losses := [] }

theorem u24824 : Upper (D 7) (R 7) [36,192,3,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24825 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 194 7 26 304 40 193 193 449), lower := (rows 37 194 7 26 304 40 64 128 256), losses := [] }

theorem u24825 : Upper (D 7) (R 7) [36,192,3,18,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24825 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24826 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(3,6)], upper := (rows 37 194 7 26 304 96 201 137 393), lower := (rows 37 194 7 26 304 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 98 64 128 256), good := (rows 37 224 37 56 304 96 96 128 256) },{ target := 6, region := (rows 1 2 4 12 17 32 0 133 261), good := (rows 445 130 415 26 304 32 0 128 256) }] }

theorem u24826 : Upper (D 7) (R 7) [36,192,3,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24827 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 26 336 33 232 168 424), lower := (rows 37 194 7 26 336 33 64 128 256), losses := [] }

theorem u24827 : Upper (D 7) (R 7) [36,192,3,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24828 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 194 7 26 336 40 225 161 417), lower := (rows 37 194 7 26 336 40 64 128 256), losses := [] }

theorem u24828 : Upper (D 7) (R 7) [36,192,3,18,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24828 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24829 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 37, targets := 64 }], pairs := [(0,1),(0,6),(2,6),(3,7)], upper := (rows 37 194 7 26 336 160 105 169 297), lower := (rows 37 194 7 26 336 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 162 64 128 256), good := (rows 37 224 37 56 336 160 64 160 256) },{ target := 7, region := (rows 1 2 4 12 21 32 65 0 257), good := (rows 381 66 351 26 336 32 64 0 256) }] }

theorem u24829 : Upper (D 7) (R 7) [36,192,3,18,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24830 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 7 56 81 34 456 392 392), lower := (rows 37 194 7 56 81 34 64 128 256), losses := [] }

theorem u24830 : Upper (D 7) (R 7) [36,192,3,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24831 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 7 56 81 40 450 386 386), lower := (rows 37 194 7 56 81 40 64 128 256), losses := [] }

theorem u24831 : Upper (D 7) (R 7) [36,192,3,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24831 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24832 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 194 7 56 81 160 330 394 266), lower := (rows 37 194 7 56 81 160 64 128 256), losses := [] }

theorem u24832 : Upper (D 7) (R 7) [36,192,3,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24833 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 3, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 7 56 81 288 202 138 394), lower := (rows 37 194 7 56 81 288 64 128 256), losses := [] }

theorem u24833 : Upper (D 7) (R 7) [36,192,3,48,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24833 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24834 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 56 273 34 200 200 456), lower := (rows 37 194 7 56 273 34 64 128 256), losses := [] }

theorem u24834 : Upper (D 7) (R 7) [36,192,3,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24835 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 7 56 273 40 194 194 450), lower := (rows 37 194 7 56 273 40 64 128 256), losses := [] }

theorem u24835 : Upper (D 7) (R 7) [36,192,3,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24835 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24836 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 194 7 56 273 96 202 138 394), lower := (rows 37 194 7 56 273 96 64 128 256), losses := [] }

theorem u24836 : Upper (D 7) (R 7) [36,192,3,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24837 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 194 7 56 274 33 200 200 456), lower := (rows 37 194 7 56 274 33 64 128 256), losses := [] }

theorem u24837 : Upper (D 7) (R 7) [36,192,3,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24838 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 194 7 56 274 40 193 193 449), lower := (rows 37 194 7 56 274 40 64 128 256), losses := [] }

theorem u24838 : Upper (D 7) (R 7) [36,192,3,48,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24838 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24839 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 37, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(3,0)], upper := (rows 37 194 7 56 274 96 201 137 393), lower := (rows 37 194 7 56 274 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 98 64 128 256), good := (rows 36 226 38 56 314 96 96 128 256) },{ target := 1, region := (rows 5 0 4 24 16 98 64 128 256), good := (rows 37 224 37 56 312 96 96 128 256) }] }

theorem u24839 : Upper (D 7) (R 7) [36,192,3,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u24839
end Delivery.IrregularNine14.P07
