import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0002

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r660 : Route 9 := (fun mask => (mask,id))

def c660 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u660 : Upper (D 10) (R 10) [6,96,160,192,257,16] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,257,16] 13 (by decide) (choices 1) [8,32,256] r660 c660
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u146
  · exact u147
  · exact u148

def r661 : Route 9 := (fun mask => (mask,id))

def c661 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u661 : Upper (D 10) (R 10) [6,96,160,192,257,256] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,257,256] 13 (by decide) (choices 1) [8,16,32] r661 c661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u149
  · exact u150
  · exact u151

def b662 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 200 280 33 368 432 304), lower := (rows 7 98 164 200 280 33 64 128 256), losses := [] }

theorem u662 : Upper (D 10) (R 10) [6,96,160,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b662 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b663 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 200 280 48 353 417 289), lower := (rows 7 98 164 200 280 48 64 128 256), losses := [] }

theorem u663 : Upper (D 10) (R 10) [6,96,160,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b663 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r664 : Route 9 := (fun mask => (mask,id))

def c664 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u664 : Upper (D 10) (R 10) [6,96,160,192,264,256] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,264,256] 13 (by decide) (choices 1) [1,16,32] r664 c664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u152
  · exact u153
  · exact u154

def b665 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 39, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 200 304 33 344 408 280), lower := (rows 7 98 164 200 304 33 64 128 256), losses := [] }

theorem u665 : Upper (D 10) (R 10) [6,96,160,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b665 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b666 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 200 304 40 337 401 273), lower := (rows 7 98 164 200 304 40 64 128 256), losses := [] }

theorem u666 : Upper (D 10) (R 10) [6,96,160,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b666 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b667 : PairBound 9 := { available := 265, camps := [{ cop := 8, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 98 164 200 304 48 329 393 265), lower := (rows 7 98 164 200 304 48 64 128 256), losses := [] }

theorem u667 : Upper (D 10) (R 10) [6,96,160,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b667 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b668 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 98 164 200 304 288 89 153 281), lower := (rows 7 98 164 200 304 288 64 128 256), losses := [] }

theorem u668 : Upper (D 10) (R 10) [6,96,160,192,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b668 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b669 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 7 98 164 265 304 40 208 208 464), lower := (rows 7 98 164 265 304 40 64 128 256), losses := [] }

theorem u669 : Upper (D 10) (R 10) [6,96,160,257,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b669 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b670 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 98 164 265 304 48 200 200 456), lower := (rows 7 98 164 265 304 48 64 128 256), losses := [] }

theorem u670 : Upper (D 10) (R 10) [6,96,160,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b670 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b671 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 164 265 304 96 216 152 408), lower := (rows 7 98 164 265 304 96 64 128 256), losses := [] }

theorem u671 : Upper (D 10) (R 10) [6,96,160,257,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b671 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r672 : Route 9 := (fun mask => (mask,id))

def c672 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u672 : Upper (D 10) (R 10) [6,96,160,257,320,8] 13 := by
  apply FastRouting.sound _ _ [6,96,160,257,320,8] 13 (by decide) (choices 1) [16,32,128] r672 c672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u155
  · exact u156
  · exact u157

def b673 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 265 336 48 232 168 424), lower := (rows 7 98 164 265 336 48 64 128 256), losses := [] }

theorem u673 : Upper (D 10) (R 10) [6,96,160,257,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b673 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b674 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 98 164 265 336 160 120 184 312), lower := (rows 7 98 164 265 336 160 64 128 256), losses := [] }

theorem u674 : Upper (D 10) (R 10) [6,96,160,257,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b674 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b675 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 164 296 336 33 216 152 408), lower := (rows 7 98 164 296 336 33 64 128 256), losses := [] }

theorem u675 : Upper (D 10) (R 10) [6,96,160,288,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b675 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b676 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 42, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 164 296 336 40 209 145 401), lower := (rows 7 98 164 296 336 40 64 128 256), losses := [] }

theorem u676 : Upper (D 10) (R 10) [6,96,160,288,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b676 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b677 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 296 336 48 201 137 393), lower := (rows 7 98 164 296 336 48 64 128 256), losses := [] }

theorem u677 : Upper (D 10) (R 10) [6,96,160,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b677 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b678 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 98 164 296 336 160 89 153 281), lower := (rows 7 98 164 296 336 160 64 128 256), losses := [] }

theorem u678 : Upper (D 10) (R 10) [6,96,160,288,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b678 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r679 : Route 9 := (fun mask => (mask,id))

def c679 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u679 : Upper (D 10) (R 10) [6,96,160,320,384,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,320,384,1] 13 (by decide) (choices 1) [8,16,32] r679 c679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u158
  · exact u159
  · exact u160

def b680 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 328 400 40 113 177 305), lower := (rows 7 98 164 328 400 40 64 128 256), losses := [] }

theorem u680 : Upper (D 10) (R 10) [6,96,160,320,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b680 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b681 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 388 41 88 48 480 416 416), lower := (rows 7 98 388 41 88 48 64 128 256), losses := [] }

theorem u681 : Upper (D 10) (R 10) [6,96,384,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b681 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b682 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 338, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 98 388 41 88 160 368 432 304), lower := (rows 7 98 388 41 88 160 64 128 256), losses := [] }

theorem u682 : Upper (D 10) (R 10) [6,96,384,33,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b682 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b683 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 388 41 152 48 352 480 352), lower := (rows 7 98 388 41 152 48 64 128 256), losses := [] }

theorem u683 : Upper (D 10) (R 10) [6,96,384,33,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b683 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b684 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 388 41 152 96 368 432 304), lower := (rows 7 98 388 41 152 96 64 128 256), losses := [] }

theorem u684 : Upper (D 10) (R 10) [6,96,384,33,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b684 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b685 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 210, targets := 256 }], pairs := [(1,8),(4,8)], upper := (rows 7 98 388 41 152 288 112 240 368), lower := (rows 7 98 388 41 152 288 64 128 256), losses := [] }

theorem u685 : Upper (D 10) (R 10) [6,96,384,33,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b685 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b686 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 7 98 388 41 176 40 336 464 336), lower := (rows 7 98 388 41 176 40 64 128 256), losses := [] }

theorem u686 : Upper (D 10) (R 10) [6,96,384,33,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b686 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b687 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 98 388 41 176 48 328 456 328), lower := (rows 7 98 388 41 176 48 64 128 256), losses := [] }

theorem u687 : Upper (D 10) (R 10) [6,96,384,33,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b687 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b688 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 388 41 176 96 344 408 280), lower := (rows 7 98 388 41 176 96 64 128 256), losses := [] }

theorem u688 : Upper (D 10) (R 10) [6,96,384,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b688 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b689 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 210, targets := 256 }], pairs := [(1,8),(4,8)], upper := (rows 7 98 388 41 176 288 88 216 344), lower := (rows 7 98 388 41 176 288 64 128 256), losses := [] }

theorem u689 : Upper (D 10) (R 10) [6,96,384,33,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b689 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b690 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 7 98 388 41 208 40 368 432 304), lower := (rows 7 98 388 41 208 40 64 128 256), losses := [] }

theorem u690 : Upper (D 10) (R 10) [6,96,384,33,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b690 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b691 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 388 41 208 48 360 424 296), lower := (rows 7 98 388 41 208 48 64 128 256), losses := [] }

theorem u691 : Upper (D 10) (R 10) [6,96,384,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b691 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b692 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 210, targets := 256 }], pairs := [(1,8),(4,8)], upper := (rows 7 98 388 41 208 288 120 184 312), lower := (rows 7 98 388 41 208 288 64 128 256), losses := [] }

theorem u692 : Upper (D 10) (R 10) [6,96,384,33,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b692 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b693 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 7 98 388 56 208 33 360 424 296), lower := (rows 7 98 388 56 208 33 64 128 256), losses := [] }

theorem u693 : Upper (D 10) (R 10) [6,96,384,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b693 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b694 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 42, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 388 56 208 40 353 417 289), lower := (rows 7 98 388 56 208 40 64 128 256), losses := [] }

theorem u694 : Upper (D 10) (R 10) [6,96,384,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b694 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r695 : Route 9 := (fun mask => (mask,id))

def c695 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u695 : Upper (D 10) (R 10) [6,96,384,48,192,256] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,192,256] 13 (by decide) (choices 1) [1,8,32] r695 c695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u161
  · exact u162
  · exact u163

def b696 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 388 88 176 33 360 424 296), lower := (rows 7 98 388 88 176 33 64 128 256), losses := [] }

theorem u696 : Upper (D 10) (R 10) [6,96,384,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b696 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b697 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 388 88 176 40 353 417 289), lower := (rows 7 98 388 88 176 40 64 128 256), losses := [] }

theorem u697 : Upper (D 10) (R 10) [6,96,384,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b697 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r698 : Route 9 := (fun mask => (mask,id))

def c698 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u698 : Upper (D 10) (R 10) [6,96,384,80,160,256] 13 := by
  apply FastRouting.sound _ _ [6,96,384,80,160,256] 13 (by decide) (choices 1) [1,8,32] r698 c698
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u164
  · exact u165
  · exact u166

def b699 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 202, targets := 256 }], pairs := [(1,8)], upper := (rows 7 98 388 152 304 33 104 232 360), lower := (rows 7 98 388 152 304 33 64 128 256), losses := [] }

theorem u699 : Upper (D 10) (R 10) [6,96,384,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b699 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b700 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 7 98 388 152 304 40 97 225 353), lower := (rows 7 98 388 152 304 40 64 128 256), losses := [] }

theorem u700 : Upper (D 10) (R 10) [6,96,384,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b700 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b701 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 388 152 304 96 105 169 297), lower := (rows 7 98 388 152 304 96 64 128 256), losses := [] }

theorem u701 : Upper (D 10) (R 10) [6,96,384,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b701 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r702 : Route 9 := (fun mask => (mask,id))

def c702 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u702 : Upper (D 10) (R 10) [6,96,384,144,320,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,144,320,1] 13 (by decide) (choices 1) [8,32] r702 c702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u167
  · exact u168

def b703 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 388 152 336 40 97 161 289), lower := (rows 7 98 388 152 336 40 64 128 256), losses := [] }

theorem u703 : Upper (D 10) (R 10) [6,96,384,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b703 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b704 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 338, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 388 168 304 33 88 216 344), lower := (rows 7 98 388 168 304 33 64 128 256), losses := [] }

theorem u704 : Upper (D 10) (R 10) [6,96,384,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b704 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b705 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 7 98 388 168 304 40 81 209 337), lower := (rows 7 98 388 168 304 40 64 128 256), losses := [] }

theorem u705 : Upper (D 10) (R 10) [6,96,384,160,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b705 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b706 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 388 168 304 96 89 153 281), lower := (rows 7 98 388 168 304 96 64 128 256), losses := [] }

theorem u706 : Upper (D 10) (R 10) [6,96,384,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b706 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b707 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 338, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 388 168 336 33 120 184 312), lower := (rows 7 98 388 168 336 33 64 128 256), losses := [] }

theorem u707 : Upper (D 10) (R 10) [6,96,384,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b707 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b708 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 7 98 388 168 336 40 113 177 305), lower := (rows 7 98 388 168 336 40 64 128 256), losses := [] }

theorem u708 : Upper (D 10) (R 10) [6,96,384,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b708 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b709 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 388 168 336 48 105 169 297), lower := (rows 7 98 388 168 336 48 64 128 256), losses := [] }

theorem u709 : Upper (D 10) (R 10) [6,96,384,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b709 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b710 : PairBound 9 := { available := 448, camps := [{ cop := 8, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 44 140 304 48 448 448 448), lower := (rows 35 67 44 140 304 48 64 128 256), losses := [] }

theorem u710 : Upper (D 10) (R 10) [34,65,40,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b710 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b711 : PairBound 9 := { available := 400, camps := [{ cop := 5, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 44 140 304 96 464 400 400), lower := (rows 35 67 44 140 304 96 64 128 256), losses := [] }

theorem u711 : Upper (D 10) (R 10) [34,65,40,132,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b711 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b712 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 195, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 67 44 140 304 288 208 208 464), lower := (rows 35 67 44 140 304 288 64 128 256), losses := [] }

theorem u712 : Upper (D 10) (R 10) [34,65,40,132,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b712 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b713 : PairBound 9 := { available := 416, camps := [{ cop := 5, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 44 152 276 96 480 416 416), lower := (rows 35 67 44 152 276 96 64 128 256), losses := [] }

theorem u713 : Upper (D 10) (R 10) [34,65,40,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b713 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b714 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 44 152 276 160 352 480 352), lower := (rows 35 67 44 152 276 160 64 128 256), losses := [] }

theorem u714 : Upper (D 10) (R 10) [34,65,40,144,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b714 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b715 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 195, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 67 44 152 276 288 224 224 480), lower := (rows 35 67 44 152 276 288 64 128 256), losses := [] }

theorem u715 : Upper (D 10) (R 10) [34,65,40,144,260,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b715 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b716 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 152 304 36 448 448 448), lower := (rows 35 67 44 152 304 36 64 128 256), losses := [] }

theorem u716 : Upper (D 10) (R 10) [34,65,40,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b716 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b717 : PairBound 9 := { available := 388, camps := [{ cop := 5, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 67 44 152 304 96 452 388 388), lower := (rows 35 67 44 152 304 96 64 128 256), losses := [] }

theorem u717 : Upper (D 10) (R 10) [34,65,40,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b717 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b718 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 44 152 304 160 324 452 324), lower := (rows 35 67 44 152 304 160 64 128 256), losses := [] }

theorem u718 : Upper (D 10) (R 10) [34,65,40,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b718 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b719 : PairBound 9 := { available := 196, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 67 44 152 304 288 196 196 452), lower := (rows 35 67 44 152 304 288 64 128 256), losses := [] }

theorem u719 : Upper (D 10) (R 10) [34,65,40,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b719 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u719
end Delivery.IrregularNine14.P10
