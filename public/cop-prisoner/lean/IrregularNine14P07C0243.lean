import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0042

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14580 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 389, targets := 32 },{ cop := 3, region := 66, targets := 128 }], pairs := [(0,5),(1,7),(2,5)], upper := (rows 7 98 388 41 152 48 67 195 323), lower := (rows 7 98 388 41 152 48 64 128 256), losses := [] }

theorem u14580 : Upper (D 7) (R 7) [6,96,384,33,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14580 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14581 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 41 152 96 83 147 275), lower := (rows 7 98 388 41 152 96 64 128 256), losses := [] }

theorem u14581 : Upper (D 7) (R 7) [6,96,384,33,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14582 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 98 388 41 208 33 90 154 282), lower := (rows 7 98 388 41 208 33 64 128 256), losses := [] }

theorem u14582 : Upper (D 7) (R 7) [6,96,384,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14583 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 388 41 208 34 89 153 281), lower := (rows 7 98 388 41 208 34 64 128 256), losses := [] }

theorem u14583 : Upper (D 7) (R 7) [6,96,384,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14584 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 98 388 41 208 40 83 147 275), lower := (rows 7 98 388 41 208 40 64 128 256), losses := [] }

theorem u14584 : Upper (D 7) (R 7) [6,96,384,33,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14584 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14585 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 388 41 208 48 75 139 267), lower := (rows 7 98 388 41 208 48 64 128 256), losses := [] }

theorem u14585 : Upper (D 7) (R 7) [6,96,384,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14585 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14586 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 454, targets := 1 },{ cop := 4, region := 40, targets := 66 }], pairs := [(1,0),(2,0),(3,1),(3,6)], upper := (rows 7 98 388 56 145 33 74 202 330), lower := (rows 7 98 388 56 145 33 64 128 256), losses := [] }

theorem u14586 : Upper (D 7) (R 7) [6,96,384,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14587 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 106, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 388 56 145 34 73 201 329), lower := (rows 7 98 388 56 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 66 4 24 16 99 64 128 256), good := (rows 38 98 388 56 184 34 98 128 256) }] }

theorem u14587 : Upper (D 7) (R 7) [6,96,384,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14588 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 388 56 145 40 67 195 323), lower := (rows 7 98 388 56 145 40 64 128 256), losses := [] }

theorem u14588 : Upper (D 7) (R 7) [6,96,384,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14588 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14589 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 56 145 96 75 139 267), lower := (rows 7 98 388 56 145 96 64 128 256), losses := [] }

theorem u14589 : Upper (D 7) (R 7) [6,96,384,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14590 : Route 9 := (fun mask => (mask,id))

def c14590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14590 : Upper (D 7) (R 7) [6,96,384,48,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,130,1] 13 (by decide) (choices 1) [1,8] r14590 c14590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2539
  · exact u2540

def b14591 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 98 388 56 146 40 65 193 321), lower := (rows 7 98 388 56 146 40 64 128 256), losses := [] }

theorem u14591 : Upper (D 7) (R 7) [6,96,384,48,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14591 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14592 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 388 56 146 96 73 137 265), lower := (rows 7 98 388 56 146 96 64 128 256), losses := [] }

theorem u14592 : Upper (D 7) (R 7) [6,96,384,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14593 : Route 9 := (fun mask => (mask,id))

def c14593 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14593 : Upper (D 7) (R 7) [6,96,384,48,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,192,1] 13 (by decide) (choices 1) [1,2,8] r14593 c14593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2541
  · exact u2542
  · exact u2543

def b14594 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 388 56 208 34 73 137 265), lower := (rows 7 98 388 56 208 34 64 128 256), losses := [] }

theorem u14594 : Upper (D 7) (R 7) [6,96,384,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14595 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 7 98 388 56 208 40 67 131 259), lower := (rows 7 98 388 56 208 40 64 128 256), losses := [] }

theorem u14595 : Upper (D 7) (R 7) [6,96,384,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14595 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14596 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 45, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(2,6)], upper := (rows 7 259 13 56 82 96 224 160 416), lower := (rows 7 259 13 56 82 96 64 128 256), losses := [] }

theorem u14596 : Upper (D 7) (R 7) [6,257,9,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14597 : Route 9 := (fun mask => (mask,id))

def c14597 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14597 : Upper (D 7) (R 7) [6,257,9,48,66,128] 13 := by
  apply FastRouting.sound _ _ [6,257,9,48,66,128] 13 (by decide) (choices 1) [32,128] r14597 c14597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2544
  · exact u2545

def b14598 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 216, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 259 13 56 208 34 224 224 480), lower := (rows 7 259 13 56 208 34 64 128 256), losses := [] }

theorem u14598 : Upper (D 7) (R 7) [6,257,9,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14599 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 259 13 56 208 96 226 162 418), lower := (rows 7 259 13 56 208 96 64 128 256), losses := [] }

theorem u14599 : Upper (D 7) (R 7) [6,257,9,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14600 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 391, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 259 13 104 50 48 192 192 448), lower := (rows 7 259 13 104 50 48 64 128 256), losses := [] }

theorem u14600 : Upper (D 7) (R 7) [6,257,9,96,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14600 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14601 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 259 13 104 50 96 208 144 400), lower := (rows 7 259 13 104 50 96 64 128 256), losses := [] }

theorem u14601 : Upper (D 7) (R 7) [6,257,9,96,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14602 : Route 9 := (fun mask => (mask,id))

def c14602 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14602 : Upper (D 7) (R 7) [6,257,9,96,34,128] 13 := by
  apply FastRouting.sound _ _ [6,257,9,96,34,128] 13 (by decide) (choices 1) [16,128] r14602 c14602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2546
  · exact u2547

def b14603 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 4, region := 104, targets := 2 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 259 13 104 146 48 224 224 480), lower := (rows 7 259 13 104 146 48 64 128 256), losses := [] }

theorem u14603 : Upper (D 7) (R 7) [6,257,9,96,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14603 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14604 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 259 13 104 146 96 240 176 432), lower := (rows 7 259 13 104 146 96 64 128 256), losses := [] }

theorem u14604 : Upper (D 7) (R 7) [6,257,9,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14605_16 : Upper (D 7) (R 7) [6,257,9,96,130,128,16] 13 :=
  permutation_upper _ _ _ [6,257,9,96,130,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2548

theorem m14605_32 : Upper (D 7) (R 7) [6,257,9,96,130,128,32] 13 :=
  permutation_upper _ _ _ [6,257,9,96,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2549

def r14605 : Route 9 := (fun mask => (mask,id))

def c14605 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14605 : Upper (D 7) (R 7) [6,257,9,96,130,128] 13 := by
  apply FastRouting.sound _ _ [6,257,9,96,130,128] 13 (by decide) (choices 1) [16,32] r14605 c14605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14605_16
  · exact m14605_32

def b14606 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 216, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 259 13 104 176 34 208 208 464), lower := (rows 7 259 13 104 176 34 64 128 256), losses := [] }

theorem u14606 : Upper (D 7) (R 7) [6,257,9,96,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14607 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 391, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 259 13 104 176 48 194 194 450), lower := (rows 7 259 13 104 176 48 64 128 256), losses := [] }

theorem u14607 : Upper (D 7) (R 7) [6,257,9,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14607 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14608 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 259 13 104 176 96 210 146 402), lower := (rows 7 259 13 104 176 96 64 128 256), losses := [] }

theorem u14608 : Upper (D 7) (R 7) [6,257,9,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14609 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 259 13 104 176 160 82 210 338), lower := (rows 7 259 13 104 176 160 64 128 256), losses := [] }

theorem u14609 : Upper (D 7) (R 7) [6,257,9,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14610 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 212, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 28 41 208 34 224 224 480), lower := (rows 7 259 28 41 208 34 64 128 256), losses := [] }

theorem u14610 : Upper (D 7) (R 7) [6,257,24,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14611 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 240, targets := 1 },{ cop := 3, region := 386, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 7 259 28 41 208 96 226 162 418), lower := (rows 7 259 28 41 208 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 123 67 131 259), good := (rows 502 498 60 508 240 96 96 128 256) },{ target := 6, region := (rows 5 14 4 8 16 32 0 136 264), good := (rows 7 259 415 427 144 32 0 128 256) }] }

theorem u14611 : Upper (D 7) (R 7) [6,257,24,33,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14612 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 212, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 259 28 42 208 33 224 224 480), lower := (rows 7 259 28 42 208 33 64 128 256), losses := [] }

theorem u14612 : Upper (D 7) (R 7) [6,257,24,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14613 : Route 9 := (fun mask => (mask,id))

def c14613 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14613 : Upper (D 7) (R 7) [6,257,24,34,192,64] 13 := by
  apply FastRouting.sound _ _ [6,257,24,34,192,64] 13 (by decide) (choices 1) [1,32,128] r14613 c14613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2550
  · exact u2551
  · exact u2552

def b14614 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 451, targets := 32 }], pairs := [(0,5),(1,5),(2,0),(3,0)], upper := (rows 7 259 28 104 176 33 194 194 450), lower := (rows 7 259 28 104 176 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 60 40 48 32 67 131 259), good := (rows 454 450 28 124 188 508 64 128 256) }] }

theorem u14614 : Upper (D 7) (R 7) [6,257,24,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14615 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 451, targets := 32 }], pairs := [(0,5),(1,5),(2,1),(3,1)], upper := (rows 7 259 28 104 176 34 193 193 449), lower := (rows 7 259 28 104 176 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 60 40 48 32 67 131 259), good := (rows 453 449 28 124 188 508 64 128 256) }] }

theorem u14615 : Upper (D 7) (R 7) [6,257,24,96,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14616 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 259 28 104 176 96 195 131 387), lower := (rows 7 259 28 104 176 96 64 128 256), losses := [] }

theorem u14616 : Upper (D 7) (R 7) [6,257,24,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14617 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 7 259 37 26 112 40 192 192 448), lower := (rows 7 259 37 26 112 40 64 128 256), losses := [] }

theorem u14617 : Upper (D 7) (R 7) [6,257,33,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14617 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14618 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 7 259 37 26 112 96 200 136 392), lower := (rows 7 259 37 26 112 96 64 128 256), losses := [] }

theorem u14618 : Upper (D 7) (R 7) [6,257,33,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14619 : Route 9 := (fun mask => (mask,id))

def c14619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14619 : Upper (D 7) (R 7) [6,257,33,18,96,128] 13 := by
  apply FastRouting.sound _ _ [6,257,33,18,96,128] 13 (by decide) (choices 1) [8,128] r14619 c14619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2553
  · exact u2554

def b14620 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 7 259 37 26 208 40 224 224 480), lower := (rows 7 259 37 26 208 40 64 128 256), losses := [] }

theorem u14620 : Upper (D 7) (R 7) [6,257,33,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14620 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14621 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 3, region := 240, targets := 2 }], pairs := [(0,7),(3,0),(4,0),(4,1)], upper := (rows 7 259 37 26 208 96 232 168 424), lower := (rows 7 259 37 26 208 96 64 128 256), losses := [{ target := 7, region := (rows 9 2 12 8 16 112 64 0 256), good := (rows 7 259 37 63 112 96 96 0 256) }] }

theorem u14621 : Upper (D 7) (R 7) [6,257,33,18,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14622 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 7 259 37 56 82 40 192 192 448), lower := (rows 7 259 37 56 82 40 64 128 256), losses := [] }

theorem u14622 : Upper (D 7) (R 7) [6,257,33,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14622 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14623 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(2,6)], upper := (rows 7 259 37 56 82 96 200 136 392), lower := (rows 7 259 37 56 82 96 64 128 256), losses := [] }

theorem u14623 : Upper (D 7) (R 7) [6,257,33,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14624 : Route 9 := (fun mask => (mask,id))

def c14624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14624 : Upper (D 7) (R 7) [6,257,33,48,66,128] 13 := by
  apply FastRouting.sound _ _ [6,257,33,48,66,128] 13 (by decide) (choices 1) [8,128] r14624 c14624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2555
  · exact u2556

def b14625 : PairBound 9 := { available := 200, camps := [{ cop := 8, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 259 37 56 208 34 200 200 456), lower := (rows 7 259 37 56 208 34 64 128 256), losses := [] }

theorem u14625 : Upper (D 7) (R 7) [6,257,33,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14626 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 259 37 56 208 40 194 194 450), lower := (rows 7 259 37 56 208 40 64 128 256), losses := [] }

theorem u14626 : Upper (D 7) (R 7) [6,257,33,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14626 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14627 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 7 259 37 56 208 96 202 138 394), lower := (rows 7 259 37 56 208 96 64 128 256), losses := [] }

theorem u14627 : Upper (D 7) (R 7) [6,257,33,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14628 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 7 259 37 74 112 40 208 144 400), lower := (rows 7 259 37 74 112 40 64 128 256), losses := [] }

theorem u14628 : Upper (D 7) (R 7) [6,257,33,66,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14628 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14629 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 259 37 74 112 48 200 136 392), lower := (rows 7 259 37 74 112 48 64 128 256), losses := [] }

theorem u14629 : Upper (D 7) (R 7) [6,257,33,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14629 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14630 : Route 9 := (fun mask => (mask,id))

def c14630 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14630 : Upper (D 7) (R 7) [6,257,33,66,96,128] 13 := by
  apply FastRouting.sound _ _ [6,257,33,66,96,128] 13 (by decide) (choices 1) [8,16,128] r14630 c14630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2557
  · exact u2558
  · exact u2559

def b14631 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 3, region := 176, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 259 37 74 152 48 224 224 480), lower := (rows 7 259 37 74 152 48 64 128 256), losses := [] }

theorem u14631 : Upper (D 7) (R 7) [6,257,33,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14631 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14632 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(3,0),(4,0)], upper := (rows 7 259 37 74 152 96 240 176 432), lower := (rows 7 259 37 74 152 96 64 128 256), losses := [] }

theorem u14632 : Upper (D 7) (R 7) [6,257,33,66,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14633 : Route 9 := (fun mask => (mask,id))

def c14633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14633 : Upper (D 7) (R 7) [6,257,33,66,136,128] 13 := by
  apply FastRouting.sound _ _ [6,257,33,66,136,128] 13 (by decide) (choices 1) [16,32] r14633 c14633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2560
  · exact u2561

def b14634 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 7 259 37 74 176 40 208 208 464), lower := (rows 7 259 37 74 176 40 64 128 256), losses := [] }

theorem u14634 : Upper (D 7) (R 7) [6,257,33,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14634 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14635 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 259 37 74 176 48 200 200 456), lower := (rows 7 259 37 74 176 48 64 128 256), losses := [] }

theorem u14635 : Upper (D 7) (R 7) [6,257,33,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14635 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14636 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(2,7),(3,0),(4,0)], upper := (rows 7 259 37 74 176 96 216 152 408), lower := (rows 7 259 37 74 176 96 64 128 256), losses := [] }

theorem u14636 : Upper (D 7) (R 7) [6,257,33,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14637 : PairBound 9 := { available := 88, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 259 37 74 176 160 88 216 344), lower := (rows 7 259 37 74 176 160 64 128 256), losses := [] }

theorem u14637 : Upper (D 7) (R 7) [6,257,33,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14638 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 7 259 37 74 208 40 240 176 432), lower := (rows 7 259 37 74 208 40 64 128 256), losses := [] }

theorem u14638 : Upper (D 7) (R 7) [6,257,33,66,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14638 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14639 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 3, region := 176, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 259 37 74 208 48 232 168 424), lower := (rows 7 259 37 74 208 48 64 128 256), losses := [] }

theorem u14639 : Upper (D 7) (R 7) [6,257,33,66,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14639 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u14639
end Delivery.IrregularNine14.P07
