import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0170

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27600 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 322 76 168 19 160 83 147 275), lower := (rows 37 322 76 168 19 160 64 128 256), losses := [] }

theorem u27600 : Upper (D 7) (R 7) [36,320,72,160,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27601 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 76 168 145 33 82 146 274), lower := (rows 37 322 76 168 145 33 64 128 256), losses := [] }

theorem u27601 : Upper (D 7) (R 7) [36,320,72,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27602 : Route 9 := (fun mask => (mask,id))

def c27602 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27602 : Upper (D 7) (R 7) [36,320,72,160,129,2] 13 := by
  apply FastRouting.sound _ _ [36,320,72,160,129,2] 13 (by decide) (choices 1) [1,2,16] r27602 c27602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10201
  · exact u10202
  · exact u10203

def b27603 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 76 168 145 48 67 131 259), lower := (rows 37 322 76 168 145 48 64 128 256), losses := [] }

theorem u27603 : Upper (D 7) (R 7) [36,320,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27603 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27604 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 322 76 168 146 33 83 147 275), lower := (rows 37 322 76 168 146 33 64 128 256), losses := [] }

theorem u27604 : Upper (D 7) (R 7) [36,320,72,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27605 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 40, targets := 65 }], pairs := [(1,5),(3,0),(3,6),(4,5)], upper := (rows 37 322 76 168 146 34 81 145 273), lower := (rows 37 322 76 168 146 34 64 128 256), losses := [] }

theorem u27605 : Upper (D 7) (R 7) [36,320,72,160,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27606 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 322 76 168 146 48 67 131 259), lower := (rows 37 322 76 168 146 48 64 128 256), losses := [] }

theorem u27606 : Upper (D 7) (R 7) [36,320,72,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27606 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27607 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 3, region := 48, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 322 133 11 50 40 208 208 464), lower := (rows 37 322 133 11 50 40 64 128 256), losses := [] }

theorem u27607 : Upper (D 7) (R 7) [36,320,129,3,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27607 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27608 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 133 11 50 48 200 200 456), lower := (rows 37 322 133 11 50 48 64 128 256), losses := [] }

theorem u27608 : Upper (D 7) (R 7) [36,320,129,3,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27608 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27609 : PairBound 9 := { available := 152, camps := [{ cop := 4, region := 141, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 322 133 11 50 96 216 152 408), lower := (rows 37 322 133 11 50 96 64 128 256), losses := [] }

theorem u27609 : Upper (D 7) (R 7) [36,320,129,3,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27610 : PairBound 9 := { available := 88, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 11 50 160 88 216 344), lower := (rows 37 322 133 11 50 160 64 128 256), losses := [] }

theorem u27610 : Upper (D 7) (R 7) [36,320,129,3,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27611 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 48, targets := 192 }], pairs := [(1,0),(4,0),(4,6),(4,7)], upper := (rows 37 322 133 11 56 34 208 208 464), lower := (rows 37 322 133 11 56 34 64 128 256), losses := [] }

theorem u27611 : Upper (D 7) (R 7) [36,320,129,3,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27612 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 133 11 56 48 194 194 450), lower := (rows 37 322 133 11 56 48 64 128 256), losses := [] }

theorem u27612 : Upper (D 7) (R 7) [36,320,129,3,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27612 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27613 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(4,0),(4,1)], upper := (rows 37 322 133 11 56 96 210 146 402), lower := (rows 37 322 133 11 56 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 98 64 128 256), good := (rows 37 352 133 57 56 96 96 128 256) }] }

theorem u27613 : Upper (D 7) (R 7) [36,320,129,3,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27614 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 11 56 160 82 210 338), lower := (rows 37 322 133 11 56 160 64 128 256), losses := [] }

theorem u27614 : Upper (D 7) (R 7) [36,320,129,3,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27615 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 498, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 322 133 11 88 34 240 176 432), lower := (rows 37 322 133 11 88 34 64 128 256), losses := [{ target := 6, region := (rows 17 2 20 8 16 42 0 144 272), good := (rows 37 290 133 43 445 34 0 128 256) }] }

theorem u27615 : Upper (D 7) (R 7) [36,320,129,3,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27616 : Route 9 := (fun mask => (mask,id))

def c27616 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27616 : Upper (D 7) (R 7) [36,320,129,3,72,16] 13 := by
  apply FastRouting.sound _ _ [36,320,129,3,72,16] 13 (by decide) (choices 1) [2,32,128] r27616 c27616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10204
  · exact u10205
  · exact u10206

def b27617 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 11 88 160 114 178 306), lower := (rows 37 322 133 11 88 160 64 128 256), losses := [] }

theorem u27617 : Upper (D 7) (R 7) [36,320,129,3,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27618 : Route 9 := (fun mask => (mask,id))

def c27618 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u27618 : Upper (D 7) (R 7) [36,320,129,3,96,2] 13 := by
  apply FastRouting.sound _ _ [36,320,129,3,96,2] 13 (by decide) (choices 1) [8,16,128] r27618 c27618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10207
  · exact u10208
  · exact u10209

def b27619 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 4, region := 386, targets := 32 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 322 133 11 112 40 210 146 402), lower := (rows 37 322 133 11 112 40 64 128 256), losses := [] }

theorem u27619 : Upper (D 7) (R 7) [36,320,129,3,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27619 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27620 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 322 133 11 112 48 202 138 394), lower := (rows 37 322 133 11 112 48 64 128 256), losses := [] }

theorem u27620 : Upper (D 7) (R 7) [36,320,129,3,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27620 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27621 : PairBound 9 := { available := 26, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 11 112 160 90 154 282), lower := (rows 37 322 133 11 112 160 64 128 256), losses := [] }

theorem u27621 : Upper (D 7) (R 7) [36,320,129,3,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27622 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 322 133 11 146 40 112 240 368), lower := (rows 37 322 133 11 146 40 64 128 256), losses := [] }

theorem u27622 : Upper (D 7) (R 7) [36,320,129,3,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27622 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27623 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 322 133 11 146 48 104 232 360), lower := (rows 37 322 133 11 146 48 64 128 256), losses := [] }

theorem u27623 : Upper (D 7) (R 7) [36,320,129,3,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27623 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27624 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 322 133 11 146 96 120 184 312), lower := (rows 37 322 133 11 146 96 64 128 256), losses := [{ target := 1, region := (rows 17 0 20 8 16 98 64 128 256), good := (rows 37 352 133 41 181 96 96 128 256) }] }

theorem u27624 : Upper (D 7) (R 7) [36,320,129,3,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27625 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 4, region := 354, targets := 128 }], pairs := [(0,6),(1,0),(1,7),(4,0)], upper := (rows 37 322 133 11 152 34 112 240 368), lower := (rows 37 322 133 11 152 34 64 128 256), losses := [{ target := 6, region := (rows 17 2 20 8 16 42 0 128 256), good := (rows 37 290 133 43 189 34 0 128 256) }] }

theorem u27625 : Upper (D 7) (R 7) [36,320,129,3,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27626 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 11 152 48 98 226 354), lower := (rows 37 322 133 11 152 48 64 128 256), losses := [] }

theorem u27626 : Upper (D 7) (R 7) [36,320,129,3,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27626 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27627 : Route 9 := (fun mask => (mask,id))

def c27627 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27627 : Upper (D 7) (R 7) [36,320,129,3,136,64] 13 := by
  apply FastRouting.sound _ _ [36,320,129,3,136,64] 13 (by decide) (choices 1) [2,16,32] r27627 c27627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10210
  · exact u10211
  · exact u10212

def r27628 : Route 9 := (fun mask => (mask,id))

def c27628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27628 : Upper (D 7) (R 7) [36,320,129,3,192,2] 13 := by
  apply FastRouting.sound _ _ [36,320,129,3,192,2] 13 (by decide) (choices 1) [8,16,32] r27628 c27628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10213
  · exact u10214
  · exact u10215

def r27629 : Route 9 := (fun mask => (mask,id))

def c27629 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27629 : Upper (D 7) (R 7) [36,320,129,3,192,8] 13 := by
  apply FastRouting.sound _ _ [36,320,129,3,192,8] 13 (by decide) (choices 1) [2,16,32] r27629 c27629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10216
  · exact u10217
  · exact u10218

def b27630 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 11 208 48 106 170 298), lower := (rows 37 322 133 11 208 48 64 128 256), losses := [] }

theorem u27630 : Upper (D 7) (R 7) [36,320,129,3,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27630 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27631 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(4,0)], upper := (rows 37 322 133 25 26 34 224 224 480), lower := (rows 37 322 133 25 26 34 64 128 256), losses := [] }

theorem u27631 : Upper (D 7) (R 7) [36,320,129,17,10,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27632 : Route 9 := (fun mask => (mask,id))

def c27632 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u27632 : Upper (D 7) (R 7) [36,320,129,17,10,64] 13 := by
  apply FastRouting.sound _ _ [36,320,129,17,10,64] 13 (by decide) (choices 1) [2,32,128] r27632 c27632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10219
  · exact u10220
  · exact u10221

def b27633 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 25 26 160 98 226 354), lower := (rows 37 322 133 25 26 160 64 128 256), losses := [] }

theorem u27633 : Upper (D 7) (R 7) [36,320,129,17,10,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27634 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 3, region := 354, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 37 322 133 25 146 34 104 232 360), lower := (rows 37 322 133 25 146 34 64 128 256), losses := [] }

theorem u27634 : Upper (D 7) (R 7) [36,320,129,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27635 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 25 146 40 98 226 354), lower := (rows 37 322 133 25 146 40 64 128 256), losses := [] }

theorem u27635 : Upper (D 7) (R 7) [36,320,129,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27635 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27636 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 354, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(4,0)], upper := (rows 37 322 133 25 146 96 106 170 298), lower := (rows 37 322 133 25 146 96 64 128 256), losses := [{ target := 1, region := (rows 17 0 20 24 16 98 64 128 256), good := (rows 37 352 133 29 189 96 96 128 256) }] }

theorem u27636 : Upper (D 7) (R 7) [36,320,129,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27637 : Route 9 := (fun mask => (mask,id))

def c27637 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27637 : Upper (D 7) (R 7) [36,320,129,17,192,2] 13 := by
  apply FastRouting.sound _ _ [36,320,129,17,192,2] 13 (by decide) (choices 1) [2,8,32] r27637 c27637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10222
  · exact u10223
  · exact u10224

def b27638 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 45, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 322 133 25 208 40 98 162 290), lower := (rows 37 322 133 25 208 40 64 128 256), losses := [] }

theorem u27638 : Upper (D 7) (R 7) [36,320,129,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27638 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27639 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 322 133 26 56 33 194 194 450), lower := (rows 37 322 133 26 56 33 64 128 256), losses := [] }

theorem u27639 : Upper (D 7) (R 7) [36,320,129,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27640 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 56, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 37 322 133 26 56 34 193 193 449), lower := (rows 37 322 133 26 56 34 64 128 256), losses := [] }

theorem u27640 : Upper (D 7) (R 7) [36,320,129,18,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27641 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 37 322 133 26 56 96 195 131 387), lower := (rows 37 322 133 26 56 96 64 128 256), losses := [] }

theorem u27641 : Upper (D 7) (R 7) [36,320,129,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27642 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 26 56 160 67 195 323), lower := (rows 37 322 133 26 56 160 64 128 256), losses := [] }

theorem u27642 : Upper (D 7) (R 7) [36,320,129,18,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27643 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 322 133 26 112 33 202 138 394), lower := (rows 37 322 133 26 112 33 64 128 256), losses := [] }

theorem u27643 : Upper (D 7) (R 7) [36,320,129,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27644 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 37 322 133 26 112 34 201 137 393), lower := (rows 37 322 133 26 112 34 64 128 256), losses := [] }

theorem u27644 : Upper (D 7) (R 7) [36,320,129,18,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27645 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 37 322 133 26 112 40 195 131 387), lower := (rows 37 322 133 26 112 40 64 128 256), losses := [] }

theorem u27645 : Upper (D 7) (R 7) [36,320,129,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27645 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27646 : PairBound 9 := { available := 11, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 26 112 160 75 139 267), lower := (rows 37 322 133 26 112 160 64 128 256), losses := [] }

theorem u27646 : Upper (D 7) (R 7) [36,320,129,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27647 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 26 152 33 98 226 354), lower := (rows 37 322 133 26 152 33 64 128 256), losses := [] }

theorem u27647 : Upper (D 7) (R 7) [36,320,129,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27648 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,1)], upper := (rows 37 322 133 26 152 34 97 225 353), lower := (rows 37 322 133 26 152 34 64 128 256), losses := [] }

theorem u27648 : Upper (D 7) (R 7) [36,320,129,18,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27649 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(2,1)], upper := (rows 37 322 133 26 152 96 99 163 291), lower := (rows 37 322 133 26 152 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 20 8 16 98 64 128 256), good := (rows 37 352 133 61 157 96 96 128 256) }] }

theorem u27649 : Upper (D 7) (R 7) [36,320,129,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27650 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 26 208 33 106 170 298), lower := (rows 37 322 133 26 208 33 64 128 256), losses := [] }

theorem u27650 : Upper (D 7) (R 7) [36,320,129,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27650 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r27651 : Route 9 := (fun mask => (mask,id))

def c27651 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27651 : Upper (D 7) (R 7) [36,320,129,18,192,2] 13 := by
  apply FastRouting.sound _ _ [36,320,129,18,192,2] 13 (by decide) (choices 1) [1,8,32] r27651 c27651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10225
  · exact u10226
  · exact u10227

def b27652 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,6),(1,7),(2,6)], upper := (rows 37 322 133 26 208 40 99 163 291), lower := (rows 37 322 133 26 208 40 64 128 256), losses := [] }

theorem u27652 : Upper (D 7) (R 7) [36,320,129,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27652 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27653 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 322 133 42 81 34 216 152 408), lower := (rows 37 322 133 42 81 34 64 128 256), losses := [] }

theorem u27653 : Upper (D 7) (R 7) [36,320,129,34,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27654 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 322 133 42 81 40 210 146 402), lower := (rows 37 322 133 42 81 40 64 128 256), losses := [] }

theorem u27654 : Upper (D 7) (R 7) [36,320,129,34,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27654 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27655 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 3, region := 133, targets := 64 }], pairs := [(0,6),(1,0),(3,0)], upper := (rows 37 322 133 42 81 48 202 138 394), lower := (rows 37 322 133 42 81 48 64 128 256), losses := [] }

theorem u27655 : Upper (D 7) (R 7) [36,320,129,34,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27655 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27656 : PairBound 9 := { available := 26, camps := [{ cop := 5, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 42 81 160 90 154 282), lower := (rows 37 322 133 42 81 160 64 128 256), losses := [] }

theorem u27656 : Upper (D 7) (R 7) [36,320,129,34,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27657 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 322 133 42 88 33 210 146 402), lower := (rows 37 322 133 42 88 33 64 128 256), losses := [] }

theorem u27657 : Upper (D 7) (R 7) [36,320,129,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27658 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 37 322 133 42 88 34 209 145 401), lower := (rows 37 322 133 42 88 34 64 128 256), losses := [] }

theorem u27658 : Upper (D 7) (R 7) [36,320,129,34,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27659 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 37 322 133 42 88 48 195 131 387), lower := (rows 37 322 133 42 88 48 64 128 256), losses := [] }

theorem u27659 : Upper (D 7) (R 7) [36,320,129,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27659 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u27659
end Delivery.IrregularNine14.P07
