import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0088

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19560 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 265 145 96 114 178 306), lower := (rows 35 70 140 265 145 96 64 128 256), losses := [] }

theorem u19560 : Upper (D 7) (R 7) [34,68,136,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19561 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 1 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,0)], upper := (rows 35 70 140 265 146 33 112 240 368), lower := (rows 35 70 140 265 146 33 64 128 256), losses := [] }

theorem u19561 : Upper (D 7) (R 7) [34,68,136,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19562 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 35 70 140 265 146 48 97 225 353), lower := (rows 35 70 140 265 146 48 64 128 256), losses := [] }

theorem u19562 : Upper (D 7) (R 7) [34,68,136,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19562 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19563 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 265 146 96 113 177 305), lower := (rows 35 70 140 265 146 96 64 128 256), losses := [] }

theorem u19563 : Upper (D 7) (R 7) [34,68,136,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19564 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 1 }], pairs := [(0,6),(0,7),(1,0),(4,0)], upper := (rows 35 70 140 265 176 33 82 210 338), lower := (rows 35 70 140 265 176 33 64 128 256), losses := [{ target := 0, region := (rows 0 14 12 8 49 32 73 137 265), good := (rows 498 70 462 478 176 496 64 128 256) }] }

theorem u19564 : Upper (D 7) (R 7) [34,68,136,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19565 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 265 176 34 81 209 337), lower := (rows 35 70 140 265 176 34 64 128 256), losses := [] }

theorem u19565 : Upper (D 7) (R 7) [34,68,136,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19566 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 140 265 176 48 67 195 323), lower := (rows 35 70 140 265 176 48 64 128 256), losses := [] }

theorem u19566 : Upper (D 7) (R 7) [34,68,136,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19566 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19567 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 265 176 96 83 147 275), lower := (rows 35 70 140 265 176 96 64 128 256), losses := [] }

theorem u19567 : Upper (D 7) (R 7) [34,68,136,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19568 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 1 }], pairs := [(0,6),(0,7),(1,0),(4,0)], upper := (rows 35 70 140 265 208 33 114 178 306), lower := (rows 35 70 140 265 208 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 57 32 65 129 257), good := (rows 498 70 158 478 208 496 64 128 256) }] }

theorem u19568 : Upper (D 7) (R 7) [34,68,136,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19569 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 265 208 34 113 177 305), lower := (rows 35 70 140 265 208 34 64 128 256), losses := [] }

theorem u19569 : Upper (D 7) (R 7) [34,68,136,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19570 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 0, region := 264, targets := 128 }], pairs := [(2,6),(3,6),(3,7)], upper := (rows 35 70 140 265 208 48 99 163 291), lower := (rows 35 70 140 265 208 48 64 128 256), losses := [] }

theorem u19570 : Upper (D 7) (R 7) [34,68,136,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19570 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19571 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,7)], upper := (rows 35 70 140 266 81 33 240 176 432), lower := (rows 35 70 140 266 81 33 64 128 256), losses := [] }

theorem u19571 : Upper (D 7) (R 7) [34,68,136,258,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19572 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 70 140 266 81 48 225 161 417), lower := (rows 35 70 140 266 81 48 64 128 256), losses := [] }

theorem u19572 : Upper (D 7) (R 7) [34,68,136,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19572 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19573 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 0, region := 80, targets := 2 }], pairs := [(0,6),(3,7),(4,1),(4,7)], upper := (rows 35 70 140 266 81 160 113 177 305), lower := (rows 35 70 140 266 81 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 180 0 144 272), good := (rows 35 39 172 267 433 160 0 160 256) }] }

theorem u19573 : Upper (D 7) (R 7) [34,68,136,258,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19574 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,7)], upper := (rows 35 70 140 266 112 33 209 145 401), lower := (rows 35 70 140 266 112 33 64 128 256), losses := [] }

theorem u19574 : Upper (D 7) (R 7) [34,68,136,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19575 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 140 266 112 48 193 129 385), lower := (rows 35 70 140 266 112 48 64 128 256), losses := [] }

theorem u19575 : Upper (D 7) (R 7) [34,68,136,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19575 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19576 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,7),(4,0),(4,1),(4,7)], upper := (rows 35 70 140 266 112 160 81 145 273), lower := (rows 35 70 140 266 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 164 64 128 256), good := (rows 50 118 172 282 112 160 64 160 256) }] }

theorem u19576 : Upper (D 7) (R 7) [34,68,136,258,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19577 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(0,7),(4,1),(4,6)], upper := (rows 35 70 140 266 145 33 112 240 368), lower := (rows 35 70 140 266 145 33 64 128 256), losses := [{ target := 6, region := (rows 11 2 4 8 20 63 0 128 256), good := (rows 35 55 189 299 177 33 0 128 256) }] }

theorem u19577 : Upper (D 7) (R 7) [34,68,136,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19578 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 208, targets := 2 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,6),(3,7),(4,1)], upper := (rows 35 70 140 266 145 48 97 225 353), lower := (rows 35 70 140 266 145 48 64 128 256), losses := [{ target := 6, region := (rows 11 2 4 8 20 54 0 128 256), good := (rows 35 55 189 299 177 48 0 128 256) }] }

theorem u19578 : Upper (D 7) (R 7) [34,68,136,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19578 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19579 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 140 266 145 96 113 177 305), lower := (rows 35 70 140 266 145 96 64 128 256), losses := [] }

theorem u19579 : Upper (D 7) (R 7) [34,68,136,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19580 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(0,7),(4,1),(4,6)], upper := (rows 35 70 140 266 176 33 81 209 337), lower := (rows 35 70 140 266 176 33 64 128 256), losses := [{ target := 6, region := (rows 11 2 4 8 20 47 0 128 256), good := (rows 35 55 189 299 176 33 0 128 256) }] }

theorem u19580 : Upper (D 7) (R 7) [34,68,136,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19581 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 140 266 176 48 65 193 321), lower := (rows 35 70 140 266 176 48 64 128 256), losses := [] }

theorem u19581 : Upper (D 7) (R 7) [34,68,136,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19581 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19582 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 140 266 176 96 81 145 273), lower := (rows 35 70 140 266 176 96 64 128 256), losses := [] }

theorem u19582 : Upper (D 7) (R 7) [34,68,136,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19583 : Route 9 := (fun mask => (mask,id))

def c19583 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19583 : Upper (D 7) (R 7) [34,68,136,258,192,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258,192,1] 13 (by decide) (choices 1) [1,16,32] r19583 c19583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5318
  · exact u5319
  · exact u5320

def b19584 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(2,6),(3,6),(4,1)], upper := (rows 35 70 140 266 208 48 97 161 289), lower := (rows 35 70 140 266 208 48 64 128 256), losses := [] }

theorem u19584 : Upper (D 7) (R 7) [34,68,136,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19584 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19585 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(4,7)], upper := (rows 35 70 140 280 81 33 226 162 418), lower := (rows 35 70 140 280 81 33 64 128 256), losses := [{ target := 0, region := (rows 0 18 20 24 16 32 65 129 257), good := (rows 482 70 140 286 478 480 64 128 256) }] }

theorem u19585 : Upper (D 7) (R 7) [34,68,136,272,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19586 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 280 81 34 225 161 417), lower := (rows 35 70 140 280 81 34 64 128 256), losses := [] }

theorem u19586 : Upper (D 7) (R 7) [34,68,136,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19587 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(2,6),(3,7),(4,7)], upper := (rows 35 70 140 280 81 160 99 163 291), lower := (rows 35 70 140 280 81 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 20 24 16 183 0 131 259), good := (rows 419 423 172 316 445 160 0 160 256) }] }

theorem u19587 : Upper (D 7) (R 7) [34,68,136,272,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19588 : Route 9 := (fun mask => (mask,id))

def c19588 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19588 : Upper (D 7) (R 7) [34,68,136,272,96,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,96,1] 13 (by decide) (choices 1) [1,2,128] r19588 c19588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5321
  · exact u5322
  · exact u5323

def b19589 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 280 112 34 193 129 385), lower := (rows 35 70 140 280 112 34 64 128 256), losses := [] }

theorem u19589 : Upper (D 7) (R 7) [34,68,136,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19590 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,7),(4,0),(4,7)], upper := (rows 35 70 140 280 112 160 67 131 259), lower := (rows 35 70 140 280 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 164 64 128 256), good := (rows 50 118 172 280 112 160 64 160 256) }] }

theorem u19590 : Upper (D 7) (R 7) [34,68,136,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19591 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7)], upper := (rows 35 70 140 280 145 33 98 226 354), lower := (rows 35 70 140 280 145 33 64 128 256), losses := [{ target := 0, region := (rows 0 18 20 24 16 32 65 129 257), good := (rows 482 70 140 286 478 480 64 128 256) }] }

theorem u19591 : Upper (D 7) (R 7) [34,68,136,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19592 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 280 145 34 97 225 353), lower := (rows 35 70 140 280 145 34 64 128 256), losses := [] }

theorem u19592 : Upper (D 7) (R 7) [34,68,136,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19593 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 280 145 96 99 163 291), lower := (rows 35 70 140 280 145 96 64 128 256), losses := [] }

theorem u19593 : Upper (D 7) (R 7) [34,68,136,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19594 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 1, region := 33, targets := 64 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(3,7)], upper := (rows 35 70 140 280 146 33 97 225 353), lower := (rows 35 70 140 280 146 33 64 128 256), losses := [] }

theorem u19594 : Upper (D 7) (R 7) [34,68,136,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19595 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 280 146 96 97 161 289), lower := (rows 35 70 140 280 146 96 64 128 256), losses := [] }

theorem u19595 : Upper (D 7) (R 7) [34,68,136,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19596 : Route 9 := (fun mask => (mask,id))

def c19596 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19596 : Upper (D 7) (R 7) [34,68,136,272,160,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,160,1] 13 (by decide) (choices 1) [1,2] r19596 c19596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5324
  · exact u5325

def b19597 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 280 176 34 65 193 321), lower := (rows 35 70 140 280 176 34 64 128 256), losses := [] }

theorem u19597 : Upper (D 7) (R 7) [34,68,136,272,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19598 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 280 176 96 67 131 259), lower := (rows 35 70 140 280 176 96 64 128 256), losses := [] }

theorem u19598 : Upper (D 7) (R 7) [34,68,136,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19599 : Route 9 := (fun mask => (mask,id))

def c19599 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19599 : Upper (D 7) (R 7) [34,68,136,272,192,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,192,1] 13 (by decide) (choices 1) [1,2,32] r19599 c19599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5326
  · exact u5327
  · exact u5328

def b19600 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 280 208 34 97 161 289), lower := (rows 35 70 140 280 208 34 64 128 256), losses := [] }

theorem u19600 : Upper (D 7) (R 7) [34,68,136,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19601 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 0, region := 208, targets := 32 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,5),(4,7)], upper := (rows 35 70 140 296 81 33 210 146 402), lower := (rows 35 70 140 296 81 33 64 128 256), losses := [] }

theorem u19601 : Upper (D 7) (R 7) [34,68,136,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19602 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 296 81 34 209 145 401), lower := (rows 35 70 140 296 81 34 64 128 256), losses := [] }

theorem u19602 : Upper (D 7) (R 7) [34,68,136,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19603 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 70 140 296 81 48 195 131 387), lower := (rows 35 70 140 296 81 48 64 128 256), losses := [] }

theorem u19603 : Upper (D 7) (R 7) [34,68,136,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19603 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19604 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 0, region := 80, targets := 32 }], pairs := [(0,6),(3,7),(4,5),(4,7)], upper := (rows 35 70 140 296 81 160 83 147 275), lower := (rows 35 70 140 296 81 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 172 296 17 160 0 160 256) }] }

theorem u19604 : Upper (D 7) (R 7) [34,68,136,288,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19605 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,6),(0,7),(1,5),(4,5)], upper := (rows 35 70 140 296 145 33 82 210 338), lower := (rows 35 70 140 296 145 33 64 128 256), losses := [{ target := 5, region := (rows 1 14 12 8 49 0 73 137 265), good := (rows 467 70 462 478 465 465 64 128 256) }] }

theorem u19605 : Upper (D 7) (R 7) [34,68,136,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19606 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 296 145 34 81 209 337), lower := (rows 35 70 140 296 145 34 64 128 256), losses := [] }

theorem u19606 : Upper (D 7) (R 7) [34,68,136,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19607 : Route 9 := (fun mask => (mask,id))

def c19607 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19607 : Upper (D 7) (R 7) [34,68,136,288,129,16] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,129,16] 13 (by decide) (choices 1) [1,2] r19607 c19607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5329
  · exact u5330

def b19608 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(2,6),(3,6),(4,5),(4,6)], upper := (rows 35 70 140 296 145 96 83 147 275), lower := (rows 35 70 140 296 145 96 64 128 256), losses := [] }

theorem u19608 : Upper (D 7) (R 7) [34,68,136,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19609 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,5)], upper := (rows 35 70 140 296 146 33 81 209 337), lower := (rows 35 70 140 296 146 33 64 128 256), losses := [] }

theorem u19609 : Upper (D 7) (R 7) [34,68,136,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19610 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1)], upper := (rows 35 70 140 296 146 48 65 193 321), lower := (rows 35 70 140 296 146 48 64 128 256), losses := [] }

theorem u19610 : Upper (D 7) (R 7) [34,68,136,288,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19610 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19611 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 296 146 96 81 145 273), lower := (rows 35 70 140 296 146 96 64 128 256), losses := [] }

theorem u19611 : Upper (D 7) (R 7) [34,68,136,288,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19612 : Route 9 := (fun mask => (mask,id))

def c19612 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19612 : Upper (D 7) (R 7) [34,68,136,288,192,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288,192,1] 13 (by decide) (choices 1) [1,2,16] r19612 c19612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5331
  · exact u5332
  · exact u5333

def b19613 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 296 208 34 81 145 273), lower := (rows 35 70 140 296 208 34 64 128 256), losses := [] }

theorem u19613 : Upper (D 7) (R 7) [34,68,136,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19614 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,6),(3,6),(4,5)], upper := (rows 35 70 140 296 208 48 67 131 259), lower := (rows 35 70 140 296 208 48 64 128 256), losses := [] }

theorem u19614 : Upper (D 7) (R 7) [34,68,136,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19614 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19615 : Route 9 := (fun mask => (mask,id))

def c19615 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19615 : Upper (D 7) (R 7) [34,68,136,320,129,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,129,1] 13 (by decide) (choices 1) [2,16,32] r19615 c19615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5334
  · exact u5335
  · exact u5336

def b19616 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 328 145 34 113 177 305), lower := (rows 35 70 140 328 145 34 64 128 256), losses := [] }

theorem u19616 : Upper (D 7) (R 7) [34,68,136,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19617 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,6),(3,7),(4,6)], upper := (rows 35 70 140 328 145 48 99 163 291), lower := (rows 35 70 140 328 145 48 64 128 256), losses := [] }

theorem u19617 : Upper (D 7) (R 7) [34,68,136,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19617 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19618 : Route 9 := (fun mask => (mask,id))

def c19618 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19618 : Upper (D 7) (R 7) [34,68,136,320,160,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320,160,1] 13 (by decide) (choices 1) [1,2,16] r19618 c19618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5337
  · exact u5338
  · exact u5339

def b19619 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 328 176 34 81 145 273), lower := (rows 35 70 140 328 176 34 64 128 256), losses := [] }

theorem u19619 : Upper (D 7) (R 7) [34,68,136,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u19619
end Delivery.IrregularNine14.P07
