import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0033
import IrregularNine14P07C0034

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13560 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 292 73 208 34 209 145 401), lower := (rows 7 42 292 73 208 34 64 128 256), losses := [] }

theorem u13560 : Upper (D 7) (R 7) [6,40,288,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13561 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 42 292 73 208 48 195 131 387), lower := (rows 7 42 292 73 208 48 64 128 256), losses := [] }

theorem u13561 : Upper (D 7) (R 7) [6,40,288,65,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13561 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13562 : Route 9 := (fun mask => (mask,id))

def c13562 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13562 : Upper (D 7) (R 7) [6,40,288,65,192,128] 13 := by
  apply FastRouting.sound _ _ [6,40,288,65,192,128] 13 (by decide) (choices 1) [1,2,16] r13562 c13562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1991
  · exact u1992
  · exact u1993

def b13563 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 452, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(4,5)], upper := (rows 7 42 292 88 145 33 194 194 450), lower := (rows 7 42 292 88 145 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 38 24 16 32 67 131 259), good := (rows 454 494 292 88 472 484 64 128 256) }] }

theorem u13563 : Upper (D 7) (R 7) [6,40,288,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13564 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 292 88 145 34 193 193 449), lower := (rows 7 42 292 88 145 34 64 128 256), losses := [] }

theorem u13564 : Upper (D 7) (R 7) [6,40,288,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13565 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 7 42 292 88 145 96 195 131 387), lower := (rows 7 42 292 88 145 96 64 128 256), losses := [] }

theorem u13565 : Upper (D 7) (R 7) [6,40,288,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13566 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 292 88 145 160 67 195 323), lower := (rows 7 42 292 88 145 160 64 128 256), losses := [] }

theorem u13566 : Upper (D 7) (R 7) [6,40,288,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13567 : Route 9 := (fun mask => (mask,id))

def c13567 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13567 : Upper (D 7) (R 7) [6,40,288,80,130,1] 13 := by
  apply FastRouting.sound _ _ [6,40,288,80,130,1] 13 (by decide) (choices 1) [1,128] r13567 c13567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1994
  · exact u1995

def b13568 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 7 42 292 88 146 96 193 129 385), lower := (rows 7 42 292 88 146 96 64 128 256), losses := [] }

theorem u13568 : Upper (D 7) (R 7) [6,40,288,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13569 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 292 88 146 160 65 193 321), lower := (rows 7 42 292 88 146 160 64 128 256), losses := [] }

theorem u13569 : Upper (D 7) (R 7) [6,40,288,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13570 : Route 9 := (fun mask => (mask,id))

def c13570 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13570 : Upper (D 7) (R 7) [6,40,288,192,65,1] 13 := by
  apply FastRouting.sound _ _ [6,40,288,192,65,1] 13 (by decide) (choices 1) [2,16,128] r13570 c13570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1996
  · exact u1997
  · exact u1998

def b13571 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 292 200 81 34 209 145 401), lower := (rows 7 42 292 200 81 34 64 128 256), losses := [] }

theorem u13571 : Upper (D 7) (R 7) [6,40,288,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13572 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 42 292 200 81 48 195 131 387), lower := (rows 7 42 292 200 81 48 64 128 256), losses := [] }

theorem u13572 : Upper (D 7) (R 7) [6,40,288,192,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13572 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13573 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 292 200 81 160 83 147 275), lower := (rows 7 42 292 200 81 160 64 128 256), losses := [] }

theorem u13573 : Upper (D 7) (R 7) [6,40,288,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13574 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 324 25 82 33 224 160 416), lower := (rows 7 42 324 25 82 33 64 128 256), losses := [] }

theorem u13574 : Upper (D 7) (R 7) [6,40,320,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13575 : Route 9 := (fun mask => (mask,id))

def c13575 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13575 : Upper (D 7) (R 7) [6,40,320,17,66,128] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17,66,128] 13 (by decide) (choices 1) [1,32,128] r13575 c13575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1999
  · exact u2000
  · exact u2001

def b13576 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 324 25 112 33 194 130 386), lower := (rows 7 42 324 25 112 33 64 128 256), losses := [] }

theorem u13576 : Upper (D 7) (R 7) [6,40,320,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13577 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 324 25 112 34 193 129 385), lower := (rows 7 42 324 25 112 34 64 128 256), losses := [] }

theorem u13577 : Upper (D 7) (R 7) [6,40,320,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13578 : Route 9 := (fun mask => (mask,id))

def c13578 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13578 : Upper (D 7) (R 7) [6,40,320,17,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17,96,128] 13 (by decide) (choices 1) [1,2,128] r13578 c13578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2002
  · exact u2003
  · exact u2004

def b13579 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 324 25 146 33 224 224 480), lower := (rows 7 42 324 25 146 33 64 128 256), losses := [] }

theorem u13579 : Upper (D 7) (R 7) [6,40,320,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13580 : Route 9 := (fun mask => (mask,id))

def c13580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13580 : Upper (D 7) (R 7) [6,40,320,17,130,64] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17,130,64] 13 (by decide) (choices 1) [1,32,128] r13580 c13580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2005
  · exact u2006
  · exact u2007

def b13581 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,7),(1,0),(2,1),(2,7)], upper := (rows 7 42 324 25 146 160 97 225 353), lower := (rows 7 42 324 25 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 6 42 324 58 178 160 64 160 256) }] }

theorem u13581 : Upper (D 7) (R 7) [6,40,320,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13582 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,0),(2,5),(4,0)], upper := (rows 7 42 324 25 176 33 194 194 450), lower := (rows 7 42 324 25 176 33 64 128 256), losses := [] }

theorem u13582 : Upper (D 7) (R 7) [6,40,320,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13583 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 452, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 42 324 25 176 34 193 193 449), lower := (rows 7 42 324 25 176 34 64 128 256), losses := [] }

theorem u13583 : Upper (D 7) (R 7) [6,40,320,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13584 : Route 9 := (fun mask => (mask,id))

def c13584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13584 : Upper (D 7) (R 7) [6,40,320,17,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17,160,64] 13 (by decide) (choices 1) [1,2,128] r13584 c13584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2008
  · exact u2009
  · exact u2010

def b13585 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 324 25 176 160 67 195 323), lower := (rows 7 42 324 25 176 160 64 128 256), losses := [] }

theorem u13585 : Upper (D 7) (R 7) [6,40,320,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13586 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 64 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 324 25 208 33 226 162 418), lower := (rows 7 42 324 25 208 33 64 128 256), losses := [] }

theorem u13586 : Upper (D 7) (R 7) [6,40,320,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13587 : Route 9 := (fun mask => (mask,id))

def c13587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13587 : Upper (D 7) (R 7) [6,40,320,17,192,2] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17,192,2] 13 (by decide) (choices 1) [1,32,128] r13587 c13587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2011
  · exact u2012
  · exact u2013

def b13588 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 3, region := 162, targets := 64 }], pairs := [(0,7),(1,0),(1,6),(2,7)], upper := (rows 7 42 324 25 208 160 99 163 291), lower := (rows 7 42 324 25 208 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 6 42 324 58 240 160 64 160 256) }] }

theorem u13588 : Upper (D 7) (R 7) [6,40,320,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13589 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 42, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 42 324 26 145 33 224 224 480), lower := (rows 7 42 324 26 145 33 64 128 256), losses := [] }

theorem u13589 : Upper (D 7) (R 7) [6,40,320,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13590 : Route 9 := (fun mask => (mask,id))

def c13590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13590 : Upper (D 7) (R 7) [6,40,320,18,129,64] 13 := by
  apply FastRouting.sound _ _ [6,40,320,18,129,64] 13 (by decide) (choices 1) [1,32,128] r13590 c13590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2014
  · exact u2015
  · exact u2016

def b13591 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 324 26 145 160 97 225 353), lower := (rows 7 42 324 26 145 160 64 128 256), losses := [] }

theorem u13591 : Upper (D 7) (R 7) [6,40,320,18,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13592 : Route 9 := (fun mask => (mask,id))

def c13592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13592 : Upper (D 7) (R 7) [6,40,320,18,192,1] 13 := by
  apply FastRouting.sound _ _ [6,40,320,18,192,1] 13 (by decide) (choices 1) [1,32,128] r13592 c13592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2017
  · exact u2018
  · exact u2019

def b13593 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 324 26 208 160 97 161 289), lower := (rows 7 42 324 26 208 160 64 128 256), losses := [] }

theorem u13593 : Upper (D 7) (R 7) [6,40,320,18,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13594 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 324 73 49 34 208 144 400), lower := (rows 7 42 324 73 49 34 64 128 256), losses := [] }

theorem u13594 : Upper (D 7) (R 7) [6,40,320,65,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13595 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 42 324 73 49 48 194 130 386), lower := (rows 7 42 324 73 49 48 64 128 256), losses := [] }

theorem u13595 : Upper (D 7) (R 7) [6,40,320,65,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13595 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13596 : Route 9 := (fun mask => (mask,id))

def c13596 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13596 : Upper (D 7) (R 7) [6,40,320,65,33,128] 13 := by
  apply FastRouting.sound _ _ [6,40,320,65,33,128] 13 (by decide) (choices 1) [2,16,128] r13596 c13596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2020
  · exact u2021
  · exact u2022

def b13597 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 3, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(3,7)], upper := (rows 7 42 324 73 145 34 240 176 432), lower := (rows 7 42 324 73 145 34 64 128 256), losses := [] }

theorem u13597 : Upper (D 7) (R 7) [6,40,320,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13598 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 178, targets := 64 },{ cop := 1, region := 452, targets := 1 }], pairs := [(1,6),(2,0),(4,6)], upper := (rows 7 42 324 73 145 48 226 162 418), lower := (rows 7 42 324 73 145 48 64 128 256), losses := [] }

theorem u13598 : Upper (D 7) (R 7) [6,40,320,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13598 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13599 : Route 9 := (fun mask => (mask,id))

def c13599 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13599 : Upper (D 7) (R 7) [6,40,320,65,129,128] 13 := by
  apply FastRouting.sound _ _ [6,40,320,65,129,128] 13 (by decide) (choices 1) [2,16,32] r13599 c13599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2023
  · exact u2024
  · exact u2025

def b13600 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 1, region := 468, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 324 73 146 33 240 176 432), lower := (rows 7 42 324 73 146 33 64 128 256), losses := [] }

theorem u13600 : Upper (D 7) (R 7) [6,40,320,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13601 : Route 9 := (fun mask => (mask,id))

def c13601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13601 : Upper (D 7) (R 7) [6,40,320,65,130,16] 13 := by
  apply FastRouting.sound _ _ [6,40,320,65,130,16] 13 (by decide) (choices 1) [1,32,128] r13601 c13601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2026
  · exact u2027
  · exact u2028

def r13602 : Route 9 := (fun mask => (mask,id))

def c13602 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13602 : Upper (D 7) (R 7) [6,40,320,65,130,128] 13 := by
  apply FastRouting.sound _ _ [6,40,320,65,130,128] 13 (by decide) (choices 1) [1,16,32] r13602 c13602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2029
  · exact u2030
  · exact u2031

def b13603 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 1, region := 468, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 324 73 176 33 210 146 402), lower := (rows 7 42 324 73 176 33 64 128 256), losses := [] }

theorem u13603 : Upper (D 7) (R 7) [6,40,320,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13604 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 3, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(3,7)], upper := (rows 7 42 324 73 176 34 209 145 401), lower := (rows 7 42 324 73 176 34 64 128 256), losses := [] }

theorem u13604 : Upper (D 7) (R 7) [6,40,320,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13605 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 324 73 176 48 195 131 387), lower := (rows 7 42 324 73 176 48 64 128 256), losses := [] }

theorem u13605 : Upper (D 7) (R 7) [6,40,320,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13605 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13606 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 324 73 176 160 83 147 275), lower := (rows 7 42 324 73 176 160 64 128 256), losses := [] }

theorem u13606 : Upper (D 7) (R 7) [6,40,320,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13607 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 0, region := 500, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 7 42 324 74 145 33 240 176 432), lower := (rows 7 42 324 74 145 33 64 128 256), losses := [] }

theorem u13607 : Upper (D 7) (R 7) [6,40,320,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13608 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 176, targets := 64 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 7 42 324 74 145 48 225 161 417), lower := (rows 7 42 324 74 145 48 64 128 256), losses := [] }

theorem u13608 : Upper (D 7) (R 7) [6,40,320,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13608 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13609 : Route 9 := (fun mask => (mask,id))

def c13609 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13609 : Upper (D 7) (R 7) [6,40,320,66,129,128] 13 := by
  apply FastRouting.sound _ _ [6,40,320,66,129,128] 13 (by decide) (choices 1) [1,16,32] r13609 c13609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2032
  · exact u2033
  · exact u2034

def b13610 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 43, targets := 128 },{ cop := 0, region := 500, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 7 42 324 74 176 33 209 145 401), lower := (rows 7 42 324 74 176 33 64 128 256), losses := [] }

theorem u13610 : Upper (D 7) (R 7) [6,40,320,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13611 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 324 74 176 48 193 129 385), lower := (rows 7 42 324 74 176 48 64 128 256), losses := [] }

theorem u13611 : Upper (D 7) (R 7) [6,40,320,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13611 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13612 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 324 74 176 160 81 145 273), lower := (rows 7 42 324 74 176 160 64 128 256), losses := [] }

theorem u13612 : Upper (D 7) (R 7) [6,40,320,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13613 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 176, targets := 64 },{ cop := 1, region := 452, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(4,6)], upper := (rows 7 42 324 88 145 33 226 162 418), lower := (rows 7 42 324 88 145 33 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 49 49 0 139 267), good := (rows 439 442 260 442 433 433 0 128 256) },{ target := 7, region := (rows 1 10 4 8 16 49 64 0 256), good := (rows 39 42 324 122 49 33 64 0 256) }] }

theorem u13613 : Upper (D 7) (R 7) [6,40,320,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13614 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 176, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 7 42 324 88 145 34 225 161 417), lower := (rows 7 42 324 88 145 34 64 128 256), losses := [] }

theorem u13614 : Upper (D 7) (R 7) [6,40,320,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13615 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 0, region := 176, targets := 64 }], pairs := [(0,7),(1,0),(2,7),(4,6)], upper := (rows 7 42 324 88 145 160 99 163 291), lower := (rows 7 42 324 88 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 6 42 324 122 176 160 64 160 256) }] }

theorem u13615 : Upper (D 7) (R 7) [6,40,320,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13616 : Route 9 := (fun mask => (mask,id))

def c13616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13616 : Upper (D 7) (R 7) [6,40,320,80,130,1] 13 := by
  apply FastRouting.sound _ _ [6,40,320,80,130,1] 13 (by decide) (choices 1) [1,32,128] r13616 c13616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2035
  · exact u2036
  · exact u2037

def b13617 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 0, region := 484, targets := 2 },{ cop := 0, region := 176, targets := 64 }], pairs := [(0,7),(2,1),(2,7),(4,6)], upper := (rows 7 42 324 88 146 160 97 161 289), lower := (rows 7 42 324 88 146 160 64 128 256), losses := [] }

theorem u13617 : Upper (D 7) (R 7) [6,40,320,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13618 : Route 9 := (fun mask => (mask,id))

def c13618 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13618 : Upper (D 7) (R 7) [6,40,320,80,160,1] 13 := by
  apply FastRouting.sound _ _ [6,40,320,80,160,1] 13 (by decide) (choices 1) [1,2,128] r13618 c13618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2038
  · exact u2039
  · exact u2040

def b13619 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 452, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 42 324 88 176 34 193 129 385), lower := (rows 7 42 324 88 176 34 64 128 256), losses := [] }

theorem u13619 : Upper (D 7) (R 7) [6,40,320,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u13619
end Delivery.IrregularNine14.P07
