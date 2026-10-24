import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0091

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19980 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 168 81 34 209 145 401), lower := (rows 35 70 268 168 81 34 64 128 256), losses := [] }

theorem u19980 : Upper (D 7) (R 7) [34,68,264,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19981 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 70 268 168 81 48 195 131 387), lower := (rows 35 70 268 168 81 48 64 128 256), losses := [] }

theorem u19981 : Upper (D 7) (R 7) [34,68,264,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19981 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19982 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 70 268 168 81 160 83 147 275), lower := (rows 35 70 268 168 81 160 64 128 256), losses := [] }

theorem u19982 : Upper (D 7) (R 7) [34,68,264,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19983 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 4, region := 40, targets := 66 }], pairs := [(0,6),(0,7),(3,1),(3,6)], upper := (rows 35 70 268 168 145 33 82 210 338), lower := (rows 35 70 268 168 145 33 64 128 256), losses := [] }

theorem u19983 : Upper (D 7) (R 7) [34,68,264,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19984 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 168 145 34 81 209 337), lower := (rows 35 70 268 168 145 34 64 128 256), losses := [] }

theorem u19984 : Upper (D 7) (R 7) [34,68,264,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19985 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 268 168 145 48 67 195 323), lower := (rows 35 70 268 168 145 48 64 128 256), losses := [] }

theorem u19985 : Upper (D 7) (R 7) [34,68,264,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19985 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19986 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(2,6),(3,6),(4,5),(4,6)], upper := (rows 35 70 268 168 145 96 83 147 275), lower := (rows 35 70 268 168 145 96 64 128 256), losses := [] }

theorem u19986 : Upper (D 7) (R 7) [34,68,264,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19987 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(0,7),(3,6),(4,5)], upper := (rows 35 70 268 168 146 33 81 209 337), lower := (rows 35 70 268 168 146 33 64 128 256), losses := [] }

theorem u19987 : Upper (D 7) (R 7) [34,68,264,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19988 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 268 168 146 48 65 193 321), lower := (rows 35 70 268 168 146 48 64 128 256), losses := [] }

theorem u19988 : Upper (D 7) (R 7) [34,68,264,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19988 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19989 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(2,6),(3,6),(4,5),(4,6)], upper := (rows 35 70 268 168 146 96 81 145 273), lower := (rows 35 70 268 168 146 96 64 128 256), losses := [] }

theorem u19989 : Upper (D 7) (R 7) [34,68,264,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19990 : Route 9 := (fun mask => (mask,id))

def c19990 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19990 : Upper (D 7) (R 7) [34,68,264,160,192,1] 13 := by
  apply FastRouting.sound _ _ [34,68,264,160,192,1] 13 (by decide) (choices 1) [1,2,16] r19990 c19990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5483
  · exact u5484
  · exact u5485

def b19991 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 168 208 34 81 145 273), lower := (rows 35 70 268 168 208 34 64 128 256), losses := [] }

theorem u19991 : Upper (D 7) (R 7) [34,68,264,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19992 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 268 168 208 48 67 131 259), lower := (rows 35 70 268 168 208 48 64 128 256), losses := [] }

theorem u19992 : Upper (D 7) (R 7) [34,68,264,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19992 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19993 : Route 9 := (fun mask => (mask,id))

def c19993 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19993 : Upper (D 7) (R 7) [34,68,264,192,129,1] 13 := by
  apply FastRouting.sound _ _ [34,68,264,192,129,1] 13 (by decide) (choices 1) [2,16,32] r19993 c19993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5486
  · exact u5487
  · exact u5488

def b19994 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 200 145 34 113 177 305), lower := (rows 35 70 268 200 145 34 64 128 256), losses := [] }

theorem u19994 : Upper (D 7) (R 7) [34,68,264,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19995 : Route 9 := (fun mask => (mask,id))

def c19995 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19995 : Upper (D 7) (R 7) [34,68,264,192,129,16] 13 := by
  apply FastRouting.sound _ _ [34,68,264,192,129,16] 13 (by decide) (choices 1) [1,2,32] r19995 c19995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5489
  · exact u5490
  · exact u5491

def r19996 : Route 9 := (fun mask => (mask,id))

def c19996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19996 : Upper (D 7) (R 7) [34,68,264,192,130,1] 13 := by
  apply FastRouting.sound _ _ [34,68,264,192,130,1] 13 (by decide) (choices 1) [1,16,32] r19996 c19996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5492
  · exact u5493
  · exact u5494

def b19997 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 268 200 146 48 97 161 289), lower := (rows 35 70 268 200 146 48 64 128 256), losses := [] }

theorem u19997 : Upper (D 7) (R 7) [34,68,264,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19997 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19998 : Route 9 := (fun mask => (mask,id))

def c19998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19998 : Upper (D 7) (R 7) [34,68,264,192,160,1] 13 := by
  apply FastRouting.sound _ _ [34,68,264,192,160,1] 13 (by decide) (choices 1) [1,2,16] r19998 c19998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5495
  · exact u5496
  · exact u5497

def b19999 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 268 200 176 34 81 145 273), lower := (rows 35 70 268 200 176 34 64 128 256), losses := [] }

theorem u19999 : Upper (D 7) (R 7) [34,68,264,192,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20000 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 268 200 176 48 67 131 259), lower := (rows 35 70 268 200 176 48 64 128 256), losses := [] }

theorem u20000 : Upper (D 7) (R 7) [34,68,264,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20000 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20001 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 292 25 146 33 200 200 456), lower := (rows 35 70 292 25 146 33 64 128 256), losses := [] }

theorem u20001 : Upper (D 7) (R 7) [34,68,288,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20002 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 70 292 25 146 40 193 193 449), lower := (rows 35 70 292 25 146 40 64 128 256), losses := [] }

theorem u20002 : Upper (D 7) (R 7) [34,68,288,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20002 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20003 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 152, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 292 25 146 96 201 137 393), lower := (rows 35 70 292 25 146 96 64 128 256), losses := [] }

theorem u20003 : Upper (D 7) (R 7) [34,68,288,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20004 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(3,5),(3,6),(4,5)], upper := (rows 35 70 292 25 146 160 73 201 329), lower := (rows 35 70 292 25 146 160 64 128 256), losses := [] }

theorem u20004 : Upper (D 7) (R 7) [34,68,288,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20005 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 0, region := 216, targets := 32 }], pairs := [(1,0),(2,0),(3,5),(4,5)], upper := (rows 35 70 292 25 152 33 194 194 450), lower := (rows 35 70 292 25 152 33 64 128 256), losses := [] }

theorem u20005 : Upper (D 7) (R 7) [34,68,288,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20006 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 292 25 152 34 193 193 449), lower := (rows 35 70 292 25 152 34 64 128 256), losses := [] }

theorem u20006 : Upper (D 7) (R 7) [34,68,288,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20007 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 152, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 292 25 152 96 195 131 387), lower := (rows 35 70 292 25 152 96 64 128 256), losses := [] }

theorem u20007 : Upper (D 7) (R 7) [34,68,288,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20008 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 35 70 292 25 152 160 67 195 323), lower := (rows 35 70 292 25 152 160 64 128 256), losses := [] }

theorem u20008 : Upper (D 7) (R 7) [34,68,288,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20009 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 292 25 208 33 202 138 394), lower := (rows 35 70 292 25 208 33 64 128 256), losses := [] }

theorem u20009 : Upper (D 7) (R 7) [34,68,288,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20010 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 292 25 208 34 201 137 393), lower := (rows 35 70 292 25 208 34 64 128 256), losses := [] }

theorem u20010 : Upper (D 7) (R 7) [34,68,288,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20011 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 292 25 208 40 195 131 387), lower := (rows 35 70 292 25 208 40 64 128 256), losses := [] }

theorem u20011 : Upper (D 7) (R 7) [34,68,288,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20011 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20012 : Route 9 := (fun mask => (mask,id))

def c20012 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20012 : Upper (D 7) (R 7) [34,68,288,17,192,128] 13 := by
  apply FastRouting.sound _ _ [34,68,288,17,192,128] 13 (by decide) (choices 1) [1,2,8] r20012 c20012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5498
  · exact u5499
  · exact u5500

def b20013 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 292 26 145 33 200 200 456), lower := (rows 35 70 292 26 145 33 64 128 256), losses := [] }

theorem u20013 : Upper (D 7) (R 7) [34,68,288,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20014 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 35 70 292 26 145 40 193 193 449), lower := (rows 35 70 292 26 145 40 64 128 256), losses := [] }

theorem u20014 : Upper (D 7) (R 7) [34,68,288,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20014 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20015 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 152, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 292 26 145 96 201 137 393), lower := (rows 35 70 292 26 145 96 64 128 256), losses := [] }

theorem u20015 : Upper (D 7) (R 7) [34,68,288,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20016 : Route 9 := (fun mask => (mask,id))

def c20016 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20016 : Upper (D 7) (R 7) [34,68,288,18,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,288,18,129,128] 13 (by decide) (choices 1) [1,8] r20016 c20016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5501
  · exact u5502

def b20017 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 292 26 152 33 193 193 449), lower := (rows 35 70 292 26 152 33 64 128 256), losses := [] }

theorem u20017 : Upper (D 7) (R 7) [34,68,288,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20018 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 152, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 292 26 152 96 193 129 385), lower := (rows 35 70 292 26 152 96 64 128 256), losses := [] }

theorem u20018 : Upper (D 7) (R 7) [34,68,288,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20019 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 35 70 292 26 152 160 65 193 321), lower := (rows 35 70 292 26 152 160 64 128 256), losses := [] }

theorem u20019 : Upper (D 7) (R 7) [34,68,288,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20020 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 292 73 145 34 216 152 408), lower := (rows 35 70 292 73 145 34 64 128 256), losses := [] }

theorem u20020 : Upper (D 7) (R 7) [34,68,288,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20021 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 292 73 145 40 210 146 402), lower := (rows 35 70 292 73 145 40 64 128 256), losses := [] }

theorem u20021 : Upper (D 7) (R 7) [34,68,288,65,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20021 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20022 : Route 9 := (fun mask => (mask,id))

def c20022 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20022 : Upper (D 7) (R 7) [34,68,288,65,129,16] 13 := by
  apply FastRouting.sound _ _ [34,68,288,65,129,16] 13 (by decide) (choices 1) [2,8,128] r20022 c20022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5503
  · exact u5504
  · exact u5505

def r20023 : Route 9 := (fun mask => (mask,id))

def c20023 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20023 : Upper (D 7) (R 7) [34,68,288,65,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,288,65,129,128] 13 (by decide) (choices 1) [2,8,16] r20023 c20023
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5506
  · exact u5507
  · exact u5508

def b20024 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,5),(3,7),(4,5)], upper := (rows 35 70 292 73 146 33 216 152 408), lower := (rows 35 70 292 73 146 33 64 128 256), losses := [] }

theorem u20024 : Upper (D 7) (R 7) [34,68,288,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20025 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 292 73 146 40 209 145 401), lower := (rows 35 70 292 73 146 40 64 128 256), losses := [] }

theorem u20025 : Upper (D 7) (R 7) [34,68,288,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20025 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20026 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 35 70 292 73 146 48 201 137 393), lower := (rows 35 70 292 73 146 48 64 128 256), losses := [] }

theorem u20026 : Upper (D 7) (R 7) [34,68,288,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20026 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20027 : Route 9 := (fun mask => (mask,id))

def c20027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20027 : Upper (D 7) (R 7) [34,68,288,65,130,128] 13 := by
  apply FastRouting.sound _ _ [34,68,288,65,130,128] 13 (by decide) (choices 1) [1,8,16] r20027 c20027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5509
  · exact u5510
  · exact u5511

def b20028 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,7),(3,5),(3,7),(4,5)], upper := (rows 35 70 292 73 152 33 210 146 402), lower := (rows 35 70 292 73 152 33 64 128 256), losses := [] }

theorem u20028 : Upper (D 7) (R 7) [34,68,288,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20029 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 292 73 152 34 209 145 401), lower := (rows 35 70 292 73 152 34 64 128 256), losses := [] }

theorem u20029 : Upper (D 7) (R 7) [34,68,288,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20030 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 292 73 152 48 195 131 387), lower := (rows 35 70 292 73 152 48 64 128 256), losses := [] }

theorem u20030 : Upper (D 7) (R 7) [34,68,288,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20030 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20031 : Route 9 := (fun mask => (mask,id))

def c20031 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20031 : Upper (D 7) (R 7) [34,68,288,65,136,128] 13 := by
  apply FastRouting.sound _ _ [34,68,288,65,136,128] 13 (by decide) (choices 1) [1,2,16] r20031 c20031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5512
  · exact u5513
  · exact u5514

def b20032 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 292 88 145 33 202 138 394), lower := (rows 35 70 292 88 145 33 64 128 256), losses := [] }

theorem u20032 : Upper (D 7) (R 7) [34,68,288,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20032 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20033 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 292 88 145 34 201 137 393), lower := (rows 35 70 292 88 145 34 64 128 256), losses := [] }

theorem u20033 : Upper (D 7) (R 7) [34,68,288,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20034 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 292 88 145 40 195 131 387), lower := (rows 35 70 292 88 145 40 64 128 256), losses := [] }

theorem u20034 : Upper (D 7) (R 7) [34,68,288,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20034 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20035 : Route 9 := (fun mask => (mask,id))

def c20035 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20035 : Upper (D 7) (R 7) [34,68,288,80,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,288,80,129,128] 13 (by decide) (choices 1) [1,2,8] r20035 c20035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5515
  · exact u5516
  · exact u5517

def b20036 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 292 88 146 33 201 137 393), lower := (rows 35 70 292 88 146 33 64 128 256), losses := [] }

theorem u20036 : Upper (D 7) (R 7) [34,68,288,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20037 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 292 88 146 40 193 129 385), lower := (rows 35 70 292 88 146 40 64 128 256), losses := [] }

theorem u20037 : Upper (D 7) (R 7) [34,68,288,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20037 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20038 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 292 88 146 160 73 137 265), lower := (rows 35 70 292 88 146 160 64 128 256), losses := [{ target := 6, region := (rows 17 2 12 8 16 184 0 136 264), good := (rows 35 6 292 445 179 160 0 160 256) }] }

theorem u20038 : Upper (D 7) (R 7) [34,68,288,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20039 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 292 137 146 33 88 216 344), lower := (rows 35 70 292 137 146 33 64 128 256), losses := [] }

theorem u20039 : Upper (D 7) (R 7) [34,68,288,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u20039
end Delivery.IrregularNine14.P07
