import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0081
import IrregularNine14P08C0082
import IrregularNine14P08C0083

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r14580 : Route 9 := (fun mask => (mask,id))

def c14580 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14580 : Upper (D 8) (R 8) [96,36,72,160,384] 13 := by
  apply FastRouting.sound _ _ [96,36,72,160,384] 13 (by decide) (choices 1) [1,2,16] r14580 c14580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4903
  · exact u4904
  · exact u4905

def r14581 : Route 9 := (fun mask => (mask,id))

def c14581 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14581 : Upper (D 8) (R 8) [96,36,72,257,129] 13 := by
  apply FastRouting.sound _ _ [96,36,72,257,129] 13 (by decide) (choices 1) [2,16,128] r14581 c14581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4906
  · exact u4907
  · exact u4908

def r14582 : Route 9 := (fun mask => (mask,id))

def c14582 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14582 : Upper (D 8) (R 8) [96,36,72,257,130] 13 := by
  apply FastRouting.sound _ _ [96,36,72,257,130] 13 (by decide) (choices 1) [1,16,128] r14582 c14582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4909
  · exact u4910
  · exact u4911

def r14583 : Route 9 := (fun mask => (mask,id))

def c14583 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14583 : Upper (D 8) (R 8) [96,36,72,257,160] 13 := by
  apply FastRouting.sound _ _ [96,36,72,257,160] 13 (by decide) (choices 1) [1,2,16,128] r14583 c14583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4912
  · exact u4913
  · exact u4914
  · exact u4915

def b14584 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 38 76 266 145 177 241 177 433), lower := (rows 97 38 76 266 145 32 64 128 256), losses := [] }

theorem u14584 : Upper (D 8) (R 8) [96,36,72,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14584 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14585 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 38 76 266 176 177 209 145 401), lower := (rows 97 38 76 266 176 32 64 128 256), losses := [] }

theorem u14585 : Upper (D 8) (R 8) [96,36,72,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14585 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14586 : Route 9 := (fun mask => (mask,id))

def c14586 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14586 : Upper (D 8) (R 8) [96,36,72,272,129] 13 := by
  apply FastRouting.sound _ _ [96,36,72,272,129] 13 (by decide) (choices 1) [1,2,128] r14586 c14586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4916
  · exact u4917
  · exact u4918

def r14587 : Route 9 := (fun mask => (mask,id))

def c14587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14587 : Upper (D 8) (R 8) [96,36,72,272,130] 13 := by
  apply FastRouting.sound _ _ [96,36,72,272,130] 13 (by decide) (choices 1) [1,128] r14587 c14587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4919
  · exact u4920

def r14588 : Route 9 := (fun mask => (mask,id))

def c14588 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14588 : Upper (D 8) (R 8) [96,36,72,272,160] 13 := by
  apply FastRouting.sound _ _ [96,36,72,272,160] 13 (by decide) (choices 1) [1,2,128] r14588 c14588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4921
  · exact u4922
  · exact u4923

def r14589 : Route 9 := (fun mask => (mask,id))

def c14589 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14589 : Upper (D 8) (R 8) [96,36,72,288,129] 13 := by
  apply FastRouting.sound _ _ [96,36,72,288,129] 13 (by decide) (choices 1) [1,2,16,128] r14589 c14589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4924
  · exact u4925
  · exact u4926
  · exact u4927

def r14590 : Route 9 := (fun mask => (mask,id))

def c14590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14590 : Upper (D 8) (R 8) [96,36,72,288,130] 13 := by
  apply FastRouting.sound _ _ [96,36,72,288,130] 13 (by decide) (choices 1) [1,16,128] r14590 c14590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4928
  · exact u4929
  · exact u4930

def r14591 : Route 9 := (fun mask => (mask,id))

def c14591 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14591 : Upper (D 8) (R 8) [96,36,72,384,129] 13 := by
  apply FastRouting.sound _ _ [96,36,72,384,129] 13 (by decide) (choices 1) [1,2,16] r14591 c14591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4931
  · exact u4932
  · exact u4933

def b14592 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 76 392 146 49 113 177 305), lower := (rows 97 38 76 392 146 32 64 128 256), losses := [] }

theorem u14592 : Upper (D 8) (R 8) [96,36,72,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14592 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14593 : Route 9 := (fun mask => (mask,id))

def c14593 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14593 : Upper (D 8) (R 8) [96,36,72,384,160] 13 := by
  apply FastRouting.sound _ _ [96,36,72,384,160] 13 (by decide) (choices 1) [1,2,16] r14593 c14593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4934
  · exact u4935
  · exact u4936

def b14594 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 100 137 146 313 345 409 281), lower := (rows 97 38 100 137 146 32 64 128 256), losses := [] }

theorem u14594 : Upper (D 8) (R 8) [96,36,96,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14594 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14595 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 100 137 273 186 218 154 410), lower := (rows 97 38 100 137 273 32 64 128 256), losses := [] }

theorem u14595 : Upper (D 8) (R 8) [96,36,96,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14595 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14596 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 100 137 274 185 217 153 409), lower := (rows 97 38 100 137 274 32 64 128 256), losses := [] }

theorem u14596 : Upper (D 8) (R 8) [96,36,96,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14596 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14597 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 100 137 280 179 211 147 403), lower := (rows 97 38 100 137 280 32 64 128 256), losses := [] }

theorem u14597 : Upper (D 8) (R 8) [96,36,96,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14597 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14598 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 100 137 400 59 91 155 283), lower := (rows 97 38 100 137 400 32 64 128 256), losses := [] }

theorem u14598 : Upper (D 8) (R 8) [96,36,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14598 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14599 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 100 138 273 185 217 153 409), lower := (rows 97 38 100 138 273 32 64 128 256), losses := [] }

theorem u14599 : Upper (D 8) (R 8) [96,36,96,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14599 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14600 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 100 138 280 177 209 145 401), lower := (rows 97 38 100 138 280 32 64 128 256), losses := [] }

theorem u14600 : Upper (D 8) (R 8) [96,36,96,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14601 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 100 138 400 57 89 153 281), lower := (rows 97 38 100 138 400 32 64 128 256), losses := [] }

theorem u14601 : Upper (D 8) (R 8) [96,36,96,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14601 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14602 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 100 152 273 171 203 139 395), lower := (rows 97 38 100 152 273 32 64 128 256), losses := [] }

theorem u14602 : Upper (D 8) (R 8) [96,36,96,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14602 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14603 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 100 152 274 169 201 137 393), lower := (rows 97 38 100 152 274 32 64 128 256), losses := [] }

theorem u14603 : Upper (D 8) (R 8) [96,36,96,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14603 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14604 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 100 152 280 163 195 131 387), lower := (rows 97 38 100 152 280 32 64 128 256), losses := [] }

theorem u14604 : Upper (D 8) (R 8) [96,36,96,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14604 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14605 : PairBound 9 := { available := 330, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 133 56 145 362 330 458 330), lower := (rows 97 38 133 56 145 32 64 128 256), losses := [] }

theorem u14605 : Upper (D 8) (R 8) [96,36,129,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14605 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14606 : PairBound 9 := { available := 329, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 56 146 361 329 457 329), lower := (rows 97 38 133 56 146 32 64 128 256), losses := [] }

theorem u14606 : Upper (D 8) (R 8) [96,36,129,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14607 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 56 152 355 323 451 323), lower := (rows 97 38 133 56 152 32 64 128 256), losses := [] }

theorem u14607 : Upper (D 8) (R 8) [96,36,129,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14607 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14608 : Route 9 := (fun mask => (mask,id))

def c14608 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u14608 : Upper (D 8) (R 8) [96,36,129,48,192] 13 := by
  apply FastRouting.sound _ _ [96,36,129,48,192] 13 (by decide) (choices 1) [1,2,8,256] r14608 c14608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4937
  · exact u4938
  · exact u4939
  · exact u4940

def r14609 : Route 9 := (fun mask => (mask,id))

def c14609 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14609 : Upper (D 8) (R 8) [96,36,129,48,257] 13 := by
  apply FastRouting.sound _ _ [96,36,129,48,257] 13 (by decide) (choices 1) [2,8,64,128] r14609 c14609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4941
  · exact u4942
  · exact u4943
  · exact u4944

def r14610 : Route 9 := (fun mask => (mask,id))

def c14610 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14610 : Upper (D 8) (R 8) [96,36,129,48,258] 13 := by
  apply FastRouting.sound _ _ [96,36,129,48,258] 13 (by decide) (choices 1) [1,8,64,128] r14610 c14610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4945
  · exact u4946
  · exact u4947
  · exact u4948

def r14611 : Route 9 := (fun mask => (mask,id))

def c14611 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14611 : Upper (D 8) (R 8) [96,36,129,48,264] 13 := by
  apply FastRouting.sound _ _ [96,36,129,48,264] 13 (by decide) (choices 1) [1,2,64,128] r14611 c14611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4949
  · exact u4950
  · exact u4951
  · exact u4952

def r14612 : Route 9 := (fun mask => (mask,id))

def c14612 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14612 : Upper (D 8) (R 8) [96,36,129,48,320] 13 := by
  apply FastRouting.sound _ _ [96,36,129,48,320] 13 (by decide) (choices 1) [1,2,8,128] r14612 c14612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4953
  · exact u4954
  · exact u4955
  · exact u4956

def r14613 : Route 9 := (fun mask => (mask,id))

def c14613 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14613 : Upper (D 8) (R 8) [96,36,129,48,384] 13 := by
  apply FastRouting.sound _ _ [96,36,129,48,384] 13 (by decide) (choices 1) [1,2,8,64] r14613 c14613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4957
  · exact u4958
  · exact u4959
  · exact u4960

def b14614 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 73 152 306 370 434 306), lower := (rows 97 38 133 73 152 32 64 128 256), losses := [] }

theorem u14614 : Upper (D 8) (R 8) [96,36,129,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14615 : PairBound 9 := { available := 282, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 73 176 314 346 410 282), lower := (rows 97 38 133 73 176 32 64 128 256), losses := [] }

theorem u14615 : Upper (D 8) (R 8) [96,36,129,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14615 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14616 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 73 274 184 248 184 440), lower := (rows 97 38 133 73 274 32 64 128 256), losses := [] }

theorem u14616 : Upper (D 8) (R 8) [96,36,129,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14616 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14617 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 73 280 178 242 178 434), lower := (rows 97 38 133 73 280 32 64 128 256), losses := [] }

theorem u14617 : Upper (D 8) (R 8) [96,36,129,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14617 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14618 : PairBound 9 := { available := 154, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 73 304 186 218 154 410), lower := (rows 97 38 133 73 304 32 64 128 256), losses := [] }

theorem u14618 : Upper (D 8) (R 8) [96,36,129,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14619 : PairBound 9 := { available := 58, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 73 400 58 122 186 314), lower := (rows 97 38 133 73 400 32 64 128 256), losses := [] }

theorem u14619 : Upper (D 8) (R 8) [96,36,129,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14619 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14620 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 133 74 145 312 376 440 312), lower := (rows 97 38 133 74 145 32 64 128 256), losses := [] }

theorem u14620 : Upper (D 8) (R 8) [96,36,129,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14620 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14621 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 74 152 305 369 433 305), lower := (rows 97 38 133 74 152 32 64 128 256), losses := [] }

theorem u14621 : Upper (D 8) (R 8) [96,36,129,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14621 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14622 : Route 9 := (fun mask => (mask,id))

def c14622 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u14622 : Upper (D 8) (R 8) [96,36,129,66,160] 13 := by
  apply FastRouting.sound _ _ [96,36,129,66,160] 13 (by decide) (choices 1) [1,8,16,256] r14622 c14622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4961
  · exact u4962
  · exact u4963
  · exact u4964

def r14623 : Route 9 := (fun mask => (mask,id))

def c14623 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14623 : Upper (D 8) (R 8) [96,36,129,66,257] 13 := by
  apply FastRouting.sound _ _ [96,36,129,66,257] 13 (by decide) (choices 1) [8,16,128] r14623 c14623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4965
  · exact u4966
  · exact u4967

def r14624 : Route 9 := (fun mask => (mask,id))

def c14624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14624 : Upper (D 8) (R 8) [96,36,129,66,264] 13 := by
  apply FastRouting.sound _ _ [96,36,129,66,264] 13 (by decide) (choices 1) [1,16,128] r14624 c14624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4968
  · exact u4969
  · exact u4970

def r14625 : Route 9 := (fun mask => (mask,id))

def c14625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14625 : Upper (D 8) (R 8) [96,36,129,66,288] 13 := by
  apply FastRouting.sound _ _ [96,36,129,66,288] 13 (by decide) (choices 1) [1,8,16,128] r14625 c14625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4971
  · exact u4972
  · exact u4973
  · exact u4974

def r14626 : Route 9 := (fun mask => (mask,id))

def c14626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14626 : Upper (D 8) (R 8) [96,36,129,66,384] 13 := by
  apply FastRouting.sound _ _ [96,36,129,66,384] 13 (by decide) (choices 1) [1,8,16] r14626 c14626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4975
  · exact u4976
  · exact u4977

def b14627 : PairBound 9 := { available := 298, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 38 133 88 145 298 362 426 298), lower := (rows 97 38 133 88 145 32 64 128 256), losses := [] }

theorem u14627 : Upper (D 8) (R 8) [96,36,129,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14628 : PairBound 9 := { available := 297, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 133 88 146 297 361 425 297), lower := (rows 97 38 133 88 146 32 64 128 256), losses := [] }

theorem u14628 : Upper (D 8) (R 8) [96,36,129,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14628 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14629 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 88 152 291 355 419 291), lower := (rows 97 38 133 88 152 32 64 128 256), losses := [] }

theorem u14629 : Upper (D 8) (R 8) [96,36,129,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14630 : Route 9 := (fun mask => (mask,id))

def c14630 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u14630 : Upper (D 8) (R 8) [96,36,129,80,160] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,160] 13 (by decide) (choices 1) [1,2,8,256] r14630 c14630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4978
  · exact u4979
  · exact u4980
  · exact u4981

def r14631 : Route 9 := (fun mask => (mask,id))

def c14631 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14631 : Upper (D 8) (R 8) [96,36,129,80,257] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,257] 13 (by decide) (choices 1) [2,8,128] r14631 c14631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4982
  · exact u4983
  · exact u4984

def r14632 : Route 9 := (fun mask => (mask,id))

def c14632 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14632 : Upper (D 8) (R 8) [96,36,129,80,258] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,258] 13 (by decide) (choices 1) [1,8,128] r14632 c14632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4985
  · exact u4986
  · exact u4987

def b14633 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 88 280 163 227 163 419), lower := (rows 97 38 133 88 280 32 64 128 256), losses := [] }

theorem u14633 : Upper (D 8) (R 8) [96,36,129,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14633 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14634 : Route 9 := (fun mask => (mask,id))

def c14634 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14634 : Upper (D 8) (R 8) [96,36,129,80,288] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,288] 13 (by decide) (choices 1) [1,2,8,128] r14634 c14634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4988
  · exact u4989
  · exact u4990
  · exact u4991

def r14635 : Route 9 := (fun mask => (mask,id))

def c14635 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14635 : Upper (D 8) (R 8) [96,36,129,80,384] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80,384] 13 (by decide) (choices 1) [1,2,8] r14635 c14635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4992
  · exact u4993
  · exact u4994

def b14636 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 104 152 307 339 403 275), lower := (rows 97 38 133 104 152 32 64 128 256), losses := [] }

theorem u14636 : Upper (D 8) (R 8) [96,36,129,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14636 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14637 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 104 273 186 218 154 410), lower := (rows 97 38 133 104 273 32 64 128 256), losses := [] }

theorem u14637 : Upper (D 8) (R 8) [96,36,129,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14638 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 104 274 185 217 153 409), lower := (rows 97 38 133 104 274 32 64 128 256), losses := [] }

theorem u14638 : Upper (D 8) (R 8) [96,36,129,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14639 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 38 133 104 280 179 211 147 403), lower := (rows 97 38 133 104 280 32 64 128 256), losses := [] }

theorem u14639 : Upper (D 8) (R 8) [96,36,129,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14639 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u14639
end Delivery.IrregularNine14.P08
