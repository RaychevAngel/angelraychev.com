import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0276
import IrregularNine14P07C0277
import IrregularNine14P07C0278

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33000 : Route 9 := (fun mask => (mask,id))

def c33000 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33000 : Upper (D 7) (R 7) [12,96,3,288,129] 13 := by
  apply FastRouting.sound _ _ [12,96,3,288,129] 13 (by decide) (choices 1) [2,16,64,128] r33000 c33000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16594
  · exact u16595
  · exact u16596
  · exact u16597

def r33001 : Route 9 := (fun mask => (mask,id))

def c33001 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33001 : Upper (D 7) (R 7) [12,96,3,288,130] 13 := by
  apply FastRouting.sound _ _ [12,96,3,288,130] 13 (by decide) (choices 1) [1,16,64,128] r33001 c33001
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16598
  · exact u16599
  · exact u16600
  · exact u16601

def r33002 : Route 9 := (fun mask => (mask,id))

def c33002 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33002 : Upper (D 7) (R 7) [12,96,3,288,192] 13 := by
  apply FastRouting.sound _ _ [12,96,3,288,192] 13 (by decide) (choices 1) [1,2,16,128] r33002 c33002
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16602
  · exact u16603
  · exact u16604
  · exact u16605

def b33003 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 16, targets := 224 },{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 13 98 7 392 19 240 240 240 496), lower := (rows 13 98 7 392 19 32 64 128 256), losses := [] }

theorem u33003 : Upper (D 7) (R 7) [12,96,3,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33004 : Route 9 := (fun mask => (mask,id))

def c33004 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33004 : Upper (D 7) (R 7) [12,96,3,384,33] 13 := by
  apply FastRouting.sound _ _ [12,96,3,384,33] 13 (by decide) (choices 1) [2,16,64,128] r33004 c33004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16606
  · exact u16607
  · exact u16608
  · exact u16609

def b33005 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 98 7 392 50 241 209 209 465), lower := (rows 13 98 7 392 50 32 64 128 256), losses := [] }

theorem u33005 : Upper (D 7) (R 7) [12,96,3,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33006 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 7 392 112 179 211 147 403), lower := (rows 13 98 7 392 112 32 64 128 256), losses := [] }

theorem u33006 : Upper (D 7) (R 7) [12,96,3,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33006 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33007 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 102, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 7 392 145 114 114 242 370), lower := (rows 13 98 7 392 145 32 64 128 256), losses := [] }

theorem u33007 : Upper (D 7) (R 7) [12,96,3,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33008 : Route 9 := (fun mask => (mask,id))

def c33008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33008 : Upper (D 7) (R 7) [12,96,3,384,130] 13 := by
  apply FastRouting.sound _ _ [12,96,3,384,130] 13 (by decide) (choices 1) [1,16,64] r33008 c33008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16610
  · exact u16611
  · exact u16612

def r33009 : Route 9 := (fun mask => (mask,id))

def c33009 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33009 : Upper (D 7) (R 7) [12,96,3,384,160] 13 := by
  apply FastRouting.sound _ _ [12,96,3,384,160] 13 (by decide) (choices 1) [1,2,16,64] r33009 c33009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16613
  · exact u16614
  · exact u16615
  · exact u16616

def b33010 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 29, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 21 41 82 418 450 386 386), lower := (rows 13 98 21 41 82 32 64 128 256), losses := [] }

theorem u33010 : Upper (D 7) (R 7) [12,96,17,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33011 : Route 9 := (fun mask => (mask,id))

def c33011 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u33011 : Upper (D 7) (R 7) [12,96,17,33,130] 13 := by
  apply FastRouting.sound _ _ [12,96,17,33,130] 13 (by decide) (choices 1) [2,64,128,256] r33011 c33011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16617
  · exact u16618
  · exact u16619
  · exact u16620

def r33012 : Route 9 := (fun mask => (mask,id))

def c33012 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33012 : Upper (D 7) (R 7) [12,96,17,33,192] 13 := by
  apply FastRouting.sound _ _ [12,96,17,33,192] 13 (by decide) (choices 1) [2,128,256] r33012 c33012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16621
  · exact u16622
  · exact u16623

def r33013 : Route 9 := (fun mask => (mask,id))

def c33013 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33013 : Upper (D 7) (R 7) [12,96,17,33,258] 13 := by
  apply FastRouting.sound _ _ [12,96,17,33,258] 13 (by decide) (choices 1) [2,64,128] r33013 c33013
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16624
  · exact u16625
  · exact u16626

def r33014 : Route 9 := (fun mask => (mask,id))

def c33014 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33014 : Upper (D 7) (R 7) [12,96,17,33,320] 13 := by
  apply FastRouting.sound _ _ [12,96,17,33,320] 13 (by decide) (choices 1) [2,128] r33014 c33014
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16627
  · exact u16628

def r33015 : Route 9 := (fun mask => (mask,id))

def c33015 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33015 : Upper (D 7) (R 7) [12,96,17,33,384] 13 := by
  apply FastRouting.sound _ _ [12,96,17,33,384] 13 (by decide) (choices 1) [2,64,128] r33015 c33015
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16629
  · exact u16630
  · exact u16631

def b33016 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 0, region := 482, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 98 21 137 50 482 450 450 450), lower := (rows 13 98 21 137 50 32 64 128 256), losses := [] }

theorem u33016 : Upper (D 7) (R 7) [12,96,17,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33017 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 16, targets := 2 },{ cop := 1, region := 16, targets := 128 }], pairs := [(1,0),(4,0),(4,1),(4,7)], upper := (rows 13 98 21 137 112 418 450 386 386), lower := (rows 13 98 21 137 112 32 64 128 256), losses := [] }

theorem u33017 : Upper (D 7) (R 7) [12,96,17,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33018 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 13, targets := 98 }], pairs := [(0,1),(0,5),(0,6),(2,1)], upper := (rows 13 98 21 137 146 354 354 482 354), lower := (rows 13 98 21 137 146 32 64 128 256), losses := [] }

theorem u33018 : Upper (D 7) (R 7) [12,96,17,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33019 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 13, targets := 98 }], pairs := [(0,1),(0,5),(0,6),(2,1)], upper := (rows 13 98 21 137 176 354 322 450 322), lower := (rows 13 98 21 137 176 32 64 128 256), losses := [] }

theorem u33019 : Upper (D 7) (R 7) [12,96,17,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33020 : Route 9 := (fun mask => (mask,id))

def c33020 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33020 : Upper (D 7) (R 7) [12,96,17,129,258] 13 := by
  apply FastRouting.sound _ _ [12,96,17,129,258] 13 (by decide) (choices 1) [2,64,128] r33020 c33020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16632
  · exact u16633
  · exact u16634

def r33021 : Route 9 := (fun mask => (mask,id))

def c33021 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33021 : Upper (D 7) (R 7) [12,96,17,129,288] 13 := by
  apply FastRouting.sound _ _ [12,96,17,129,288] 13 (by decide) (choices 1) [2,64,128] r33021 c33021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16635
  · exact u16636
  · exact u16637

def b33022 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 13, targets := 98 }], pairs := [(0,1),(0,5),(0,6),(2,1)], upper := (rows 13 98 21 137 400 98 98 226 354), lower := (rows 13 98 21 137 400 32 64 128 256), losses := [] }

theorem u33022 : Upper (D 7) (R 7) [12,96,17,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33023 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 21, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 98 21 138 19 480 480 480 480), lower := (rows 13 98 21 138 19 32 64 128 256), losses := [] }

theorem u33023 : Upper (D 7) (R 7) [12,96,17,130,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33024 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 13 98 21 138 49 482 450 450 450), lower := (rows 13 98 21 138 49 32 64 128 256), losses := [] }

theorem u33024 : Upper (D 7) (R 7) [12,96,17,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33025 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 98 21 138 50 481 449 449 449), lower := (rows 13 98 21 138 50 32 64 128 256), losses := [] }

theorem u33025 : Upper (D 7) (R 7) [12,96,17,130,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33026 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 21 138 112 419 451 387 387), lower := (rows 13 98 21 138 112 32 64 128 256), losses := [] }

theorem u33026 : Upper (D 7) (R 7) [12,96,17,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33027 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 21, targets := 98 }], pairs := [(0,1),(0,5),(0,6),(2,1)], upper := (rows 13 98 21 138 145 354 354 482 354), lower := (rows 13 98 21 138 145 32 64 128 256), losses := [] }

theorem u33027 : Upper (D 7) (R 7) [12,96,17,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33028 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 21, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 13 98 21 138 146 353 353 481 353), lower := (rows 13 98 21 138 146 32 64 128 256), losses := [] }

theorem u33028 : Upper (D 7) (R 7) [12,96,17,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33029 : Route 9 := (fun mask => (mask,id))

def c33029 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33029 : Upper (D 7) (R 7) [12,96,17,130,160] 13 := by
  apply FastRouting.sound _ _ [12,96,17,130,160] 13 (by decide) (choices 1) [1,2,64,256] r33029 c33029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16638
  · exact u16639
  · exact u16640
  · exact u16641

def b33030 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 13 98 21 138 273 226 226 226 482), lower := (rows 13 98 21 138 273 32 64 128 256), losses := [] }

theorem u33030 : Upper (D 7) (R 7) [12,96,17,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33031 : Route 9 := (fun mask => (mask,id))

def c33031 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33031 : Upper (D 7) (R 7) [12,96,17,130,258] 13 := by
  apply FastRouting.sound _ _ [12,96,17,130,258] 13 (by decide) (choices 1) [1,64,128] r33031 c33031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16642
  · exact u16643
  · exact u16644

def r33032 : Route 9 := (fun mask => (mask,id))

def c33032 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33032 : Upper (D 7) (R 7) [12,96,17,130,288] 13 := by
  apply FastRouting.sound _ _ [12,96,17,130,288] 13 (by decide) (choices 1) [1,2,64,128] r33032 c33032
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16645
  · exact u16646
  · exact u16647
  · exact u16648

def r33033 : Route 9 := (fun mask => (mask,id))

def c33033 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33033 : Upper (D 7) (R 7) [12,96,17,130,384] 13 := by
  apply FastRouting.sound _ _ [12,96,17,130,384] 13 (by decide) (choices 1) [1,2,64] r33033 c33033
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16649
  · exact u16650
  · exact u16651

def b33034 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 4, targets := 194 },{ cop := 0, region := 482, targets := 1 }], pairs := [(1,0),(2,1),(2,6),(2,7)], upper := (rows 13 98 21 168 19 482 450 450 450), lower := (rows 13 98 21 168 19 32 64 128 256), losses := [] }

theorem u33034 : Upper (D 7) (R 7) [12,96,17,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33035 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 13 98 21 168 81 418 450 386 386), lower := (rows 13 98 21 168 81 32 64 128 256), losses := [] }

theorem u33035 : Upper (D 7) (R 7) [12,96,17,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33036 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 21 168 82 419 451 387 387), lower := (rows 13 98 21 168 82 32 64 128 256), losses := [] }

theorem u33036 : Upper (D 7) (R 7) [12,96,17,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33037 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 21, targets := 98 }], pairs := [(0,1),(0,5),(0,6),(2,1)], upper := (rows 13 98 21 168 145 354 322 450 322), lower := (rows 13 98 21 168 145 32 64 128 256), losses := [] }

theorem u33037 : Upper (D 7) (R 7) [12,96,17,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33037 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33038 : Route 9 := (fun mask => (mask,id))

def c33038 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33038 : Upper (D 7) (R 7) [12,96,17,160,130] 13 := by
  apply FastRouting.sound _ _ [12,96,17,160,130] 13 (by decide) (choices 1) [1,2,64,256] r33038 c33038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16652
  · exact u16653
  · exact u16654
  · exact u16655

def r33039 : Route 9 := (fun mask => (mask,id))

def c33039 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33039 : Upper (D 7) (R 7) [12,96,17,160,192] 13 := by
  apply FastRouting.sound _ _ [12,96,17,160,192] 13 (by decide) (choices 1) [1,2,256] r33039 c33039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16656
  · exact u16657
  · exact u16658

def b33040 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 13 98 21 168 273 226 194 194 450), lower := (rows 13 98 21 168 273 32 64 128 256), losses := [] }

theorem u33040 : Upper (D 7) (R 7) [12,96,17,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33041 : Route 9 := (fun mask => (mask,id))

def c33041 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33041 : Upper (D 7) (R 7) [12,96,17,160,258] 13 := by
  apply FastRouting.sound _ _ [12,96,17,160,258] 13 (by decide) (choices 1) [1,2,64,128] r33041 c33041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16659
  · exact u16660
  · exact u16661
  · exact u16662

def r33042 : Route 9 := (fun mask => (mask,id))

def c33042 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33042 : Upper (D 7) (R 7) [12,96,17,160,320] 13 := by
  apply FastRouting.sound _ _ [12,96,17,160,320] 13 (by decide) (choices 1) [1,2,128] r33042 c33042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16663
  · exact u16664
  · exact u16665

def r33043 : Route 9 := (fun mask => (mask,id))

def c33043 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33043 : Upper (D 7) (R 7) [12,96,17,160,384] 13 := by
  apply FastRouting.sound _ _ [12,96,17,160,384] 13 (by decide) (choices 1) [1,2,64] r33043 c33043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16666
  · exact u16667
  · exact u16668

def b33044 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 0, region := 226, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 98 21 265 50 226 194 194 450), lower := (rows 13 98 21 265 50 32 64 128 256), losses := [] }

theorem u33044 : Upper (D 7) (R 7) [12,96,17,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33045 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 1, region := 16, targets := 2 },{ cop := 1, region := 16, targets := 128 }], pairs := [(1,0),(4,0),(4,1),(4,7)], upper := (rows 13 98 21 265 112 162 194 130 386), lower := (rows 13 98 21 265 112 32 64 128 256), losses := [] }

theorem u33045 : Upper (D 7) (R 7) [12,96,17,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33046 : Route 9 := (fun mask => (mask,id))

def c33046 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33046 : Upper (D 7) (R 7) [12,96,17,257,130] 13 := by
  apply FastRouting.sound _ _ [12,96,17,257,130] 13 (by decide) (choices 1) [2,64,128] r33046 c33046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16669
  · exact u16670
  · exact u16671

def r33047 : Route 9 := (fun mask => (mask,id))

def c33047 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33047 : Upper (D 7) (R 7) [12,96,17,257,160] 13 := by
  apply FastRouting.sound _ _ [12,96,17,257,160] 13 (by decide) (choices 1) [2,64,128] r33047 c33047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16672
  · exact u16673
  · exact u16674

def b33048 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 21, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 98 21 266 19 224 224 224 480), lower := (rows 13 98 21 266 19 32 64 128 256), losses := [] }

theorem u33048 : Upper (D 7) (R 7) [12,96,17,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33049 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 13 98 21 266 49 226 194 194 450), lower := (rows 13 98 21 266 49 32 64 128 256), losses := [] }

theorem u33049 : Upper (D 7) (R 7) [12,96,17,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33050 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 98 21 266 50 225 193 193 449), lower := (rows 13 98 21 266 50 32 64 128 256), losses := [] }

theorem u33050 : Upper (D 7) (R 7) [12,96,17,258,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33051 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 21 266 112 163 195 131 387), lower := (rows 13 98 21 266 112 32 64 128 256), losses := [] }

theorem u33051 : Upper (D 7) (R 7) [12,96,17,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33052 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 13 98 21 266 145 226 226 226 482), lower := (rows 13 98 21 266 145 32 64 128 256), losses := [] }

theorem u33052 : Upper (D 7) (R 7) [12,96,17,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33053 : Route 9 := (fun mask => (mask,id))

def c33053 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33053 : Upper (D 7) (R 7) [12,96,17,258,130] 13 := by
  apply FastRouting.sound _ _ [12,96,17,258,130] 13 (by decide) (choices 1) [1,64,128] r33053 c33053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16675
  · exact u16676
  · exact u16677

def r33054 : Route 9 := (fun mask => (mask,id))

def c33054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33054 : Upper (D 7) (R 7) [12,96,17,258,160] 13 := by
  apply FastRouting.sound _ _ [12,96,17,258,160] 13 (by decide) (choices 1) [1,2,64,128] r33054 c33054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16678
  · exact u16679
  · exact u16680
  · exact u16681

def b33055 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 194 },{ cop := 0, region := 226, targets := 1 }], pairs := [(1,0),(2,1),(2,6),(2,7)], upper := (rows 13 98 21 296 19 226 194 194 450), lower := (rows 13 98 21 296 19 32 64 128 256), losses := [] }

theorem u33055 : Upper (D 7) (R 7) [12,96,17,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33056 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 13 98 21 296 81 162 194 130 386), lower := (rows 13 98 21 296 81 32 64 128 256), losses := [] }

theorem u33056 : Upper (D 7) (R 7) [12,96,17,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33057 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 21 296 82 163 195 131 387), lower := (rows 13 98 21 296 82 32 64 128 256), losses := [] }

theorem u33057 : Upper (D 7) (R 7) [12,96,17,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33058 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 13 98 21 296 145 226 194 194 450), lower := (rows 13 98 21 296 145 32 64 128 256), losses := [] }

theorem u33058 : Upper (D 7) (R 7) [12,96,17,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33059 : Route 9 := (fun mask => (mask,id))

def c33059 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33059 : Upper (D 7) (R 7) [12,96,17,288,130] 13 := by
  apply FastRouting.sound _ _ [12,96,17,288,130] 13 (by decide) (choices 1) [1,2,64,128] r33059 c33059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16682
  · exact u16683
  · exact u16684
  · exact u16685

#print axioms u33059
end Delivery.IrregularNine14.P07
