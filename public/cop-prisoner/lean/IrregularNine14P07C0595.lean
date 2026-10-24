import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0349
import IrregularNine14P07C0350
import IrregularNine14P07C0351

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35700 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 69 76 152 178 242 178 434), lower := (rows 35 259 69 76 152 32 64 128 256), losses := [] }

theorem u35700 : Upper (D 7) (R 7) [34,257,65,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35701 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 69 76 176 186 218 154 410), lower := (rows 35 259 69 76 176 32 64 128 256), losses := [] }

theorem u35701 : Upper (D 7) (R 7) [34,257,65,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35702 : Route 9 := (fun mask => (mask,id))

def c35702 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35702 : Upper (D 7) (R 7) [34,257,65,80,130] 13 := by
  apply FastRouting.sound _ _ [34,257,65,80,130] 13 (by decide) (choices 1) [4,8,128] r35702 c35702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20956
  · exact u20957
  · exact u20958

def r35703 : Route 9 := (fun mask => (mask,id))

def c35703 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35703 : Upper (D 7) (R 7) [34,257,65,80,132] 13 := by
  apply FastRouting.sound _ _ [34,257,65,80,132] 13 (by decide) (choices 1) [2,8,128] r35703 c35703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20959
  · exact u20960
  · exact u20961

def r35704 : Route 9 := (fun mask => (mask,id))

def c35704 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35704 : Upper (D 7) (R 7) [34,257,65,80,136] 13 := by
  apply FastRouting.sound _ _ [34,257,65,80,136] 13 (by decide) (choices 1) [2,4,128] r35704 c35704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20962
  · exact u20963
  · exact u20964

def r35705 : Route 9 := (fun mask => (mask,id))

def c35705 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35705 : Upper (D 7) (R 7) [34,257,65,80,160] 13 := by
  apply FastRouting.sound _ _ [34,257,65,80,160] 13 (by decide) (choices 1) [2,4,8,128] r35705 c35705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20965
  · exact u20966
  · exact u20967
  · exact u20968

def r35706 : Route 9 := (fun mask => (mask,id))

def c35706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35706 : Upper (D 7) (R 7) [34,257,65,96,130] 13 := by
  apply FastRouting.sound _ _ [34,257,65,96,130] 13 (by decide) (choices 1) [4,8,16,128] r35706 c35706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20969
  · exact u20970
  · exact u20971
  · exact u20972

def r35707 : Route 9 := (fun mask => (mask,id))

def c35707 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35707 : Upper (D 7) (R 7) [34,257,65,96,132] 13 := by
  apply FastRouting.sound _ _ [34,257,65,96,132] 13 (by decide) (choices 1) [2,8,16,128] r35707 c35707
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20973
  · exact u20974
  · exact u20975
  · exact u20976

def r35708 : Route 9 := (fun mask => (mask,id))

def c35708 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35708 : Upper (D 7) (R 7) [34,257,65,96,136] 13 := by
  apply FastRouting.sound _ _ [34,257,65,96,136] 13 (by decide) (choices 1) [2,4,16,128] r35708 c35708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20977
  · exact u20978
  · exact u20979
  · exact u20980

def r35709 : Route 9 := (fun mask => (mask,id))

def c35709 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35709 : Upper (D 7) (R 7) [34,257,65,130,132] 13 := by
  apply FastRouting.sound _ _ [34,257,65,130,132] 13 (by decide) (choices 1) [8,16,64] r35709 c35709
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20981
  · exact u20982
  · exact u20983

def b35710 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 259 69 138 152 116 116 244 372), lower := (rows 35 259 69 138 152 32 64 128 256), losses := [] }

theorem u35710 : Upper (D 7) (R 7) [34,257,65,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35711 : Route 9 := (fun mask => (mask,id))

def c35711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35711 : Upper (D 7) (R 7) [34,257,65,130,160] 13 := by
  apply FastRouting.sound _ _ [34,257,65,130,160] 13 (by decide) (choices 1) [4,8,16,64] r35711 c35711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20984
  · exact u20985
  · exact u20986
  · exact u20987

def r35712 : Route 9 := (fun mask => (mask,id))

def c35712 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35712 : Upper (D 7) (R 7) [34,257,65,130,192] 13 := by
  apply FastRouting.sound _ _ [34,257,65,130,192] 13 (by decide) (choices 1) [4,8,16] r35712 c35712
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20988
  · exact u20989
  · exact u20990

def b35713 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 259 69 140 152 114 114 242 370), lower := (rows 35 259 69 140 152 32 64 128 256), losses := [] }

theorem u35713 : Upper (D 7) (R 7) [34,257,65,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35714 : Route 9 := (fun mask => (mask,id))

def c35714 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35714 : Upper (D 7) (R 7) [34,257,65,132,160] 13 := by
  apply FastRouting.sound _ _ [34,257,65,132,160] 13 (by decide) (choices 1) [2,8,16,64] r35714 c35714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20991
  · exact u20992
  · exact u20993
  · exact u20994

def r35715 : Route 9 := (fun mask => (mask,id))

def c35715 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35715 : Upper (D 7) (R 7) [34,257,65,132,192] 13 := by
  apply FastRouting.sound _ _ [34,257,65,132,192] 13 (by decide) (choices 1) [2,8,16] r35715 c35715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20995
  · exact u20996
  · exact u20997

def b35716 : PairBound 9 := { available := 102, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 259 69 152 152 102 102 230 358), lower := (rows 35 259 69 152 152 32 64 128 256), losses := [] }

theorem u35716 : Upper (D 7) (R 7) [34,257,65,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35717 : PairBound 9 := { available := 78, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 259 69 152 176 110 78 206 334), lower := (rows 35 259 69 152 176 32 64 128 256), losses := [] }

theorem u35717 : Upper (D 7) (R 7) [34,257,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35718 : PairBound 9 := { available := 46, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 259 69 152 208 46 110 174 302), lower := (rows 35 259 69 152 208 32 64 128 256), losses := [] }

theorem u35718 : Upper (D 7) (R 7) [34,257,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35719 : Route 9 := (fun mask => (mask,id))

def c35719 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35719 : Upper (D 7) (R 7) [34,257,65,160,192] 13 := by
  apply FastRouting.sound _ _ [34,257,65,160,192] 13 (by decide) (choices 1) [2,4,8,16] r35719 c35719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20998
  · exact u20999
  · exact u21000
  · exact u21001

def b35720 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 70 76 152 177 241 177 433), lower := (rows 35 259 70 76 152 32 64 128 256), losses := [] }

theorem u35720 : Upper (D 7) (R 7) [34,257,66,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35721 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 70 76 176 185 217 153 409), lower := (rows 35 259 70 76 176 32 64 128 256), losses := [] }

theorem u35721 : Upper (D 7) (R 7) [34,257,66,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35722 : Route 9 := (fun mask => (mask,id))

def c35722 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35722 : Upper (D 7) (R 7) [34,257,66,80,132] 13 := by
  apply FastRouting.sound _ _ [34,257,66,80,132] 13 (by decide) (choices 1) [1,8,128] r35722 c35722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21002
  · exact u21003
  · exact u21004

def r35723 : Route 9 := (fun mask => (mask,id))

def c35723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35723 : Upper (D 7) (R 7) [34,257,66,80,136] 13 := by
  apply FastRouting.sound _ _ [34,257,66,80,136] 13 (by decide) (choices 1) [1,4,128] r35723 c35723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21005
  · exact u21006
  · exact u21007

def r35724 : Route 9 := (fun mask => (mask,id))

def c35724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35724 : Upper (D 7) (R 7) [34,257,66,80,160] 13 := by
  apply FastRouting.sound _ _ [34,257,66,80,160] 13 (by decide) (choices 1) [1,4,8,128] r35724 c35724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21008
  · exact u21009
  · exact u21010
  · exact u21011

def r35725 : Route 9 := (fun mask => (mask,id))

def c35725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35725 : Upper (D 7) (R 7) [34,257,66,96,132] 13 := by
  apply FastRouting.sound _ _ [34,257,66,96,132] 13 (by decide) (choices 1) [1,8,16,128] r35725 c35725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21012
  · exact u21013
  · exact u21014
  · exact u21015

def r35726 : Route 9 := (fun mask => (mask,id))

def c35726 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35726 : Upper (D 7) (R 7) [34,257,66,96,136] 13 := by
  apply FastRouting.sound _ _ [34,257,66,96,136] 13 (by decide) (choices 1) [1,4,16,128] r35726 c35726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21016
  · exact u21017
  · exact u21018
  · exact u21019

def b35727 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 35 259 70 140 152 113 113 241 369), lower := (rows 35 259 70 140 152 32 64 128 256), losses := [] }

theorem u35727 : Upper (D 7) (R 7) [34,257,66,132,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35728 : Route 9 := (fun mask => (mask,id))

def c35728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35728 : Upper (D 7) (R 7) [34,257,66,132,160] 13 := by
  apply FastRouting.sound _ _ [34,257,66,132,160] 13 (by decide) (choices 1) [1,8,16,64] r35728 c35728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21020
  · exact u21021
  · exact u21022
  · exact u21023

def r35729 : Route 9 := (fun mask => (mask,id))

def c35729 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35729 : Upper (D 7) (R 7) [34,257,66,132,192] 13 := by
  apply FastRouting.sound _ _ [34,257,66,132,192] 13 (by decide) (choices 1) [1,8,16] r35729 c35729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21024
  · exact u21025
  · exact u21026

def b35730 : PairBound 9 := { available := 101, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 259 70 152 152 101 101 229 357), lower := (rows 35 259 70 152 152 32 64 128 256), losses := [] }

theorem u35730 : Upper (D 7) (R 7) [34,257,66,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35731 : PairBound 9 := { available := 77, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 259 70 152 176 109 77 205 333), lower := (rows 35 259 70 152 176 32 64 128 256), losses := [] }

theorem u35731 : Upper (D 7) (R 7) [34,257,66,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35732 : PairBound 9 := { available := 45, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 35 259 70 152 208 45 109 173 301), lower := (rows 35 259 70 152 208 32 64 128 256), losses := [] }

theorem u35732 : Upper (D 7) (R 7) [34,257,66,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35733 : Route 9 := (fun mask => (mask,id))

def c35733 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35733 : Upper (D 7) (R 7) [34,257,66,160,192] 13 := by
  apply FastRouting.sound _ _ [34,257,66,160,192] 13 (by decide) (choices 1) [1,4,8,16] r35733 c35733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21027
  · exact u21028
  · exact u21029
  · exact u21030

def b35734 : PairBound 9 := { available := 147, camps := [{ cop := 6, region := 12, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 259 76 76 176 179 211 147 403), lower := (rows 35 259 76 76 176 32 64 128 256), losses := [] }

theorem u35734 : Upper (D 7) (R 7) [34,257,72,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35735 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 259 76 88 148 163 227 163 419), lower := (rows 35 259 76 88 148 32 64 128 256), losses := [] }

theorem u35735 : Upper (D 7) (R 7) [34,257,72,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35736 : PairBound 9 := { available := 135, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 259 76 88 176 167 199 135 391), lower := (rows 35 259 76 88 176 32 64 128 256), losses := [] }

theorem u35736 : Upper (D 7) (R 7) [34,257,72,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35737 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 259 76 104 148 179 211 147 403), lower := (rows 35 259 76 104 148 32 64 128 256), losses := [] }

theorem u35737 : Upper (D 7) (R 7) [34,257,72,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35738 : Route 9 := (fun mask => (mask,id))

def c35738 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35738 : Upper (D 7) (R 7) [34,257,72,132,96] 13 := by
  apply FastRouting.sound _ _ [34,257,72,132,96] 13 (by decide) (choices 1) [1,2,16,128] r35738 c35738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21031
  · exact u21032
  · exact u21033
  · exact u21034

def b35739 : PairBound 9 := { available := 51, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5),(3,0)], upper := (rows 35 259 76 140 208 51 115 179 307), lower := (rows 35 259 76 140 208 32 64 128 256), losses := [] }

theorem u35739 : Upper (D 7) (R 7) [34,257,72,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35740 : Route 9 := (fun mask => (mask,id))

def c35740 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35740 : Upper (D 7) (R 7) [34,257,72,144,96] 13 := by
  apply FastRouting.sound _ _ [34,257,72,144,96] 13 (by decide) (choices 1) [1,2,4,128] r35740 c35740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21035
  · exact u21036
  · exact u21037
  · exact u21038

def b35741 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5),(3,0)], upper := (rows 35 259 76 152 208 39 103 167 295), lower := (rows 35 259 76 152 208 32 64 128 256), losses := [] }

theorem u35741 : Upper (D 7) (R 7) [34,257,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35742 : Route 9 := (fun mask => (mask,id))

def c35742 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35742 : Upper (D 7) (R 7) [34,257,72,160,192] 13 := by
  apply FastRouting.sound _ _ [34,257,72,160,192] 13 (by decide) (choices 1) [1,2,4,16] r35742 c35742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21039
  · exact u21040
  · exact u21041
  · exact u21042

def b35743 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 4, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 35 259 76 200 176 55 87 151 279), lower := (rows 35 259 76 200 176 32 64 128 256), losses := [] }

theorem u35743 : Upper (D 7) (R 7) [34,257,72,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35744 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 262 13 26 49 224 192 192 448), lower := (rows 35 262 13 26 49 32 64 128 256), losses := [] }

theorem u35744 : Upper (D 7) (R 7) [34,260,9,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35745 : Route 9 := (fun mask => (mask,id))

def c35745 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35745 : Upper (D 7) (R 7) [34,260,9,18,65] 13 := by
  apply FastRouting.sound _ _ [34,260,9,18,65] 13 (by decide) (choices 1) [64,128] r35745 c35745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21043
  · exact u21044

def r35746 : Route 9 := (fun mask => (mask,id))

def c35746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35746 : Upper (D 7) (R 7) [34,260,9,18,96] 13 := by
  apply FastRouting.sound _ _ [34,260,9,18,96] 13 (by decide) (choices 1) [1,64,128] r35746 c35746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21045
  · exact u21046
  · exact u21047

def r35747 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35747 : Upper (D 7) (R 7) [34,260,9,18,192] 13 := by
  apply FastRouting.sound _ _ [34,260,9,18,192] 13 (by decide) (choices 1) [1,64] r35747 c35747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21048
  · exact u21049

def b35748 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 262 13 56 19 224 192 192 448), lower := (rows 35 262 13 56 19 32 64 128 256), losses := [] }

theorem u35748 : Upper (D 7) (R 7) [34,260,9,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35749 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(3,0),(4,5)], upper := (rows 35 262 13 56 81 226 194 194 450), lower := (rows 35 262 13 56 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 39 71 135 263), good := (rows 482 486 494 56 504 32 64 128 256) }] }

theorem u35749 : Upper (D 7) (R 7) [34,260,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35750 : Route 9 := (fun mask => (mask,id))

def c35750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35750 : Upper (D 7) (R 7) [34,260,9,48,66] 13 := by
  apply FastRouting.sound _ _ [34,260,9,48,66] 13 (by decide) (choices 1) [1,64,128] r35750 c35750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21050
  · exact u21051
  · exact u21052

def r35751 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35751 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35751 : Upper (D 7) (R 7) [34,260,9,48,192] 13 := by
  apply FastRouting.sound _ _ [34,260,9,48,192] 13 (by decide) (choices 1) [1,2,64] r35751 c35751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21053
  · exact u21054
  · exact u21055

def b35752 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 32 },{ cop := 0, region := 16, targets := 64 }], pairs := [(1,5),(2,5),(3,5),(4,6)], upper := (rows 35 262 13 74 49 240 208 208 464), lower := (rows 35 262 13 74 49 32 64 128 256), losses := [] }

theorem u35752 : Upper (D 7) (R 7) [34,260,9,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35753 : Route 9 := (fun mask => (mask,id))

def c35753 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35753 : Upper (D 7) (R 7) [34,260,9,66,65] 13 := by
  apply FastRouting.sound _ _ [34,260,9,66,65] 13 (by decide) (choices 1) [16,128] r35753 c35753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21056
  · exact u21057

def r35754 : Route 9 := (fun mask => (mask,id))

def c35754 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35754 : Upper (D 7) (R 7) [34,260,9,66,96] 13 := by
  apply FastRouting.sound _ _ [34,260,9,66,96] 13 (by decide) (choices 1) [1,16,128] r35754 c35754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21058
  · exact u21059
  · exact u21060

def r35755 : Route 9 := (fun mask => (mask,id))

def c35755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35755 : Upper (D 7) (R 7) [34,260,9,66,129] 13 := by
  apply FastRouting.sound _ _ [34,260,9,66,129] 13 (by decide) (choices 1) [16,64,128] r35755 c35755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21061
  · exact u21062
  · exact u21063

def r35756 : Route 9 := (fun mask => (mask,id))

def c35756 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35756 : Upper (D 7) (R 7) [34,260,9,66,160] 13 := by
  apply FastRouting.sound _ _ [34,260,9,66,160] 13 (by decide) (choices 1) [1,16,64,128] r35756 c35756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21064
  · exact u21065
  · exact u21066
  · exact u21067

def r35757 : Route 9 := (fun mask => (mask,id))

def c35757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35757 : Upper (D 7) (R 7) [34,260,9,66,192] 13 := by
  apply FastRouting.sound _ _ [34,260,9,66,192] 13 (by decide) (choices 1) [1,16,128] r35757 c35757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21068
  · exact u21069
  · exact u21070

def b35758 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 224 },{ cop := 4, region := 236, targets := 2 }], pairs := [(2,1),(4,5),(4,6),(4,7)], upper := (rows 35 262 13 88 19 224 224 224 480), lower := (rows 35 262 13 88 19 32 64 128 256), losses := [] }

theorem u35758 : Upper (D 7) (R 7) [34,260,9,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35759 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 35 262 13 88 49 226 194 194 450), lower := (rows 35 262 13 88 49 32 64 128 256), losses := [] }

theorem u35759 : Upper (D 7) (R 7) [34,260,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u35759
end Delivery.IrregularNine14.P07
