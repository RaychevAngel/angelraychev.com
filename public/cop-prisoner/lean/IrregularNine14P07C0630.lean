import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0411
import IrregularNine14P07C0412
import IrregularNine14P07C0413

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37800 : Route 9 := (fun mask => (mask,id))

def c37800 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37800 : Upper (D 7) (R 7) [36,96,264,192,129] 13 := by
  apply FastRouting.sound _ _ [36,96,264,192,129] 13 (by decide) (choices 1) [1,2,16] r37800 c37800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24703
  · exact u24704
  · exact u24705

def r37801 : Route 9 := (fun mask => (mask,id))

def c37801 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37801 : Upper (D 7) (R 7) [36,96,264,192,130] 13 := by
  apply FastRouting.sound _ _ [36,96,264,192,130] 13 (by decide) (choices 1) [1,2,16] r37801 c37801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24706
  · exact u24707
  · exact u24708

def b37802 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 16, targets := 64 },{ cop := 3, region := 16, targets := 128 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 37 98 324 11 19 184 216 152 408), lower := (rows 37 98 324 11 19 32 64 128 256), losses := [] }

theorem u37802 : Upper (D 7) (R 7) [36,96,320,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37803 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 16, targets := 130 },{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5),(4,1),(4,5),(4,7)], upper := (rows 37 98 324 11 25 178 210 146 402), lower := (rows 37 98 324 11 25 32 64 128 256), losses := [] }

theorem u37803 : Upper (D 7) (R 7) [36,96,320,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37804 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 16, targets := 129 },{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5),(4,0),(4,5),(4,7)], upper := (rows 37 98 324 11 26 177 209 145 401), lower := (rows 37 98 324 11 26 32 64 128 256), losses := [] }

theorem u37804 : Upper (D 7) (R 7) [36,96,320,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37805 : Route 9 := (fun mask => (mask,id))

def c37805 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37805 : Upper (D 7) (R 7) [36,96,320,3,129] 13 := by
  apply FastRouting.sound _ _ [36,96,320,3,129] 13 (by decide) (choices 1) [2,8,16,128] r37805 c37805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24709
  · exact u24710
  · exact u24711
  · exact u24712

def r37806 : Route 9 := (fun mask => (mask,id))

def c37806 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37806 : Upper (D 7) (R 7) [36,96,320,3,130] 13 := by
  apply FastRouting.sound _ _ [36,96,320,3,130] 13 (by decide) (choices 1) [1,8,16,128] r37806 c37806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24713
  · exact u24714
  · exact u24715
  · exact u24716

def r37807 : Route 9 := (fun mask => (mask,id))

def c37807 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37807 : Upper (D 7) (R 7) [36,96,320,3,136] 13 := by
  apply FastRouting.sound _ _ [36,96,320,3,136] 13 (by decide) (choices 1) [1,2,16,128] r37807 c37807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24717
  · exact u24718
  · exact u24719
  · exact u24720

def b37808 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 324 25 25 162 194 130 386), lower := (rows 37 98 324 25 25 32 64 128 256), losses := [] }

theorem u37808 : Upper (D 7) (R 7) [36,96,320,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37809 : Route 9 := (fun mask => (mask,id))

def c37809 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37809 : Upper (D 7) (R 7) [36,96,320,17,10] 13 := by
  apply FastRouting.sound _ _ [36,96,320,17,10] 13 (by decide) (choices 1) [1,2,128] r37809 c37809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24721
  · exact u24722
  · exact u24723

def b37810 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 324 25 145 170 202 138 394), lower := (rows 37 98 324 25 145 32 64 128 256), losses := [] }

theorem u37810 : Upper (D 7) (R 7) [36,96,320,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37811 : Route 9 := (fun mask => (mask,id))

def c37811 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37811 : Upper (D 7) (R 7) [36,96,320,17,130] 13 := by
  apply FastRouting.sound _ _ [36,96,320,17,130] 13 (by decide) (choices 1) [1,2,8,128] r37811 c37811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24724
  · exact u24725
  · exact u24726
  · exact u24727

def r37812 : Route 9 := (fun mask => (mask,id))

def c37812 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37812 : Upper (D 7) (R 7) [36,96,320,17,136] 13 := by
  apply FastRouting.sound _ _ [36,96,320,17,136] 13 (by decide) (choices 1) [1,2,128] r37812 c37812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24728
  · exact u24729
  · exact u24730

def b37813 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 324 26 26 161 193 129 385), lower := (rows 37 98 324 26 26 32 64 128 256), losses := [] }

theorem u37813 : Upper (D 7) (R 7) [36,96,320,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37814 : Route 9 := (fun mask => (mask,id))

def c37814 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37814 : Upper (D 7) (R 7) [36,96,320,18,129] 13 := by
  apply FastRouting.sound _ _ [36,96,320,18,129] 13 (by decide) (choices 1) [1,2,8,128] r37814 c37814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24731
  · exact u24732
  · exact u24733
  · exact u24734

def b37815 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 324 26 146 169 201 137 393), lower := (rows 37 98 324 26 146 32 64 128 256), losses := [] }

theorem u37815 : Upper (D 7) (R 7) [36,96,320,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37816 : Route 9 := (fun mask => (mask,id))

def c37816 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37816 : Upper (D 7) (R 7) [36,96,320,18,136] 13 := by
  apply FastRouting.sound _ _ [36,96,320,18,136] 13 (by decide) (choices 1) [1,2,128] r37816 c37816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24735
  · exact u24736
  · exact u24737

def b37817 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 37 98 324 137 145 58 90 154 282), lower := (rows 37 98 324 137 145 32 64 128 256), losses := [] }

theorem u37817 : Upper (D 7) (R 7) [36,96,320,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37818 : Route 9 := (fun mask => (mask,id))

def c37818 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37818 : Upper (D 7) (R 7) [36,96,320,129,130] 13 := by
  apply FastRouting.sound _ _ [36,96,320,129,130] 13 (by decide) (choices 1) [1,2,8,16] r37818 c37818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24738
  · exact u24739
  · exact u24740
  · exact u24741

def b37819 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 37 98 324 137 152 51 83 147 275), lower := (rows 37 98 324 137 152 32 64 128 256), losses := [] }

theorem u37819 : Upper (D 7) (R 7) [36,96,320,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37820 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 98 324 138 146 57 89 153 281), lower := (rows 37 98 324 138 146 32 64 128 256), losses := [] }

theorem u37820 : Upper (D 7) (R 7) [36,96,320,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37821 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 37 98 324 138 152 51 83 147 275), lower := (rows 37 98 324 138 152 32 64 128 256), losses := [] }

theorem u37821 : Upper (D 7) (R 7) [36,96,320,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37822 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 324 152 152 35 67 131 259), lower := (rows 37 98 324 152 152 32 64 128 256), losses := [] }

theorem u37822 : Upper (D 7) (R 7) [36,96,320,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37823 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 16, targets := 192 }], pairs := [(2,5),(4,5),(4,6),(4,7)], upper := (rows 37 98 388 11 19 248 216 216 472), lower := (rows 37 98 388 11 19 32 64 128 256), losses := [] }

theorem u37823 : Upper (D 7) (R 7) [36,96,384,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37824 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 16, targets := 194 },{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5),(4,1),(4,6),(4,7)], upper := (rows 37 98 388 11 25 242 210 210 466), lower := (rows 37 98 388 11 25 32 64 128 256), losses := [] }

theorem u37824 : Upper (D 7) (R 7) [36,96,384,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37825 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 193 },{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5),(4,0),(4,6),(4,7)], upper := (rows 37 98 388 11 26 241 209 209 465), lower := (rows 37 98 388 11 26 32 64 128 256), losses := [] }

theorem u37825 : Upper (D 7) (R 7) [36,96,384,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37826 : Route 9 := (fun mask => (mask,id))

def c37826 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37826 : Upper (D 7) (R 7) [36,96,384,3,65] 13 := by
  apply FastRouting.sound _ _ [36,96,384,3,65] 13 (by decide) (choices 1) [2,8,16,128] r37826 c37826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24742
  · exact u24743
  · exact u24744
  · exact u24745

def b37827 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 388 11 82 185 217 153 409), lower := (rows 37 98 388 11 82 32 64 128 256), losses := [] }

theorem u37827 : Upper (D 7) (R 7) [36,96,384,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37828 : Route 9 := (fun mask => (mask,id))

def c37828 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37828 : Upper (D 7) (R 7) [36,96,384,3,72] 13 := by
  apply FastRouting.sound _ _ [36,96,384,3,72] 13 (by decide) (choices 1) [1,2,16,128] r37828 c37828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24746
  · exact u24747
  · exact u24748
  · exact u24749

def b37829 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7),(2,5),(3,7),(4,5)], upper := (rows 37 98 388 11 145 122 90 218 346), lower := (rows 37 98 388 11 145 32 64 128 256), losses := [] }

theorem u37829 : Upper (D 7) (R 7) [36,96,384,3,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37830 : Route 9 := (fun mask => (mask,id))

def c37830 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37830 : Upper (D 7) (R 7) [36,96,384,3,130] 13 := by
  apply FastRouting.sound _ _ [36,96,384,3,130] 13 (by decide) (choices 1) [1,8,16,64] r37830 c37830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24750
  · exact u24751
  · exact u24752
  · exact u24753

def r37831 : Route 9 := (fun mask => (mask,id))

def c37831 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37831 : Upper (D 7) (R 7) [36,96,384,3,136] 13 := by
  apply FastRouting.sound _ _ [36,96,384,3,136] 13 (by decide) (choices 1) [1,2,16,64] r37831 c37831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24754
  · exact u24755
  · exact u24756
  · exact u24757

def r37832 : Route 9 := (fun mask => (mask,id))

def c37832 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37832 : Upper (D 7) (R 7) [36,96,384,3,192] 13 := by
  apply FastRouting.sound _ _ [36,96,384,3,192] 13 (by decide) (choices 1) [1,2,8,16] r37832 c37832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24758
  · exact u24759
  · exact u24760
  · exact u24761

def b37833 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 388 25 25 226 194 194 450), lower := (rows 37 98 388 25 25 32 64 128 256), losses := [] }

theorem u37833 : Upper (D 7) (R 7) [36,96,384,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37834 : Route 9 := (fun mask => (mask,id))

def c37834 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u37834 : Upper (D 7) (R 7) [36,96,384,17,10] 13 := by
  apply FastRouting.sound _ _ [36,96,384,17,10] 13 (by decide) (choices 1) [1,2,64,128] r37834 c37834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24762
  · exact u24763
  · exact u24764
  · exact u24765

def b37835 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 98 388 25 81 170 202 138 394), lower := (rows 37 98 388 25 81 32 64 128 256), losses := [] }

theorem u37835 : Upper (D 7) (R 7) [36,96,384,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37836 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 98 388 25 82 171 203 139 395), lower := (rows 37 98 388 25 82 32 64 128 256), losses := [] }

theorem u37836 : Upper (D 7) (R 7) [36,96,384,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37837 : Route 9 := (fun mask => (mask,id))

def c37837 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37837 : Upper (D 7) (R 7) [36,96,384,17,72] 13 := by
  apply FastRouting.sound _ _ [36,96,384,17,72] 13 (by decide) (choices 1) [1,2,128] r37837 c37837
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24766
  · exact u24767
  · exact u24768

def b37838 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 8, targets := 98 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,6)], upper := (rows 37 98 388 25 145 106 74 202 330), lower := (rows 37 98 388 25 145 32 64 128 256), losses := [] }

theorem u37838 : Upper (D 7) (R 7) [36,96,384,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37839 : Route 9 := (fun mask => (mask,id))

def c37839 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37839 : Upper (D 7) (R 7) [36,96,384,17,130] 13 := by
  apply FastRouting.sound _ _ [36,96,384,17,130] 13 (by decide) (choices 1) [1,2,8,64] r37839 c37839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24769
  · exact u24770
  · exact u24771
  · exact u24772

def r37840 : Route 9 := (fun mask => (mask,id))

def c37840 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37840 : Upper (D 7) (R 7) [36,96,384,17,136] 13 := by
  apply FastRouting.sound _ _ [36,96,384,17,136] 13 (by decide) (choices 1) [1,2,64] r37840 c37840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24773
  · exact u24774
  · exact u24775

def r37841 : Route 9 := (fun mask => (mask,id))

def c37841 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37841 : Upper (D 7) (R 7) [36,96,384,17,192] 13 := by
  apply FastRouting.sound _ _ [36,96,384,17,192] 13 (by decide) (choices 1) [1,2,8] r37841 c37841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24776
  · exact u24777
  · exact u24778

def b37842 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 388 26 26 225 193 193 449), lower := (rows 37 98 388 26 26 32 64 128 256), losses := [] }

theorem u37842 : Upper (D 7) (R 7) [36,96,384,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37843 : Route 9 := (fun mask => (mask,id))

def c37843 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u37843 : Upper (D 7) (R 7) [36,96,384,18,65] 13 := by
  apply FastRouting.sound _ _ [36,96,384,18,65] 13 (by decide) (choices 1) [1,2,8,128] r37843 c37843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24779
  · exact u24780
  · exact u24781
  · exact u24782

def b37844 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 98 388 26 82 169 201 137 393), lower := (rows 37 98 388 26 82 32 64 128 256), losses := [] }

theorem u37844 : Upper (D 7) (R 7) [36,96,384,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37845 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 37 98 388 26 88 163 195 131 387), lower := (rows 37 98 388 26 88 32 64 128 256), losses := [] }

theorem u37845 : Upper (D 7) (R 7) [36,96,384,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37846 : Route 9 := (fun mask => (mask,id))

def c37846 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37846 : Upper (D 7) (R 7) [36,96,384,18,129] 13 := by
  apply FastRouting.sound _ _ [36,96,384,18,129] 13 (by decide) (choices 1) [1,2,8,64] r37846 c37846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24783
  · exact u24784
  · exact u24785
  · exact u24786

def b37847 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 98 388 26 146 105 73 201 329), lower := (rows 37 98 388 26 146 32 64 128 256), losses := [] }

theorem u37847 : Upper (D 7) (R 7) [36,96,384,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37848 : Route 9 := (fun mask => (mask,id))

def c37848 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37848 : Upper (D 7) (R 7) [36,96,384,18,136] 13 := by
  apply FastRouting.sound _ _ [36,96,384,18,136] 13 (by decide) (choices 1) [1,2,64] r37848 c37848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24787
  · exact u24788
  · exact u24789

def r37849 : Route 9 := (fun mask => (mask,id))

def c37849 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37849 : Upper (D 7) (R 7) [36,96,384,18,192] 13 := by
  apply FastRouting.sound _ _ [36,96,384,18,192] 13 (by decide) (choices 1) [1,2,8] r37849 c37849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24790
  · exact u24791
  · exact u24792

def r37850 : Route 9 := (fun mask => (mask,id))

def c37850 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37850 : Upper (D 7) (R 7) [36,96,384,65,129] 13 := by
  apply FastRouting.sound _ _ [36,96,384,65,129] 13 (by decide) (choices 1) [2,8,16] r37850 c37850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24793
  · exact u24794
  · exact u24795

def r37851 : Route 9 := (fun mask => (mask,id))

def c37851 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37851 : Upper (D 7) (R 7) [36,96,384,65,130] 13 := by
  apply FastRouting.sound _ _ [36,96,384,65,130] 13 (by decide) (choices 1) [1,2,8,16] r37851 c37851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24796
  · exact u24797
  · exact u24798
  · exact u24799

def r37852 : Route 9 := (fun mask => (mask,id))

def c37852 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37852 : Upper (D 7) (R 7) [36,96,384,65,136] 13 := by
  apply FastRouting.sound _ _ [36,96,384,65,136] 13 (by decide) (choices 1) [1,2,16] r37852 c37852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24800
  · exact u24801
  · exact u24802

def b37853 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 388 74 145 59 91 155 283), lower := (rows 37 98 388 74 145 32 64 128 256), losses := [] }

theorem u37853 : Upper (D 7) (R 7) [36,96,384,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37854 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 388 74 146 57 89 153 281), lower := (rows 37 98 388 74 146 32 64 128 256), losses := [] }

theorem u37854 : Upper (D 7) (R 7) [36,96,384,66,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37854 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37855 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 388 74 152 51 83 147 275), lower := (rows 37 98 388 74 152 32 64 128 256), losses := [] }

theorem u37855 : Upper (D 7) (R 7) [36,96,384,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r37856 : Route 9 := (fun mask => (mask,id))

def c37856 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37856 : Upper (D 7) (R 7) [36,96,384,80,129] 13 := by
  apply FastRouting.sound _ _ [36,96,384,80,129] 13 (by decide) (choices 1) [1,2,8] r37856 c37856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24803
  · exact u24804
  · exact u24805

def r37857 : Route 9 := (fun mask => (mask,id))

def c37857 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37857 : Upper (D 7) (R 7) [36,96,384,80,130] 13 := by
  apply FastRouting.sound _ _ [36,96,384,80,130] 13 (by decide) (choices 1) [1,2,8] r37857 c37857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24806
  · exact u24807
  · exact u24808

def b37858 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(2,6)], upper := (rows 37 98 388 88 152 35 67 131 259), lower := (rows 37 98 388 88 152 32 64 128 256), losses := [] }

theorem u37858 : Upper (D 7) (R 7) [36,96,384,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37858 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37859 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5),(3,5),(3,6),(3,7)], upper := (rows 37 194 7 11 56 496 464 464 464), lower := (rows 37 194 7 11 56 32 64 128 256), losses := [] }

theorem u37859 : Upper (D 7) (R 7) [36,192,3,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u37859
end Delivery.IrregularNine14.P07
