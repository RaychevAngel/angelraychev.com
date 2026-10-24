import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0299
import IrregularNine14P07C0300

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33780 : Route 9 := (fun mask => (mask,id))

def c33780 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33780 : Upper (D 7) (R 7) [34,65,9,20,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,384] 13 (by decide) (choices 1) [2,64,128] r33780 c33780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17955
  · exact u17956
  · exact u17957

def b33781 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 13 42 84 432 464 400 400), lower := (rows 35 67 13 42 84 32 64 128 256), losses := [] }

theorem u33781 : Upper (D 7) (R 7) [34,65,9,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33782 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 13 42 148 496 464 464 464), lower := (rows 35 67 13 42 148 32 64 128 256), losses := [] }

theorem u33782 : Upper (D 7) (R 7) [34,65,9,34,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33783 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 13 42 208 436 468 404 404), lower := (rows 35 67 13 42 208 32 64 128 256), losses := [] }

theorem u33783 : Upper (D 7) (R 7) [34,65,9,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33784 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 13 42 276 240 208 208 464), lower := (rows 35 67 13 42 276 32 64 128 256), losses := [] }

theorem u33784 : Upper (D 7) (R 7) [34,65,9,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33785 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 13 42 336 180 212 148 404), lower := (rows 35 67 13 42 336 32 64 128 256), losses := [] }

theorem u33785 : Upper (D 7) (R 7) [34,65,9,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33786 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 67 13 42 400 244 212 212 468), lower := (rows 35 67 13 42 400 32 64 128 256), losses := [] }

theorem u33786 : Upper (D 7) (R 7) [34,65,9,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33787 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 67 13 44 146 496 464 464 464), lower := (rows 35 67 13 44 146 32 64 128 256), losses := [] }

theorem u33787 : Upper (D 7) (R 7) [34,65,9,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33788 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 67 13 44 208 434 466 402 402), lower := (rows 35 67 13 44 208 32 64 128 256), losses := [] }

theorem u33788 : Upper (D 7) (R 7) [34,65,9,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33789 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 67 13 44 274 240 208 208 464), lower := (rows 35 67 13 44 274 32 64 128 256), losses := [] }

theorem u33789 : Upper (D 7) (R 7) [34,65,9,36,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33790 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 67 13 44 336 178 210 146 402), lower := (rows 35 67 13 44 336 32 64 128 256), losses := [] }

theorem u33790 : Upper (D 7) (R 7) [34,65,9,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33791 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 67 13 44 400 242 210 210 466), lower := (rows 35 67 13 44 400 32 64 128 256), losses := [] }

theorem u33791 : Upper (D 7) (R 7) [34,65,9,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33792 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 67 13 56 82 420 452 388 388), lower := (rows 35 67 13 56 82 32 64 128 256), losses := [] }

theorem u33792 : Upper (D 7) (R 7) [34,65,9,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33793 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(3,0),(4,5)], upper := (rows 35 67 13 56 84 418 450 386 386), lower := (rows 35 67 13 56 84 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 35 67 131 259), good := (rows 482 482 508 56 92 32 64 128 256) }] }

theorem u33793 : Upper (D 7) (R 7) [34,65,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33794 : Route 9 := (fun mask => (mask,id))

def c33794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | _ => 0)

theorem u33794 : Upper (D 7) (R 7) [34,65,9,48,130] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48,130] 13 (by decide) (choices 1) [4,64,128,256] r33794 c33794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17958
  · exact u17959
  · exact u17960
  · exact u17961

def b33795 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 67 13 56 148 482 450 450 450), lower := (rows 35 67 13 56 148 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 35 67 131 259), good := (rows 482 482 508 56 156 32 64 128 256) }] }

theorem u33795 : Upper (D 7) (R 7) [34,65,9,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33796 : Route 9 := (fun mask => (mask,id))

def c33796 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33796 : Upper (D 7) (R 7) [34,65,9,48,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48,192] 13 (by decide) (choices 1) [2,4,128,256] r33796 c33796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17962
  · exact u17963
  · exact u17964
  · exact u17965

def r33797 : Route 9 := (fun mask => (mask,id))

def c33797 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33797 : Upper (D 7) (R 7) [34,65,9,48,258] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48,258] 13 (by decide) (choices 1) [4,64,128] r33797 c33797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17966
  · exact u17967
  · exact u17968

def b33798 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 67 13 56 276 226 194 194 450), lower := (rows 35 67 13 56 276 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 35 67 131 259), good := (rows 482 482 508 56 284 32 64 128 256) }] }

theorem u33798 : Upper (D 7) (R 7) [34,65,9,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33799 : Route 9 := (fun mask => (mask,id))

def c33799 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33799 : Upper (D 7) (R 7) [34,65,9,48,320] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48,320] 13 (by decide) (choices 1) [2,4,128] r33799 c33799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17969
  · exact u17970
  · exact u17971

def r33800 : Route 9 := (fun mask => (mask,id))

def c33800 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33800 : Upper (D 7) (R 7) [34,65,9,48,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48,384] 13 (by decide) (choices 1) [2,4,64,128] r33800 c33800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17972
  · exact u17973
  · exact u17974
  · exact u17975

def b33801 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 12, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 67 13 74 52 432 464 400 400), lower := (rows 35 67 13 74 52 32 64 128 256), losses := [] }

theorem u33801 : Upper (D 7) (R 7) [34,65,9,66,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33802 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 12, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 67 13 74 148 432 496 432 432), lower := (rows 35 67 13 74 148 32 64 128 256), losses := [] }

theorem u33802 : Upper (D 7) (R 7) [34,65,9,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33803 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 12, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 67 13 74 176 436 468 404 404), lower := (rows 35 67 13 74 176 32 64 128 256), losses := [] }

theorem u33803 : Upper (D 7) (R 7) [34,65,9,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33803 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33804 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 12, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 67 13 74 276 176 240 176 432), lower := (rows 35 67 13 74 276 32 64 128 256), losses := [] }

theorem u33804 : Upper (D 7) (R 7) [34,65,9,66,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33805 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 12, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 67 13 74 304 180 212 148 404), lower := (rows 35 67 13 74 304 32 64 128 256), losses := [] }

theorem u33805 : Upper (D 7) (R 7) [34,65,9,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33805 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33806 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 12, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 67 13 74 400 180 244 180 436), lower := (rows 35 67 13 74 400 32 64 128 256), losses := [] }

theorem u33806 : Upper (D 7) (R 7) [34,65,9,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33807 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 12, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 67 13 76 146 432 496 432 432), lower := (rows 35 67 13 76 146 32 64 128 256), losses := [] }

theorem u33807 : Upper (D 7) (R 7) [34,65,9,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33808 : PairBound 9 := { available := 402, camps := [{ cop := 1, region := 12, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 67 13 76 176 434 466 402 402), lower := (rows 35 67 13 76 176 32 64 128 256), losses := [] }

theorem u33808 : Upper (D 7) (R 7) [34,65,9,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33809 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 12, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 67 13 76 274 176 240 176 432), lower := (rows 35 67 13 76 274 32 64 128 256), losses := [] }

theorem u33809 : Upper (D 7) (R 7) [34,65,9,68,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33810 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 12, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 67 13 76 304 178 210 146 402), lower := (rows 35 67 13 76 304 32 64 128 256), losses := [] }

theorem u33810 : Upper (D 7) (R 7) [34,65,9,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33811 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 12, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 67 13 76 400 178 242 178 434), lower := (rows 35 67 13 76 400 32 64 128 256), losses := [] }

theorem u33811 : Upper (D 7) (R 7) [34,65,9,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33812 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 67 13 88 50 420 452 388 388), lower := (rows 35 67 13 88 50 32 64 128 256), losses := [] }

theorem u33812 : Upper (D 7) (R 7) [34,65,9,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33813 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(3,0),(4,0)], upper := (rows 35 67 13 88 52 418 450 386 386), lower := (rows 35 67 13 88 52 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 35 67 131 259), good := (rows 482 482 508 88 60 32 64 128 256) }] }

theorem u33813 : Upper (D 7) (R 7) [34,65,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33814 : Route 9 := (fun mask => (mask,id))

def c33814 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33814 : Upper (D 7) (R 7) [34,65,9,80,130] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,130] 13 (by decide) (choices 1) [4,128,256] r33814 c33814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17976
  · exact u17977
  · exact u17978

def b33815 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(3,0),(4,0),(4,6)], upper := (rows 35 67 13 88 148 418 482 418 418), lower := (rows 35 67 13 88 148 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 35 67 131 259), good := (rows 482 482 508 88 156 32 64 128 256) },{ target := 6, region := (rows 3 2 4 8 20 35 0 131 259), good := (rows 419 419 445 24 148 32 0 128 256) }] }

theorem u33815 : Upper (D 7) (R 7) [34,65,9,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33815 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33816 : Route 9 := (fun mask => (mask,id))

def c33816 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u33816 : Upper (D 7) (R 7) [34,65,9,80,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,160] 13 (by decide) (choices 1) [2,4,128,256] r33816 c33816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17979
  · exact u17980
  · exact u17981
  · exact u17982

def r33817 : Route 9 := (fun mask => (mask,id))

def c33817 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33817 : Upper (D 7) (R 7) [34,65,9,80,258] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,258] 13 (by decide) (choices 1) [4,128] r33817 c33817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17983
  · exact u17984

def b33818 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,0),(4,0),(4,6)], upper := (rows 35 67 13 88 276 162 226 162 418), lower := (rows 35 67 13 88 276 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 35 67 131 259), good := (rows 482 482 508 88 284 32 64 128 256) },{ target := 6, region := (rows 3 2 4 8 20 35 0 131 259), good := (rows 419 419 445 24 276 32 0 128 256) }] }

theorem u33818 : Upper (D 7) (R 7) [34,65,9,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33819 : Route 9 := (fun mask => (mask,id))

def c33819 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33819 : Upper (D 7) (R 7) [34,65,9,80,288] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,288] 13 (by decide) (choices 1) [2,4,128] r33819 c33819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17985
  · exact u17986
  · exact u17987

def r33820 : Route 9 := (fun mask => (mask,id))

def c33820 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33820 : Upper (D 7) (R 7) [34,65,9,80,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,384] 13 (by decide) (choices 1) [2,4,128] r33820 c33820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17988
  · exact u17989
  · exact u17990

def b33821 : PairBound 9 := { available := 404, camps := [{ cop := 3, region := 7, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,7)], upper := (rows 35 67 13 104 146 436 468 404 404), lower := (rows 35 67 13 104 146 32 64 128 256), losses := [] }

theorem u33821 : Upper (D 7) (R 7) [34,65,9,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33822 : PairBound 9 := { available := 402, camps := [{ cop := 3, region := 7, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,7)], upper := (rows 35 67 13 104 148 434 466 402 402), lower := (rows 35 67 13 104 148 32 64 128 256), losses := [] }

theorem u33822 : Upper (D 7) (R 7) [34,65,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33823 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 7, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,7)], upper := (rows 35 67 13 104 274 180 212 148 404), lower := (rows 35 67 13 104 274 32 64 128 256), losses := [] }

theorem u33823 : Upper (D 7) (R 7) [34,65,9,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33824 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 7, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,7)], upper := (rows 35 67 13 104 276 178 210 146 402), lower := (rows 35 67 13 104 276 32 64 128 256), losses := [] }

theorem u33824 : Upper (D 7) (R 7) [34,65,9,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33825 : PairBound 9 := { available := 150, camps := [{ cop := 3, region := 7, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(2,7)], upper := (rows 35 67 13 104 400 182 214 150 406), lower := (rows 35 67 13 104 400 32 64 128 256), losses := [] }

theorem u33825 : Upper (D 7) (R 7) [34,65,9,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33826 : Route 9 := (fun mask => (mask,id))

def c33826 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u33826 : Upper (D 7) (R 7) [34,65,9,130,36] 13 := by
  apply FastRouting.sound _ _ [34,65,9,130,36] 13 (by decide) (choices 1) [16,64,128,256] r33826 c33826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17991
  · exact u17992
  · exact u17993
  · exact u17994

def r33827 : Route 9 := (fun mask => (mask,id))

def c33827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u33827 : Upper (D 7) (R 7) [34,65,9,130,68] 13 := by
  apply FastRouting.sound _ _ [34,65,9,130,68] 13 (by decide) (choices 1) [16,128,256] r33827 c33827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17995
  · exact u17996
  · exact u17997

def b33828 : PairBound 9 := { available := 404, camps := [{ cop := 2, region := 496, targets := 3 },{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,1)], upper := (rows 35 67 13 138 112 436 468 404 404), lower := (rows 35 67 13 138 112 32 64 128 256), losses := [] }

theorem u33828 : Upper (D 7) (R 7) [34,65,9,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33829 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 496, targets := 3 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,1)], upper := (rows 35 67 13 138 148 368 368 496 368), lower := (rows 35 67 13 138 148 32 64 128 256), losses := [] }

theorem u33829 : Upper (D 7) (R 7) [34,65,9,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33830 : Route 9 := (fun mask => (mask,id))

def c33830 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u33830 : Upper (D 7) (R 7) [34,65,9,130,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,130,160] 13 (by decide) (choices 1) [4,16,64,256] r33830 c33830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17998
  · exact u17999
  · exact u18000
  · exact u18001

def r33831 : Route 9 := (fun mask => (mask,id))

def c33831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33831 : Upper (D 7) (R 7) [34,65,9,130,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,130,192] 13 (by decide) (choices 1) [4,16,256] r33831 c33831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18002
  · exact u18003
  · exact u18004

def r33832 : Route 9 := (fun mask => (mask,id))

def c33832 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33832 : Upper (D 7) (R 7) [34,65,9,130,260] 13 := by
  apply FastRouting.sound _ _ [34,65,9,130,260] 13 (by decide) (choices 1) [16,64,128] r33832 c33832
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18005
  · exact u18006
  · exact u18007

def r33833 : Route 9 := (fun mask => (mask,id))

def c33833 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33833 : Upper (D 7) (R 7) [34,65,9,130,288] 13 := by
  apply FastRouting.sound _ _ [34,65,9,130,288] 13 (by decide) (choices 1) [4,16,64,128] r33833 c33833
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18008
  · exact u18009
  · exact u18010
  · exact u18011

def r33834 : Route 9 := (fun mask => (mask,id))

def c33834 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33834 : Upper (D 7) (R 7) [34,65,9,130,320] 13 := by
  apply FastRouting.sound _ _ [34,65,9,130,320] 13 (by decide) (choices 1) [4,16,128] r33834 c33834
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18012
  · exact u18013
  · exact u18014

def r33835 : Route 9 := (fun mask => (mask,id))

def c33835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33835 : Upper (D 7) (R 7) [34,65,9,130,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,130,384] 13 (by decide) (choices 1) [4,16,64] r33835 c33835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18015
  · exact u18016
  · exact u18017

def b33836 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 67 13 140 50 496 464 464 464), lower := (rows 35 67 13 140 50 32 64 128 256), losses := [] }

theorem u33836 : Upper (D 7) (R 7) [34,65,9,132,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33837 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 429, targets := 64 },{ cop := 1, region := 16, targets := 32 }], pairs := [(0,6),(2,6),(3,6),(4,5)], upper := (rows 35 67 13 140 82 432 496 432 432), lower := (rows 35 67 13 140 82 32 64 128 256), losses := [] }

theorem u33837 : Upper (D 7) (R 7) [34,65,9,132,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33838 : PairBound 9 := { available := 402, camps := [{ cop := 4, region := 3, targets := 128 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 140 112 434 466 402 402), lower := (rows 35 67 13 140 112 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 23 35 67 131 259), good := (rows 498 498 508 156 112 32 64 128 256) }] }

theorem u33838 : Upper (D 7) (R 7) [34,65,9,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33839 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 140 146 368 368 496 368), lower := (rows 35 67 13 140 146 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 19 55 87 151 279), good := (rows 498 498 508 492 498 32 64 128 256) }] }

theorem u33839 : Upper (D 7) (R 7) [34,65,9,132,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u33839
end Delivery.IrregularNine14.P07
