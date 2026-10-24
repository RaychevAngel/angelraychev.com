import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0465
import IrregularNine14P07C0466

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b39720 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 322 196 25 49 170 202 138 394), lower := (rows 37 322 196 25 49 32 64 128 256), losses := [] }

theorem u39720 : Upper (D 7) (R 7) [36,320,192,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39721 : Route 9 := (fun mask => (mask,id))

def c39721 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39721 : Upper (D 7) (R 7) [36,320,192,17,34] 13 := by
  apply FastRouting.sound _ _ [36,320,192,17,34] 13 (by decide) (choices 1) [1,2,8,128] r39721 c39721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27944
  · exact u27945
  · exact u27946
  · exact u27947

def b39722 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 322 196 25 56 163 195 131 387), lower := (rows 37 322 196 25 56 32 64 128 256), losses := [] }

theorem u39722 : Upper (D 7) (R 7) [36,320,192,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39723 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 8, targets := 98 },{ cop := 3, region := 354, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,6)], upper := (rows 37 322 196 25 145 42 106 170 298), lower := (rows 37 322 196 25 145 32 64 128 256), losses := [] }

theorem u39723 : Upper (D 7) (R 7) [36,320,192,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39723 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39724 : Route 9 := (fun mask => (mask,id))

def c39724 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39724 : Upper (D 7) (R 7) [36,320,192,17,130] 13 := by
  apply FastRouting.sound _ _ [36,320,192,17,130] 13 (by decide) (choices 1) [1,2,8] r39724 c39724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27948
  · exact u27949
  · exact u27950

def r39725 : Route 9 := (fun mask => (mask,id))

def c39725 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39725 : Upper (D 7) (R 7) [36,320,192,17,136] 13 := by
  apply FastRouting.sound _ _ [36,320,192,17,136] 13 (by decide) (choices 1) [1,2] r39725 c39725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27951
  · exact u27952

def r39726 : Route 9 := (fun mask => (mask,id))

def c39726 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39726 : Upper (D 7) (R 7) [36,320,192,17,160] 13 := by
  apply FastRouting.sound _ _ [36,320,192,17,160] 13 (by decide) (choices 1) [1,2,8] r39726 c39726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27953
  · exact u27954
  · exact u27955

def b39727 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 322 196 26 26 161 225 161 417), lower := (rows 37 322 196 26 26 32 64 128 256), losses := [] }

theorem u39727 : Upper (D 7) (R 7) [36,320,192,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39728 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 196 26 49 171 203 139 395), lower := (rows 37 322 196 26 49 32 64 128 256), losses := [] }

theorem u39728 : Upper (D 7) (R 7) [36,320,192,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39729 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 322 196 26 50 169 201 137 393), lower := (rows 37 322 196 26 50 32 64 128 256), losses := [] }

theorem u39729 : Upper (D 7) (R 7) [36,320,192,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39730 : Route 9 := (fun mask => (mask,id))

def c39730 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39730 : Upper (D 7) (R 7) [36,320,192,18,40] 13 := by
  apply FastRouting.sound _ _ [36,320,192,18,40] 13 (by decide) (choices 1) [1,2,128] r39730 c39730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27956
  · exact u27957
  · exact u27958

def r39731 : Route 9 := (fun mask => (mask,id))

def c39731 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39731 : Upper (D 7) (R 7) [36,320,192,18,129] 13 := by
  apply FastRouting.sound _ _ [36,320,192,18,129] 13 (by decide) (choices 1) [1,2,8] r39731 c39731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27959
  · exact u27960
  · exact u27961

def b39732 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 322 196 26 146 41 105 169 297), lower := (rows 37 322 196 26 146 32 64 128 256), losses := [] }

theorem u39732 : Upper (D 7) (R 7) [36,320,192,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39733 : Route 9 := (fun mask => (mask,id))

def c39733 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39733 : Upper (D 7) (R 7) [36,320,192,18,136] 13 := by
  apply FastRouting.sound _ _ [36,320,192,18,136] 13 (by decide) (choices 1) [1,2] r39733 c39733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27962
  · exact u27963

def r39734 : Route 9 := (fun mask => (mask,id))

def c39734 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39734 : Upper (D 7) (R 7) [36,320,192,18,160] 13 := by
  apply FastRouting.sound _ _ [36,320,192,18,160] 13 (by decide) (choices 1) [1,2,8] r39734 c39734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27964
  · exact u27965
  · exact u27966

def b39735 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 196 41 145 58 90 154 282), lower := (rows 37 322 196 41 145 32 64 128 256), losses := [] }

theorem u39735 : Upper (D 7) (R 7) [36,320,192,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39736 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 196 41 146 59 91 155 283), lower := (rows 37 322 196 41 146 32 64 128 256), losses := [] }

theorem u39736 : Upper (D 7) (R 7) [36,320,192,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39737 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 196 41 152 51 83 147 275), lower := (rows 37 322 196 41 152 32 64 128 256), losses := [] }

theorem u39737 : Upper (D 7) (R 7) [36,320,192,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39738 : Route 9 := (fun mask => (mask,id))

def c39738 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39738 : Upper (D 7) (R 7) [36,320,192,34,129] 13 := by
  apply FastRouting.sound _ _ [36,320,192,34,129] 13 (by decide) (choices 1) [1,2,8,16] r39738 c39738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27967
  · exact u27968
  · exact u27969
  · exact u27970

def r39739 : Route 9 := (fun mask => (mask,id))

def c39739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39739 : Upper (D 7) (R 7) [36,320,192,34,130] 13 := by
  apply FastRouting.sound _ _ [36,320,192,34,130] 13 (by decide) (choices 1) [1,8,16] r39739 c39739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27971
  · exact u27972
  · exact u27973

def r39740 : Route 9 := (fun mask => (mask,id))

def c39740 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39740 : Upper (D 7) (R 7) [36,320,192,34,136] 13 := by
  apply FastRouting.sound _ _ [36,320,192,34,136] 13 (by decide) (choices 1) [1,2,16] r39740 c39740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27974
  · exact u27975
  · exact u27976

def r39741 : Route 9 := (fun mask => (mask,id))

def c39741 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39741 : Upper (D 7) (R 7) [36,320,192,48,129] 13 := by
  apply FastRouting.sound _ _ [36,320,192,48,129] 13 (by decide) (choices 1) [1,2,8] r39741 c39741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27977
  · exact u27978
  · exact u27979

def r39742 : Route 9 := (fun mask => (mask,id))

def c39742 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39742 : Upper (D 7) (R 7) [36,320,192,48,130] 13 := by
  apply FastRouting.sound _ _ [36,320,192,48,130] 13 (by decide) (choices 1) [1,2,8] r39742 c39742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27980
  · exact u27981
  · exact u27982

def b39743 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,5)], upper := (rows 37 322 196 56 152 35 67 131 259), lower := (rows 37 322 196 56 152 32 64 128 256), losses := [] }

theorem u39743 : Upper (D 7) (R 7) [36,320,192,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39744 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 97 162 7 11 28 496 464 464 464), lower := (rows 97 162 7 11 28 32 64 128 256), losses := [] }

theorem u39744 : Upper (D 7) (R 7) [96,160,3,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39745 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 2, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 97 162 7 11 84 440 472 408 408), lower := (rows 97 162 7 11 84 32 64 128 256), losses := [] }

theorem u39745 : Upper (D 7) (R 7) [96,160,3,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39746 : PairBound 9 := { available := 284, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 2, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 97 162 7 11 208 316 348 412 284), lower := (rows 97 162 7 11 208 32 64 128 256), losses := [] }

theorem u39746 : Upper (D 7) (R 7) [96,160,3,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39747 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 2, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 97 162 7 11 276 248 216 216 472), lower := (rows 97 162 7 11 276 32 64 128 256), losses := [] }

theorem u39747 : Upper (D 7) (R 7) [96,160,3,3,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39748 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 2, region := 8, targets := 192 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 97 162 7 11 336 188 220 156 412), lower := (rows 97 162 7 11 336 32 64 128 256), losses := [] }

theorem u39748 : Upper (D 7) (R 7) [96,160,3,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39749 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 97 162 7 13 26 496 464 464 464), lower := (rows 97 162 7 13 26 32 64 128 256), losses := [] }

theorem u39749 : Upper (D 7) (R 7) [96,160,3,5,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39750 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 162 7 13 82 440 472 408 408), lower := (rows 97 162 7 13 82 32 64 128 256), losses := [] }

theorem u39750 : Upper (D 7) (R 7) [96,160,3,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39751 : PairBound 9 := { available := 402, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 162 7 13 88 434 466 402 402), lower := (rows 97 162 7 13 88 32 64 128 256), losses := [] }

theorem u39751 : Upper (D 7) (R 7) [96,160,3,5,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39752 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 162 7 13 152 370 338 466 338), lower := (rows 97 162 7 13 152 32 64 128 256), losses := [] }

theorem u39752 : Upper (D 7) (R 7) [96,160,3,5,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39753 : PairBound 9 := { available := 282, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 162 7 13 208 314 346 410 282), lower := (rows 97 162 7 13 208 32 64 128 256), losses := [] }

theorem u39753 : Upper (D 7) (R 7) [96,160,3,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39754 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 162 7 13 274 248 216 216 472), lower := (rows 97 162 7 13 274 32 64 128 256), losses := [] }

theorem u39754 : Upper (D 7) (R 7) [96,160,3,5,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39755 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 162 7 13 280 242 210 210 466), lower := (rows 97 162 7 13 280 32 64 128 256), losses := [] }

theorem u39755 : Upper (D 7) (R 7) [96,160,3,5,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39756 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 162 7 13 336 186 218 154 410), lower := (rows 97 162 7 13 336 32 64 128 256), losses := [] }

theorem u39756 : Upper (D 7) (R 7) [96,160,3,5,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39757 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 8, targets := 194 },{ cop := 2, region := 8, targets := 32 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 97 162 7 13 400 122 90 218 346), lower := (rows 97 162 7 13 400 32 64 128 256), losses := [] }

theorem u39757 : Upper (D 7) (R 7) [96,160,3,5,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39758 : PairBound 9 := { available := 452, camps := [{ cop := 2, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 97 162 7 25 26 484 452 452 452), lower := (rows 97 162 7 25 26 32 64 128 256), losses := [] }

theorem u39758 : Upper (D 7) (R 7) [96,160,3,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39759 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 97 162 7 25 28 482 450 450 450), lower := (rows 97 162 7 25 28 32 64 128 256), losses := [] }

theorem u39759 : Upper (D 7) (R 7) [96,160,3,17,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39760 : PairBound 9 := { available := 396, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 162 7 25 82 428 460 396 396), lower := (rows 97 162 7 25 82 32 64 128 256), losses := [] }

theorem u39760 : Upper (D 7) (R 7) [96,160,3,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39761 : PairBound 9 := { available := 394, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 162 7 25 84 426 458 394 394), lower := (rows 97 162 7 25 84 32 64 128 256), losses := [] }

theorem u39761 : Upper (D 7) (R 7) [96,160,3,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39762 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 24, targets := 162 }], pairs := [(3,1),(3,5),(3,7),(4,1)], upper := (rows 97 162 7 25 88 422 454 390 390), lower := (rows 97 162 7 25 88 32 64 128 256), losses := [] }

theorem u39762 : Upper (D 7) (R 7) [96,160,3,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39763 : PairBound 9 := { available := 332, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 97 162 7 25 146 364 332 460 332), lower := (rows 97 162 7 25 146 32 64 128 256), losses := [] }

theorem u39763 : Upper (D 7) (R 7) [96,160,3,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39764 : Route 9 := (fun mask => (mask,id))

def c39764 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u39764 : Upper (D 7) (R 7) [96,160,3,17,132] 13 := by
  apply FastRouting.sound _ _ [96,160,3,17,132] 13 (by decide) (choices 1) [2,8,64,256] r39764 c39764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27983
  · exact u27984
  · exact u27985
  · exact u27986

def b39765 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 2, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 97 162 7 25 152 358 326 454 326), lower := (rows 97 162 7 25 152 32 64 128 256), losses := [] }

theorem u39765 : Upper (D 7) (R 7) [96,160,3,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39766 : PairBound 9 := { available := 270, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 162 7 25 208 302 334 398 270), lower := (rows 97 162 7 25 208 32 64 128 256), losses := [] }

theorem u39766 : Upper (D 7) (R 7) [96,160,3,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39767 : Route 9 := (fun mask => (mask,id))

def c39767 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39767 : Upper (D 7) (R 7) [96,160,3,17,258] 13 := by
  apply FastRouting.sound _ _ [96,160,3,17,258] 13 (by decide) (choices 1) [4,8,64,128] r39767 c39767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27987
  · exact u27988
  · exact u27989
  · exact u27990

def r39768 : Route 9 := (fun mask => (mask,id))

def c39768 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39768 : Upper (D 7) (R 7) [96,160,3,17,260] 13 := by
  apply FastRouting.sound _ _ [96,160,3,17,260] 13 (by decide) (choices 1) [2,8,64,128] r39768 c39768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27991
  · exact u27992
  · exact u27993
  · exact u27994

def r39769 : Route 9 := (fun mask => (mask,id))

def c39769 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39769 : Upper (D 7) (R 7) [96,160,3,17,264] 13 := by
  apply FastRouting.sound _ _ [96,160,3,17,264] 13 (by decide) (choices 1) [2,4,64,128] r39769 c39769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27995
  · exact u27996
  · exact u27997
  · exact u27998

def b39770 : PairBound 9 := { available := 142, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 162 7 25 336 174 206 142 398), lower := (rows 97 162 7 25 336 32 64 128 256), losses := [] }

theorem u39770 : Upper (D 7) (R 7) [96,160,3,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39771 : Route 9 := (fun mask => (mask,id))

def c39771 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39771 : Upper (D 7) (R 7) [96,160,3,17,384] 13 := by
  apply FastRouting.sound _ _ [96,160,3,17,384] 13 (by decide) (choices 1) [2,4,8,64] r39771 c39771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27999
  · exact u28000
  · exact u28001
  · exact u28002

def b39772 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 16, targets := 162 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(4,1),(4,5),(4,7)], upper := (rows 97 162 7 28 81 426 458 394 394), lower := (rows 97 162 7 28 81 32 64 128 256), losses := [] }

theorem u39772 : Upper (D 7) (R 7) [96,160,3,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39773 : Route 9 := (fun mask => (mask,id))

def c39773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u39773 : Upper (D 7) (R 7) [96,160,3,20,66] 13 := by
  apply FastRouting.sound _ _ [96,160,3,20,66] 13 (by decide) (choices 1) [1,8,128,256] r39773 c39773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28003
  · exact u28004
  · exact u28005
  · exact u28006

def b39774 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 2, region := 472, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(4,5)], upper := (rows 97 162 7 28 88 419 451 387 387), lower := (rows 97 162 7 28 88 32 64 128 256), losses := [] }

theorem u39774 : Upper (D 7) (R 7) [96,160,3,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m39775_2 : Upper (D 7) (R 7) [96,160,3,20,192,2] 13 :=
  permutation_upper _ _ _ [96,160,3,20,192,1] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28007

def r39775 : Route 9 := (fun mask => (mask,id))

def c39775 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u39775 : Upper (D 7) (R 7) [96,160,3,20,192] 13 := by
  apply FastRouting.sound _ _ [96,160,3,20,192] 13 (by decide) (choices 1) [1,2,8,256] r39775 c39775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28007
  · exact m39775_2
  · exact u28008
  · exact u28009

def r39776 : Route 9 := (fun mask => (mask,id))

def c39776 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39776 : Upper (D 7) (R 7) [96,160,3,20,257] 13 := by
  apply FastRouting.sound _ _ [96,160,3,20,257] 13 (by decide) (choices 1) [2,8,64,128] r39776 c39776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28010
  · exact u28011
  · exact u28012
  · exact u28013

theorem m39777_2 : Upper (D 7) (R 7) [96,160,3,20,264,2] 13 :=
  permutation_upper _ _ _ [96,160,3,20,264,1] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28014

theorem m39777_128 : Upper (D 7) (R 7) [96,160,3,20,264,128] 13 :=
  permutation_upper _ _ _ [96,160,3,20,264,64] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28015

def r39777 : Route 9 := (fun mask => (mask,id))

def c39777 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39777 : Upper (D 7) (R 7) [96,160,3,20,264] 13 := by
  apply FastRouting.sound _ _ [96,160,3,20,264] 13 (by decide) (choices 1) [1,2,64,128] r39777 c39777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28014
  · exact m39777_2
  · exact u28015
  · exact m39777_128

def r39778 : Route 9 := (fun mask => (mask,id))

def c39778 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39778 : Upper (D 7) (R 7) [96,160,3,20,320] 13 := by
  apply FastRouting.sound _ _ [96,160,3,20,320] 13 (by decide) (choices 1) [1,2,8,128] r39778 c39778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u28016
  · exact u28017
  · exact u28018
  · exact u28019

def b39779 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 8, targets := 162 },{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6),(3,1),(3,5),(3,7)], upper := (rows 97 162 7 73 148 314 346 410 282), lower := (rows 97 162 7 73 148 32 64 128 256), losses := [] }

theorem u39779 : Upper (D 7) (R 7) [96,160,3,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u39779
end Delivery.IrregularNine14.P07
