import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0235
import IrregularNine14P06C0236
import IrregularNine14P06C0237

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31860 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 70 140 112 293 325 389 261), lower := (rows 11 50 70 140 112 32 64 128 256), losses := [] }

theorem u31860 : Upper (D 6) (R 6) [10,48,66,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31861 : Route 9 := (fun mask => (mask,id))

def c31861 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31861 : Upper (D 6) (R 6) [10,48,66,132,257] 13 := by
  apply FastRouting.sound _ _ [10,48,66,132,257] 13 (by decide) (choices 1) [1,4,64] r31861 c31861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14140
  · exact u14141
  · exact u14142

def r31862 : Route 9 := (fun mask => (mask,id))

def c31862 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31862 : Upper (D 6) (R 6) [10,48,66,132,260] 13 := by
  apply FastRouting.sound _ _ [10,48,66,132,260] 13 (by decide) (choices 1) [1,64] r31862 c31862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14143
  · exact u14144

def b31863 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 70 140 304 101 69 197 325), lower := (rows 11 50 70 140 304 32 64 128 256), losses := [] }

theorem u31863 : Upper (D 6) (R 6) [10,48,66,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31864 : Route 9 := (fun mask => (mask,id))

def c31864 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31864 : Upper (D 6) (R 6) [10,48,66,132,320] 13 := by
  apply FastRouting.sound _ _ [10,48,66,132,320] 13 (by decide) (choices 1) [1,4] r31864 c31864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14145
  · exact u14146

def b31865 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 488, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 50 70 168 21 357 325 453 325), lower := (rows 11 50 70 168 21 32 64 128 256), losses := [] }

theorem u31865 : Upper (D 6) (R 6) [10,48,66,160,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31866 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 425, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 50 70 168 81 293 325 389 261), lower := (rows 11 50 70 168 81 32 64 128 256), losses := [] }

theorem u31866 : Upper (D 6) (R 6) [10,48,66,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31867 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 70 168 84 293 325 389 261), lower := (rows 11 50 70 168 84 32 64 128 256), losses := [] }

theorem u31867 : Upper (D 6) (R 6) [10,48,66,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31868 : Route 9 := (fun mask => (mask,id))

def c31868 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31868 : Upper (D 6) (R 6) [10,48,66,160,257] 13 := by
  apply FastRouting.sound _ _ [10,48,66,160,257] 13 (by decide) (choices 1) [1,4,64] r31868 c31868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14147
  · exact u14148
  · exact u14149

def r31869 : Route 9 := (fun mask => (mask,id))

def c31869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31869 : Upper (D 6) (R 6) [10,48,66,160,260] 13 := by
  apply FastRouting.sound _ _ [10,48,66,160,260] 13 (by decide) (choices 1) [1,4,64] r31869 c31869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14150
  · exact u14151
  · exact u14152

def b31870 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 169, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 50 70 168 336 37 69 133 261), lower := (rows 11 50 70 168 336 32 64 128 256), losses := [] }

theorem u31870 : Upper (D 6) (R 6) [10,48,66,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31871 : Route 9 := (fun mask => (mask,id))

def c31871 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31871 : Upper (D 6) (R 6) [10,48,66,192,5] 13 := by
  apply FastRouting.sound _ _ [10,48,66,192,5] 13 (by decide) (choices 1) [1,4,256] r31871 c31871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14153
  · exact u14154
  · exact u14155

def b31872 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 70 200 49 293 325 389 261), lower := (rows 11 50 70 200 49 32 64 128 256), losses := [] }

theorem u31872 : Upper (D 6) (R 6) [10,48,66,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31873 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 70 200 52 293 325 389 261), lower := (rows 11 50 70 200 52 32 64 128 256), losses := [] }

theorem u31873 : Upper (D 6) (R 6) [10,48,66,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31874 : Route 9 := (fun mask => (mask,id))

def c31874 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31874 : Upper (D 6) (R 6) [10,48,66,192,257] 13 := by
  apply FastRouting.sound _ _ [10,48,66,192,257] 13 (by decide) (choices 1) [1,4] r31874 c31874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14156
  · exact u14157

def r31875 : Route 9 := (fun mask => (mask,id))

def c31875 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31875 : Upper (D 6) (R 6) [10,48,66,192,260] 13 := by
  apply FastRouting.sound _ _ [10,48,66,192,260] 13 (by decide) (choices 1) [1,4] r31875 c31875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14158
  · exact u14159

def b31876 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 70 200 304 37 69 133 261), lower := (rows 11 50 70 200 304 32 64 128 256), losses := [] }

theorem u31876 : Upper (D 6) (R 6) [10,48,66,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31877 : Route 9 := (fun mask => (mask,id))

def c31877 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31877 : Upper (D 6) (R 6) [10,48,66,384,5] 13 := by
  apply FastRouting.sound _ _ [10,48,66,384,5] 13 (by decide) (choices 1) [1,4,64] r31877 c31877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14160
  · exact u14161
  · exact u14162

def b31878 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 70 392 49 101 69 197 325), lower := (rows 11 50 70 392 49 32 64 128 256), losses := [] }

theorem u31878 : Upper (D 6) (R 6) [10,48,66,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31879 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 70 392 52 101 69 197 325), lower := (rows 11 50 70 392 52 32 64 128 256), losses := [] }

theorem u31879 : Upper (D 6) (R 6) [10,48,66,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31880 : Route 9 := (fun mask => (mask,id))

def c31880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31880 : Upper (D 6) (R 6) [10,48,66,384,65] 13 := by
  apply FastRouting.sound _ _ [10,48,66,384,65] 13 (by decide) (choices 1) [1,4] r31880 c31880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14163
  · exact u14164

def b31881 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 50 70 392 84 37 101 165 293), lower := (rows 11 50 70 392 84 32 64 128 256), losses := [] }

theorem u31881 : Upper (D 6) (R 6) [10,48,66,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31882 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 50 70 392 112 37 69 133 261), lower := (rows 11 50 70 392 112 32 64 128 256), losses := [] }

theorem u31882 : Upper (D 6) (R 6) [10,48,66,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31883 : PairBound 9 := { available := 452, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 13 19 484 452 452 452), lower := (rows 11 50 100 13 19 32 64 128 256), losses := [] }

theorem u31883 : Upper (D 6) (R 6) [10,48,96,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31884 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 13 21 482 450 450 450), lower := (rows 11 50 100 13 21 32 64 128 256), losses := [] }

theorem u31884 : Upper (D 6) (R 6) [10,48,96,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31885 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 13 22 481 449 449 449), lower := (rows 11 50 100 13 22 32 64 128 256), losses := [] }

theorem u31885 : Upper (D 6) (R 6) [10,48,96,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31886 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c31886 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u31886 : Upper (D 6) (R 6) [10,48,96,5,65] 13 := by
  apply FastRouting.sound _ _ [10,48,96,5,65] 13 (by decide) (choices 1) [2,4,128] r31886 c31886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14165
  · exact u14166
  · exact u14167

def b31887 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 100 13 82 421 453 389 389), lower := (rows 11 50 100 13 82 32 64 128 256), losses := [] }

theorem u31887 : Upper (D 6) (R 6) [10,48,96,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31888 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 13 84 419 451 387 387), lower := (rows 11 50 100 13 84 32 64 128 256), losses := [] }

theorem u31888 : Upper (D 6) (R 6) [10,48,96,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31889 : Route 9 := (fun mask => (mask,id))

def c31889 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31889 : Upper (D 6) (R 6) [10,48,96,5,129] 13 := by
  apply FastRouting.sound _ _ [10,48,96,5,129] 13 (by decide) (choices 1) [2,4,64,256] r31889 c31889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14168
  · exact u14169
  · exact u14170
  · exact u14171

def b31890 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 11 50 100 13 146 357 325 453 325), lower := (rows 11 50 100 13 146 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 72 136 264), good := (rows 475 18 68 477 146 0 64 128 256) }] }

theorem u31890 : Upper (D 6) (R 6) [10,48,96,5,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31891 : Route 9 := (fun mask => (mask,id))

def c31891 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31891 : Upper (D 6) (R 6) [10,48,96,5,132] 13 := by
  apply FastRouting.sound _ _ [10,48,96,5,132] 13 (by decide) (choices 1) [1,2,64,256] r31891 c31891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14172
  · exact u14173
  · exact u14174
  · exact u14175

def r31892 : Route 9 := (fun mask => (mask,id))

def c31892 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31892 : Upper (D 6) (R 6) [10,48,96,5,192] 13 := by
  apply FastRouting.sound _ _ [10,48,96,5,192] 13 (by decide) (choices 1) [1,2,4,256] r31892 c31892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14176
  · exact u14177
  · exact u14178
  · exact u14179

def r31893 : Route 9 := (fun mask => (mask,id))

def c31893 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31893 : Upper (D 6) (R 6) [10,48,96,5,384] 13 := by
  apply FastRouting.sound _ _ [10,48,96,5,384] 13 (by decide) (choices 1) [1,2,4,64] r31893 c31893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14180
  · exact u14181
  · exact u14182
  · exact u14183

def b31894 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 27, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 50 100 73 19 420 452 388 388), lower := (rows 11 50 100 73 19 32 64 128 256), losses := [] }

theorem u31894 : Upper (D 6) (R 6) [10,48,96,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31895 : PairBound 9 := { available := 390, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 50 100 73 21 422 454 390 390), lower := (rows 11 50 100 73 21 32 64 128 256), losses := [] }

theorem u31895 : Upper (D 6) (R 6) [10,48,96,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31896 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 100 73 22 421 453 389 389), lower := (rows 11 50 100 73 22 32 64 128 256), losses := [] }

theorem u31896 : Upper (D 6) (R 6) [10,48,96,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31897 : Route 9 := (fun mask => (mask,id))

def c31897 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31897 : Upper (D 6) (R 6) [10,48,96,65,129] 13 := by
  apply FastRouting.sound _ _ [10,48,96,65,129] 13 (by decide) (choices 1) [2,4,256] r31897 c31897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14184
  · exact u14185
  · exact u14186

def r31898 : Route 9 := (fun mask => (mask,id))

def c31898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31898 : Upper (D 6) (R 6) [10,48,96,65,130] 13 := by
  apply FastRouting.sound _ _ [10,48,96,65,130] 13 (by decide) (choices 1) [1,4,256] r31898 c31898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14187
  · exact u14188
  · exact u14189

def r31899 : Route 9 := (fun mask => (mask,id))

def c31899 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31899 : Upper (D 6) (R 6) [10,48,96,65,132] 13 := by
  apply FastRouting.sound _ _ [10,48,96,65,132] 13 (by decide) (choices 1) [1,2,4,256] r31899 c31899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14190
  · exact u14191
  · exact u14192
  · exact u14193

def r31900 : Route 9 := (fun mask => (mask,id))

def c31900 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31900 : Upper (D 6) (R 6) [10,48,96,65,384] 13 := by
  apply FastRouting.sound _ _ [10,48,96,65,384] 13 (by decide) (choices 1) [1,2,4] r31900 c31900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14194
  · exact u14195
  · exact u14196

def b31901 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 100 137 19 356 324 452 324), lower := (rows 11 50 100 137 19 32 64 128 256), losses := [] }

theorem u31901 : Upper (D 6) (R 6) [10,48,96,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31902 : Route 9 := (fun mask => (mask,id))

def c31902 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31902 : Upper (D 6) (R 6) [10,48,96,129,5] 13 := by
  apply FastRouting.sound _ _ [10,48,96,129,5] 13 (by decide) (choices 1) [2,4,64,256] r31902 c31902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14197
  · exact u14198
  · exact u14199
  · exact u14200

def b31903 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 100 137 22 357 325 453 325), lower := (rows 11 50 100 137 22 32 64 128 256), losses := [] }

theorem u31903 : Upper (D 6) (R 6) [10,48,96,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31904 : Route 9 := (fun mask => (mask,id))

def c31904 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31904 : Upper (D 6) (R 6) [10,48,96,129,65] 13 := by
  apply FastRouting.sound _ _ [10,48,96,129,65] 13 (by decide) (choices 1) [2,4,256] r31904 c31904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14201
  · exact u14202
  · exact u14203

def b31905 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 100 137 82 293 325 389 261), lower := (rows 11 50 100 137 82 32 64 128 256), losses := [] }

theorem u31905 : Upper (D 6) (R 6) [10,48,96,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31906 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 137 84 295 327 391 263), lower := (rows 11 50 100 137 84 32 64 128 256), losses := [] }

theorem u31906 : Upper (D 6) (R 6) [10,48,96,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31907 : Route 9 := (fun mask => (mask,id))

def c31907 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31907 : Upper (D 6) (R 6) [10,48,96,129,257] 13 := by
  apply FastRouting.sound _ _ [10,48,96,129,257] 13 (by decide) (choices 1) [2,4,64] r31907 c31907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14204
  · exact u14205
  · exact u14206

def r31908 : Route 9 := (fun mask => (mask,id))

def c31908 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31908 : Upper (D 6) (R 6) [10,48,96,129,258] 13 := by
  apply FastRouting.sound _ _ [10,48,96,129,258] 13 (by decide) (choices 1) [1,4,64] r31908 c31908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14207
  · exact u14208
  · exact u14209

def r31909 : Route 9 := (fun mask => (mask,id))

def c31909 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31909 : Upper (D 6) (R 6) [10,48,96,129,260] 13 := by
  apply FastRouting.sound _ _ [10,48,96,129,260] 13 (by decide) (choices 1) [1,2,4,64] r31909 c31909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14210
  · exact u14211
  · exact u14212
  · exact u14213

def r31910 : Route 9 := (fun mask => (mask,id))

def c31910 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31910 : Upper (D 6) (R 6) [10,48,96,129,320] 13 := by
  apply FastRouting.sound _ _ [10,48,96,129,320] 13 (by decide) (choices 1) [1,2,4] r31910 c31910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14214
  · exact u14215
  · exact u14216

def b31911 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 50 100 140 19 357 325 453 325), lower := (rows 11 50 100 140 19 32 64 128 256), losses := [] }

theorem u31911 : Upper (D 6) (R 6) [10,48,96,132,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31912 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 354, targets := 4 }], pairs := [(0,5),(1,2),(3,5)], upper := (rows 11 50 100 140 21 355 323 451 323), lower := (rows 11 50 100 140 21 32 64 128 256), losses := [{ target := 5, region := (rows 3 2 4 24 16 0 67 131 259), good := (rows 459 475 68 140 477 0 64 128 256) }] }

theorem u31912 : Upper (D 6) (R 6) [10,48,96,132,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31913 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 100 140 22 353 321 449 321), lower := (rows 11 50 100 140 22 32 64 128 256), losses := [] }

theorem u31913 : Upper (D 6) (R 6) [10,48,96,132,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31914 : Route 9 := (fun mask => (mask,id))

def c31914 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31914 : Upper (D 6) (R 6) [10,48,96,132,65] 13 := by
  apply FastRouting.sound _ _ [10,48,96,132,65] 13 (by decide) (choices 1) [1,2,4,256] r31914 c31914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14217
  · exact u14218
  · exact u14219
  · exact u14220

def b31915 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 100 140 82 293 325 389 261), lower := (rows 11 50 100 140 82 32 64 128 256), losses := [] }

theorem u31915 : Upper (D 6) (R 6) [10,48,96,132,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31916 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 140 84 291 323 387 259), lower := (rows 11 50 100 140 84 32 64 128 256), losses := [] }

theorem u31916 : Upper (D 6) (R 6) [10,48,96,132,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31917 : Route 9 := (fun mask => (mask,id))

def c31917 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31917 : Upper (D 6) (R 6) [10,48,96,132,257] 13 := by
  apply FastRouting.sound _ _ [10,48,96,132,257] 13 (by decide) (choices 1) [1,2,4,64] r31917 c31917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u14221
  · exact u14222
  · exact u14223
  · exact u14224

def r31918 : Route 9 := (fun mask => (mask,id))

def c31918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31918 : Upper (D 6) (R 6) [10,48,96,132,258] 13 := by
  apply FastRouting.sound _ _ [10,48,96,132,258] 13 (by decide) (choices 1) [1,4,64] r31918 c31918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14225
  · exact u14226
  · exact u14227

def r31919 : Route 9 := (fun mask => (mask,id))

def c31919 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31919 : Upper (D 6) (R 6) [10,48,96,132,260] 13 := by
  apply FastRouting.sound _ _ [10,48,96,132,260] 13 (by decide) (choices 1) [1,2,64] r31919 c31919
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u14228
  · exact u14229
  · exact u14230

#print axioms u31919
end Delivery.IrregularNine14.P06
