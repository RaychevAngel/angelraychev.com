import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0099

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19800 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 280 112 33 70 134 262), lower := (rows 35 67 140 280 112 33 64 128 256), losses := [] }

theorem u19800 : Upper (D 6) (R 6) [34,65,136,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19801 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 280 112 34 69 133 261), lower := (rows 35 67 140 280 112 34 64 128 256), losses := [] }

theorem u19801 : Upper (D 6) (R 6) [34,65,136,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m19802_1 : Upper (D 6) (R 6) [34,65,136,272,96,4,1] 13 :=
  permutation_upper _ _ _ [34,65,136,272,96,2,4] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5941

theorem m19802_2 : Upper (D 6) (R 6) [34,65,136,272,96,4,2] 13 :=
  permutation_upper _ _ _ [34,65,136,272,96,1,4] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5940

def r19802 : Route 9 := (fun mask => (mask,id))

def c19802 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19802 : Upper (D 6) (R 6) [34,65,136,272,96,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272,96,4] 13 (by decide) (choices 1) [1,2,4] r19802 c19802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m19802_1
  · exact m19802_2
  · exact u5942

def b19803 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 296 21 34 84 212 340), lower := (rows 35 67 140 296 21 34 64 128 256), losses := [] }

theorem u19803 : Upper (D 6) (R 6) [34,65,136,288,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19804 : Route 9 := (fun mask => (mask,id))

def c19804 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19804 : Upper (D 6) (R 6) [34,65,136,288,5,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,5,4] 13 (by decide) (choices 1) [2,16] r19804 c19804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5943
  · exact u5944

def b19805 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 140 296 21 48 70 198 326), lower := (rows 35 67 140 296 21 48 64 128 256), losses := [] }

theorem u19805 : Upper (D 6) (R 6) [34,65,136,288,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19805 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19806 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 296 21 96 86 150 278), lower := (rows 35 67 140 296 21 96 64 128 256), losses := [] }

theorem u19806 : Upper (D 6) (R 6) [34,65,136,288,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19807 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 296 22 33 84 212 340), lower := (rows 35 67 140 296 22 33 64 128 256), losses := [] }

theorem u19807 : Upper (D 6) (R 6) [34,65,136,288,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19808 : Route 9 := (fun mask => (mask,id))

def c19808 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19808 : Upper (D 6) (R 6) [34,65,136,288,6,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,6,4] 13 (by decide) (choices 1) [1,16] r19808 c19808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5945
  · exact u5946

def b19809 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 140 296 22 48 69 197 325), lower := (rows 35 67 140 296 22 48 64 128 256), losses := [] }

theorem u19809 : Upper (D 6) (R 6) [34,65,136,288,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19809 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19810 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 140 296 22 96 85 149 277), lower := (rows 35 67 140 296 22 96 64 128 256), losses := [] }

theorem u19810 : Upper (D 6) (R 6) [34,65,136,288,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19811 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 296 84 33 86 150 278), lower := (rows 35 67 140 296 84 33 64 128 256), losses := [] }

theorem u19811 : Upper (D 6) (R 6) [34,65,136,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19812 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 296 84 34 85 149 277), lower := (rows 35 67 140 296 84 34 64 128 256), losses := [] }

theorem u19812 : Upper (D 6) (R 6) [34,65,136,288,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19813 : Route 9 := (fun mask => (mask,id))

def c19813 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19813 : Upper (D 6) (R 6) [34,65,136,288,68,4] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,68,4] 13 (by decide) (choices 1) [1,2,16] r19813 c19813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5947
  · exact u5948
  · exact u5949

def b19814 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 140 296 84 48 71 135 263), lower := (rows 35 67 140 296 84 48 64 128 256), losses := [] }

theorem u19814 : Upper (D 6) (R 6) [34,65,136,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19814 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19815 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 164 13 22 40 336 464 336), lower := (rows 35 67 164 13 22 40 64 128 256), losses := [] }

theorem u19815 : Upper (D 6) (R 6) [34,65,160,5,6,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19815 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19816 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 164 13 22 48 328 456 328), lower := (rows 35 67 164 13 22 48 64 128 256), losses := [] }

theorem u19816 : Upper (D 6) (R 6) [34,65,160,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19816 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19817 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 13 22 96 344 408 280), lower := (rows 35 67 164 13 22 96 64 128 256), losses := [] }

theorem u19817 : Upper (D 6) (R 6) [34,65,160,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19818 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 82, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 67 164 13 22 288 88 216 344), lower := (rows 35 67 164 13 22 288 64 128 256), losses := [] }

theorem u19818 : Upper (D 6) (R 6) [34,65,160,5,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19818 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19819 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 13 84 34 344 408 280), lower := (rows 35 67 164 13 84 34 64 128 256), losses := [] }

theorem u19819 : Upper (D 6) (R 6) [34,65,160,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19820 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 164 13 84 40 338 402 274), lower := (rows 35 67 164 13 84 40 64 128 256), losses := [] }

theorem u19820 : Upper (D 6) (R 6) [34,65,160,5,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19820 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19821 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 164 13 84 48 330 394 266), lower := (rows 35 67 164 13 84 48 64 128 256), losses := [] }

theorem u19821 : Upper (D 6) (R 6) [34,65,160,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19821 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19822 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 82, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 67 164 13 84 288 90 154 282), lower := (rows 35 67 164 13 84 288 64 128 256), losses := [] }

theorem u19822 : Upper (D 6) (R 6) [34,65,160,5,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19822 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19823 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 13 88 34 340 404 276), lower := (rows 35 67 164 13 88 34 64 128 256), losses := [] }

theorem u19823 : Upper (D 6) (R 6) [34,65,160,5,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19823 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19824 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 67 164 13 88 36 338 402 274), lower := (rows 35 67 164 13 88 36 64 128 256), losses := [] }

theorem u19824 : Upper (D 6) (R 6) [34,65,160,5,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19824 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19825 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 164 13 88 48 326 390 262), lower := (rows 35 67 164 13 88 48 64 128 256), losses := [] }

theorem u19825 : Upper (D 6) (R 6) [34,65,160,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19825 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19826 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 82, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 67 164 13 88 288 86 150 278), lower := (rows 35 67 164 13 88 288 64 128 256), losses := [] }

theorem u19826 : Upper (D 6) (R 6) [34,65,160,5,72,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19826 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19827 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 67 164 13 274 36 88 216 344), lower := (rows 35 67 164 13 274 36 64 128 256), losses := [] }

theorem u19827 : Upper (D 6) (R 6) [34,65,160,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19827 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19828 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 164 13 274 40 84 212 340), lower := (rows 35 67 164 13 274 40 64 128 256), losses := [] }

theorem u19828 : Upper (D 6) (R 6) [34,65,160,5,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19828 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19829 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 164 13 274 48 76 204 332), lower := (rows 35 67 164 13 274 48 64 128 256), losses := [] }

theorem u19829 : Upper (D 6) (R 6) [34,65,160,5,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19829 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19830 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 13 274 96 92 156 284), lower := (rows 35 67 164 13 274 96 64 128 256), losses := [] }

theorem u19830 : Upper (D 6) (R 6) [34,65,160,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19830 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19831 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 13 276 34 88 216 344), lower := (rows 35 67 164 13 276 34 64 128 256), losses := [] }

theorem u19831 : Upper (D 6) (R 6) [34,65,160,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19831 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19832 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 164 13 276 40 82 210 338), lower := (rows 35 67 164 13 276 40 64 128 256), losses := [] }

theorem u19832 : Upper (D 6) (R 6) [34,65,160,5,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19832 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19833 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 338, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 67 164 13 276 48 74 202 330), lower := (rows 35 67 164 13 276 48 64 128 256), losses := [] }

theorem u19833 : Upper (D 6) (R 6) [34,65,160,5,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19833 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19834 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 13 276 96 90 154 282), lower := (rows 35 67 164 13 276 96 64 128 256), losses := [] }

theorem u19834 : Upper (D 6) (R 6) [34,65,160,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19834 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19835 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 13 280 34 84 212 340), lower := (rows 35 67 164 13 280 34 64 128 256), losses := [] }

theorem u19835 : Upper (D 6) (R 6) [34,65,160,5,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19835 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19836 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 67 164 13 280 36 82 210 338), lower := (rows 35 67 164 13 280 36 64 128 256), losses := [] }

theorem u19836 : Upper (D 6) (R 6) [34,65,160,5,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19836 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19837 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 338, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 67 164 13 280 48 70 198 326), lower := (rows 35 67 164 13 280 48 64 128 256), losses := [] }

theorem u19837 : Upper (D 6) (R 6) [34,65,160,5,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19837 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19838 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 13 280 96 86 150 278), lower := (rows 35 67 164 13 280 96 64 128 256), losses := [] }

theorem u19838 : Upper (D 6) (R 6) [34,65,160,5,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19838 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19839 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 13 336 34 92 156 284), lower := (rows 35 67 164 13 336 34 64 128 256), losses := [] }

theorem u19839 : Upper (D 6) (R 6) [34,65,160,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19839 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19840 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 338, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 67 164 13 336 36 90 154 282), lower := (rows 35 67 164 13 336 36 64 128 256), losses := [] }

theorem u19840 : Upper (D 6) (R 6) [34,65,160,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19841 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 164 13 336 40 86 150 278), lower := (rows 35 67 164 13 336 40 64 128 256), losses := [] }

theorem u19841 : Upper (D 6) (R 6) [34,65,160,5,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19841 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19842 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 164 13 336 48 78 142 270), lower := (rows 35 67 164 13 336 48 64 128 256), losses := [] }

theorem u19842 : Upper (D 6) (R 6) [34,65,160,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19842 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19843 : PairBound 9 := { available := 336, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 14 25 36 336 464 336), lower := (rows 35 67 164 14 25 36 64 128 256), losses := [] }

theorem u19843 : Upper (D 6) (R 6) [34,65,160,6,9,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19844 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 67 164 14 25 48 324 452 324), lower := (rows 35 67 164 14 25 48 64 128 256), losses := [] }

theorem u19844 : Upper (D 6) (R 6) [34,65,160,6,9,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19844 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19845 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 14 25 96 340 404 276), lower := (rows 35 67 164 14 25 96 64 128 256), losses := [] }

theorem u19845 : Upper (D 6) (R 6) [34,65,160,6,9,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19846 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 484, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 164 14 25 288 84 212 340), lower := (rows 35 67 164 14 25 288 64 128 256), losses := [] }

theorem u19846 : Upper (D 6) (R 6) [34,65,160,6,9,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19846 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19847 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 14 84 33 344 408 280), lower := (rows 35 67 164 14 84 33 64 128 256), losses := [] }

theorem u19847 : Upper (D 6) (R 6) [34,65,160,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19848 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 164 14 84 40 337 401 273), lower := (rows 35 67 164 14 84 40 64 128 256), losses := [] }

theorem u19848 : Upper (D 6) (R 6) [34,65,160,6,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19848 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19849 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 164 14 84 48 329 393 265), lower := (rows 35 67 164 14 84 48 64 128 256), losses := [] }

theorem u19849 : Upper (D 6) (R 6) [34,65,160,6,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19849 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19850 : Route 9 := (fun mask => (mask,id))

def c19850 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19850 : Upper (D 6) (R 6) [34,65,160,6,68,256] 13 := by
  apply FastRouting.sound _ _ [34,65,160,6,68,256] 13 (by decide) (choices 1) [1,8,16] r19850 c19850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5950
  · exact u5951
  · exact u5952

def b19851 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 14 88 33 340 404 276), lower := (rows 35 67 164 14 88 33 64 128 256), losses := [] }

theorem u19851 : Upper (D 6) (R 6) [34,65,160,6,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19852 : PairBound 9 := { available := 273, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 14 88 36 337 401 273), lower := (rows 35 67 164 14 88 36 64 128 256), losses := [] }

theorem u19852 : Upper (D 6) (R 6) [34,65,160,6,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19853 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 164 14 88 48 325 389 261), lower := (rows 35 67 164 14 88 48 64 128 256), losses := [] }

theorem u19853 : Upper (D 6) (R 6) [34,65,160,6,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19853 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19854 : Route 9 := (fun mask => (mask,id))

def c19854 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19854 : Upper (D 6) (R 6) [34,65,160,6,72,256] 13 := by
  apply FastRouting.sound _ _ [34,65,160,6,72,256] 13 (by decide) (choices 1) [1,4,16] r19854 c19854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5953
  · exact u5954
  · exact u5955

def b19855 : PairBound 9 := { available := 88, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 14 273 36 88 216 344), lower := (rows 35 67 164 14 273 36 64 128 256), losses := [] }

theorem u19855 : Upper (D 6) (R 6) [34,65,160,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19856 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 164 14 273 40 84 212 340), lower := (rows 35 67 164 14 273 40 64 128 256), losses := [] }

theorem u19856 : Upper (D 6) (R 6) [34,65,160,6,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19856 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19857 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 164 14 273 48 76 204 332), lower := (rows 35 67 164 14 273 48 64 128 256), losses := [] }

theorem u19857 : Upper (D 6) (R 6) [34,65,160,6,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19857 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19858 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 14 273 96 92 156 284), lower := (rows 35 67 164 14 273 96 64 128 256), losses := [] }

theorem u19858 : Upper (D 6) (R 6) [34,65,160,6,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19858 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19859 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 14 276 33 88 216 344), lower := (rows 35 67 164 14 276 33 64 128 256), losses := [] }

theorem u19859 : Upper (D 6) (R 6) [34,65,160,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u19859
end Delivery.IrregularNine14.P06
