import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0121

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23760 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 70 25 276 33 100 228 356), lower := (rows 35 138 70 25 276 33 64 128 256), losses := [] }

theorem u23760 : Upper (D 6) (R 6) [34,136,66,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23761 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,2),(3,6)], upper := (rows 35 138 70 25 276 36 97 225 353), lower := (rows 35 138 70 25 276 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 32 65 129 257), good := (rows 483 138 66 475 272 32 64 128 256) },{ target := 6, region := (rows 5 2 4 24 16 52 0 128 256), good := (rows 35 138 39 57 317 37 0 128 256) }] }

theorem u23761 : Upper (D 6) (R 6) [34,136,66,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23762 : Route 9 := (fun mask => (mask,id))

def c23762 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23762 : Upper (D 6) (R 6) [34,136,66,17,260,64] 13 := by
  apply FastRouting.sound _ _ [34,136,66,17,260,64] 13 (by decide) (choices 1) [1,4,32] r23762 c23762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7298
  · exact u7299
  · exact u7300

def b23763 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 138 70 25 304 33 68 196 324), lower := (rows 35 138 70 25 304 33 64 128 256), losses := [] }

theorem u23763 : Upper (D 6) (R 6) [34,136,66,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23764 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 198, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 138 70 25 304 36 69 197 325), lower := (rows 35 138 70 25 304 36 64 128 256), losses := [] }

theorem u23764 : Upper (D 6) (R 6) [34,136,66,17,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23765 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 198, targets := 32 },{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 138 70 25 304 96 69 133 261), lower := (rows 35 138 70 25 304 96 64 128 256), losses := [] }

theorem u23765 : Upper (D 6) (R 6) [34,136,66,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23766 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 70 25 336 33 100 164 292), lower := (rows 35 138 70 25 336 33 64 128 256), losses := [] }

theorem u23766 : Upper (D 6) (R 6) [34,136,66,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23767 : Route 9 := (fun mask => (mask,id))

def c23767 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23767 : Upper (D 6) (R 6) [34,136,66,17,320,4] 13 := by
  apply FastRouting.sound _ _ [34,136,66,17,320,4] 13 (by decide) (choices 1) [1,4,32] r23767 c23767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7301
  · exact u7302
  · exact u7303

def b23768 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 70 44 81 33 340 404 276), lower := (rows 35 138 70 44 81 33 64 128 256), losses := [] }

theorem u23768 : Upper (D 6) (R 6) [34,136,66,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23769 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 138 70 44 81 36 337 401 273), lower := (rows 35 138 70 44 81 36 64 128 256), losses := [] }

theorem u23769 : Upper (D 6) (R 6) [34,136,66,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23770 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 138 70 44 81 48 325 389 261), lower := (rows 35 138 70 44 81 48 64 128 256), losses := [] }

theorem u23770 : Upper (D 6) (R 6) [34,136,66,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23770 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23771 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 138 70 44 81 288 85 149 277), lower := (rows 35 138 70 44 81 288 64 128 256), losses := [] }

theorem u23771 : Upper (D 6) (R 6) [34,136,66,36,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23771 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23772 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 70 44 273 33 84 212 340), lower := (rows 35 138 70 44 273 33 64 128 256), losses := [] }

theorem u23772 : Upper (D 6) (R 6) [34,136,66,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23773 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 138 70 44 273 36 81 209 337), lower := (rows 35 138 70 44 273 36 64 128 256), losses := [] }

theorem u23773 : Upper (D 6) (R 6) [34,136,66,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23774 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 138 70 44 273 48 69 197 325), lower := (rows 35 138 70 44 273 48 64 128 256), losses := [] }

theorem u23774 : Upper (D 6) (R 6) [34,136,66,36,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23774 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23775 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 138 70 44 273 96 85 149 277), lower := (rows 35 138 70 44 273 96 64 128 256), losses := [] }

theorem u23775 : Upper (D 6) (R 6) [34,136,66,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23776 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 70 44 276 33 81 209 337), lower := (rows 35 138 70 44 276 33 64 128 256), losses := [] }

theorem u23776 : Upper (D 6) (R 6) [34,136,66,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23777 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 138 70 44 276 48 65 193 321), lower := (rows 35 138 70 44 276 48 64 128 256), losses := [] }

theorem u23777 : Upper (D 6) (R 6) [34,136,66,36,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23777 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23778 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 138 70 44 276 96 81 145 273), lower := (rows 35 138 70 44 276 96 64 128 256), losses := [] }

theorem u23778 : Upper (D 6) (R 6) [34,136,66,36,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23779 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 70 44 336 33 85 149 277), lower := (rows 35 138 70 44 336 33 64 128 256), losses := [] }

theorem u23779 : Upper (D 6) (R 6) [34,136,66,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23780 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 138 70 44 336 36 81 145 273), lower := (rows 35 138 70 44 336 36 64 128 256), losses := [] }

theorem u23780 : Upper (D 6) (R 6) [34,136,66,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23781 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 138 70 44 336 48 69 133 261), lower := (rows 35 138 70 44 336 48 64 128 256), losses := [] }

theorem u23781 : Upper (D 6) (R 6) [34,136,66,36,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23781 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23782 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 70 56 276 33 69 197 325), lower := (rows 35 138 70 56 276 33 64 128 256), losses := [] }

theorem u23782 : Upper (D 6) (R 6) [34,136,66,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23783 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 138 70 56 276 36 65 193 321), lower := (rows 35 138 70 56 276 36 64 128 256), losses := [] }

theorem u23783 : Upper (D 6) (R 6) [34,136,66,48,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23783 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23784 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 70 56 276 96 69 133 261), lower := (rows 35 138 70 56 276 96 64 128 256), losses := [] }

theorem u23784 : Upper (D 6) (R 6) [34,136,66,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23785 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 4, region := 360, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 35 138 70 265 21 36 112 240 368), lower := (rows 35 138 70 265 21 36 64 128 256), losses := [] }

theorem u23785 : Upper (D 6) (R 6) [34,136,66,257,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23786 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 138 70 265 21 48 100 228 356), lower := (rows 35 138 70 265 21 48 64 128 256), losses := [] }

theorem u23786 : Upper (D 6) (R 6) [34,136,66,257,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23786 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23787 : Route 9 := (fun mask => (mask,id))

def c23787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23787 : Upper (D 6) (R 6) [34,136,66,257,5,64] 13 := by
  apply FastRouting.sound _ _ [34,136,66,257,5,64] 13 (by decide) (choices 1) [4,16,32] r23787 c23787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7304
  · exact u7305
  · exact u7306

def b23788 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 70 265 52 33 84 212 340), lower := (rows 35 138 70 265 52 33 64 128 256), losses := [] }

theorem u23788 : Upper (D 6) (R 6) [34,136,66,257,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23789 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 70 265 52 36 81 209 337), lower := (rows 35 138 70 265 52 36 64 128 256), losses := [] }

theorem u23789 : Upper (D 6) (R 6) [34,136,66,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23790 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 70 265 52 48 69 197 325), lower := (rows 35 138 70 265 52 48 64 128 256), losses := [] }

theorem u23790 : Upper (D 6) (R 6) [34,136,66,257,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23790 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23791 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 70 265 52 96 85 149 277), lower := (rows 35 138 70 265 52 96 64 128 256), losses := [] }

theorem u23791 : Upper (D 6) (R 6) [34,136,66,257,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23792 : Route 9 := (fun mask => (mask,id))

def c23792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23792 : Upper (D 6) (R 6) [34,136,66,257,65,4] 13 := by
  apply FastRouting.sound _ _ [34,136,66,257,65,4] 13 (by decide) (choices 1) [4,16,32] r23792 c23792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7307
  · exact u7308
  · exact u7309

def b23793 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 49, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 138 70 265 81 48 100 164 292), lower := (rows 35 138 70 265 81 48 64 128 256), losses := [] }

theorem u23793 : Upper (D 6) (R 6) [34,136,66,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23793 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23794 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 70 265 112 33 84 148 276), lower := (rows 35 138 70 265 112 33 64 128 256), losses := [] }

theorem u23794 : Upper (D 6) (R 6) [34,136,66,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23795 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 138 70 265 112 36 85 149 277), lower := (rows 35 138 70 265 112 36 64 128 256), losses := [] }

theorem u23795 : Upper (D 6) (R 6) [34,136,66,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23796 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 70 265 112 48 69 133 261), lower := (rows 35 138 70 265 112 48 64 128 256), losses := [] }

theorem u23796 : Upper (D 6) (R 6) [34,136,66,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23796 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23797 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 68, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 138 70 280 21 33 100 228 356), lower := (rows 35 138 70 280 21 33 64 128 256), losses := [] }

theorem u23797 : Upper (D 6) (R 6) [34,136,66,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23798 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 4, region := 360, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 35 138 70 280 21 36 97 225 353), lower := (rows 35 138 70 280 21 36 64 128 256), losses := [] }

theorem u23798 : Upper (D 6) (R 6) [34,136,66,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23798 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m23799_1 : Upper (D 6) (R 6) [34,136,66,272,5,64,1] 13 :=
  permutation_upper _ _ _ [34,136,66,272,5,4,32] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7311

theorem m23799_4 : Upper (D 6) (R 6) [34,136,66,272,5,64,4] 13 :=
  permutation_upper _ _ _ [34,136,66,272,5,1,32] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7310

def r23799 : Route 9 := (fun mask => (mask,id))

def c23799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23799 : Upper (D 6) (R 6) [34,136,66,272,5,64] 13 := by
  apply FastRouting.sound _ _ [34,136,66,272,5,64] 13 (by decide) (choices 1) [1,4,32] r23799 c23799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m23799_1
  · exact m23799_4
  · exact u7312

def b23800 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 68, targets := 32 }], pairs := [(0,2),(0,6),(2,5)], upper := (rows 35 138 70 280 52 33 69 197 325), lower := (rows 35 138 70 280 52 33 64 128 256), losses := [] }

theorem u23800 : Upper (D 6) (R 6) [34,136,66,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23801 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 70 280 52 36 65 193 321), lower := (rows 35 138 70 280 52 36 64 128 256), losses := [] }

theorem u23801 : Upper (D 6) (R 6) [34,136,66,272,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23802 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 70 280 52 96 69 133 261), lower := (rows 35 138 70 280 52 96 64 128 256), losses := [] }

theorem u23802 : Upper (D 6) (R 6) [34,136,66,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23803 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 68, targets := 32 }], pairs := [(0,2),(0,6),(2,5)], upper := (rows 35 138 70 280 112 33 69 133 261), lower := (rows 35 138 70 280 112 33 64 128 256), losses := [] }

theorem u23803 : Upper (D 6) (R 6) [34,136,66,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23804 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 35 138 70 280 112 36 69 133 261), lower := (rows 35 138 70 280 112 36 64 128 256), losses := [] }

theorem u23804 : Upper (D 6) (R 6) [34,136,66,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23805 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 70 296 81 33 84 148 276), lower := (rows 35 138 70 296 81 33 64 128 256), losses := [] }

theorem u23805 : Upper (D 6) (R 6) [34,136,66,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23806 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 138 70 296 81 36 85 149 277), lower := (rows 35 138 70 296 81 36 64 128 256), losses := [] }

theorem u23806 : Upper (D 6) (R 6) [34,136,66,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23807 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 138 70 296 81 48 69 133 261), lower := (rows 35 138 70 296 81 48 64 128 256), losses := [] }

theorem u23807 : Upper (D 6) (R 6) [34,136,66,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23807 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23808 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 3, region := 483, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 84 13 22 33 352 480 352), lower := (rows 35 138 84 13 22 33 64 128 256), losses := [] }

theorem u23808 : Upper (D 6) (R 6) [34,136,80,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23809 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 483, targets := 4 }], pairs := [(0,2),(1,2),(1,6)], upper := (rows 35 138 84 13 22 96 353 417 289), lower := (rows 35 138 84 13 22 96 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 24 32 0 129 257), good := (rows 419 154 20 415 22 32 0 128 256) }] }

theorem u23809 : Upper (D 6) (R 6) [34,136,80,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23810 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 483, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 138 84 13 22 288 97 225 353), lower := (rows 35 138 84 13 22 288 64 128 256), losses := [] }

theorem u23810 : Upper (D 6) (R 6) [34,136,80,5,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23810 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23811 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 13 273 34 100 228 356), lower := (rows 35 138 84 13 273 34 64 128 256), losses := [] }

theorem u23811 : Upper (D 6) (R 6) [34,136,80,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23812 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 336, targets := 4 },{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0),(2,0),(4,2)], upper := (rows 35 138 84 13 273 36 98 226 354), lower := (rows 35 138 84 13 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 60 75 139 267), good := (rows 482 490 116 494 500 36 64 128 256) }] }

theorem u23812 : Upper (D 6) (R 6) [34,136,80,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23813 : Route 9 := (fun mask => (mask,id))

def c23813 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23813 : Upper (D 6) (R 6) [34,136,80,5,257,64] 13 := by
  apply FastRouting.sound _ _ [34,136,80,5,257,64] 13 (by decide) (choices 1) [2,4,32] r23813 c23813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7313
  · exact u7314
  · exact u7315

def b23814 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 84 13 274 33 100 228 356), lower := (rows 35 138 84 13 274 33 64 128 256), losses := [] }

theorem u23814 : Upper (D 6) (R 6) [34,136,80,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23815 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 336, targets := 4 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 35 138 84 13 274 36 97 225 353), lower := (rows 35 138 84 13 274 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 25 32 65 129 257), good := (rows 499 154 80 475 274 32 64 128 256) },{ target := 6, region := (rows 3 2 4 8 16 44 0 128 256), good := (rows 35 171 52 45 275 36 0 128 256) }] }

theorem u23815 : Upper (D 6) (R 6) [34,136,80,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23815 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23816 : Route 9 := (fun mask => (mask,id))

def c23816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23816 : Upper (D 6) (R 6) [34,136,80,5,258,64] 13 := by
  apply FastRouting.sound _ _ [34,136,80,5,258,64] 13 (by decide) (choices 1) [1,4,32] r23816 c23816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7316
  · exact u7317
  · exact u7318

def b23817 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 84 13 276 33 98 226 354), lower := (rows 35 138 84 13 276 33 64 128 256), losses := [] }

theorem u23817 : Upper (D 6) (R 6) [34,136,80,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23818 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 84 13 276 34 97 225 353), lower := (rows 35 138 84 13 276 34 64 128 256), losses := [] }

theorem u23818 : Upper (D 6) (R 6) [34,136,80,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23819 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(1,6)], upper := (rows 35 138 84 13 276 96 99 163 291), lower := (rows 35 138 84 13 276 96 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 24 32 0 129 257), good := (rows 419 154 20 415 276 32 0 128 256) }] }

theorem u23819 : Upper (D 6) (R 6) [34,136,80,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u23819
end Delivery.IrregularNine14.P06
