import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0129

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24900 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 261 44 88 33 86 150 278), lower := (rows 35 194 261 44 88 33 64 128 256), losses := [] }

theorem u24900 : Upper (D 6) (R 6) [34,192,257,36,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24901 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 261 44 88 34 85 149 277), lower := (rows 35 194 261 44 88 34 64 128 256), losses := [] }

theorem u24901 : Upper (D 6) (R 6) [34,192,257,36,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24902 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 194 261 44 88 36 83 147 275), lower := (rows 35 194 261 44 88 36 64 128 256), losses := [] }

theorem u24902 : Upper (D 6) (R 6) [34,192,257,36,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24903 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 261 44 88 48 71 135 263), lower := (rows 35 194 261 44 88 48 64 128 256), losses := [] }

theorem u24903 : Upper (D 6) (R 6) [34,192,257,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24903 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24904 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 261 56 81 34 76 140 268), lower := (rows 35 194 261 56 81 34 64 128 256), losses := [] }

theorem u24904 : Upper (D 6) (R 6) [34,192,257,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24905 : Route 9 := (fun mask => (mask,id))

def c24905 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24905 : Upper (D 6) (R 6) [34,192,257,48,65,4] 13 := by
  apply FastRouting.sound _ _ [34,192,257,48,65,4] 13 (by decide) (choices 1) [2,4,8] r24905 c24905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7742
  · exact u7743
  · exact u7744

def b24906 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 194 261 56 81 40 70 134 262), lower := (rows 35 194 261 56 81 40 64 128 256), losses := [] }

theorem u24906 : Upper (D 6) (R 6) [34,192,257,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24906 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24907 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(3,1)], upper := (rows 35 194 261 56 84 33 78 142 270), lower := (rows 35 194 261 56 84 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 64 128 256), good := (rows 33 192 293 56 124 33 64 128 256) }] }

theorem u24907 : Upper (D 6) (R 6) [34,192,257,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24908 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 194 261 56 84 34 77 141 269), lower := (rows 35 194 261 56 84 34 64 128 256), losses := [] }

theorem u24908 : Upper (D 6) (R 6) [34,192,257,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24909 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 194 261 56 84 36 75 139 267), lower := (rows 35 194 261 56 84 36 64 128 256), losses := [] }

theorem u24909 : Upper (D 6) (R 6) [34,192,257,48,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24910 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 194 261 56 84 40 71 135 263), lower := (rows 35 194 261 56 84 40 64 128 256), losses := [] }

theorem u24910 : Upper (D 6) (R 6) [34,192,257,48,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24910 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24911 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 262 13 52 33 88 216 344), lower := (rows 35 194 262 13 52 33 64 128 256), losses := [] }

theorem u24911 : Upper (D 6) (R 6) [34,192,258,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24912 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 194 262 13 52 40 81 209 337), lower := (rows 35 194 262 13 52 40 64 128 256), losses := [] }

theorem u24912 : Upper (D 6) (R 6) [34,192,258,5,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24912 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24913 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 262 13 52 48 73 201 329), lower := (rows 35 194 262 13 52 48 64 128 256), losses := [] }

theorem u24913 : Upper (D 6) (R 6) [34,192,258,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24913 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24914 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 262 13 52 96 89 153 281), lower := (rows 35 194 262 13 52 96 64 128 256), losses := [] }

theorem u24914 : Upper (D 6) (R 6) [34,192,258,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24915 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 262 13 56 33 84 212 340), lower := (rows 35 194 262 13 56 33 64 128 256), losses := [] }

theorem u24915 : Upper (D 6) (R 6) [34,192,258,5,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24916 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 262 13 56 36 81 209 337), lower := (rows 35 194 262 13 56 36 64 128 256), losses := [] }

theorem u24916 : Upper (D 6) (R 6) [34,192,258,5,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24917 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 262 13 56 48 69 197 325), lower := (rows 35 194 262 13 56 48 64 128 256), losses := [] }

theorem u24917 : Upper (D 6) (R 6) [34,192,258,5,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24917 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24918 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 262 13 56 96 85 149 277), lower := (rows 35 194 262 13 56 96 64 128 256), losses := [] }

theorem u24918 : Upper (D 6) (R 6) [34,192,258,5,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24919 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 112, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 35 194 262 13 81 36 120 184 312), lower := (rows 35 194 262 13 81 36 64 128 256), losses := [] }

theorem u24919 : Upper (D 6) (R 6) [34,192,258,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24920 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 194 262 13 81 40 116 180 308), lower := (rows 35 194 262 13 81 40 64 128 256), losses := [] }

theorem u24920 : Upper (D 6) (R 6) [34,192,258,5,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24920 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24921 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 262 13 81 48 108 172 300), lower := (rows 35 194 262 13 81 48 64 128 256), losses := [] }

theorem u24921 : Upper (D 6) (R 6) [34,192,258,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24921 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24922 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 194 262 13 84 33 120 184 312), lower := (rows 35 194 262 13 84 33 64 128 256), losses := [] }

theorem u24922 : Upper (D 6) (R 6) [34,192,258,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24923 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 194 262 13 84 40 113 177 305), lower := (rows 35 194 262 13 84 40 64 128 256), losses := [] }

theorem u24923 : Upper (D 6) (R 6) [34,192,258,5,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24923 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24924 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 262 13 84 48 105 169 297), lower := (rows 35 194 262 13 84 48 64 128 256), losses := [] }

theorem u24924 : Upper (D 6) (R 6) [34,192,258,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24924 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24925 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 194 262 13 88 33 116 180 308), lower := (rows 35 194 262 13 88 33 64 128 256), losses := [] }

theorem u24925 : Upper (D 6) (R 6) [34,192,258,5,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24926 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 112, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 35 194 262 13 88 36 113 177 305), lower := (rows 35 194 262 13 88 36 64 128 256), losses := [] }

theorem u24926 : Upper (D 6) (R 6) [34,192,258,5,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24927 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 262 13 88 48 101 165 293), lower := (rows 35 194 262 13 88 48 64 128 256), losses := [] }

theorem u24927 : Upper (D 6) (R 6) [34,192,258,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24927 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24928 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 262 13 112 33 92 156 284), lower := (rows 35 194 262 13 112 33 64 128 256), losses := [] }

theorem u24928 : Upper (D 6) (R 6) [34,192,258,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24929 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 41, targets := 64 },{ cop := 3, region := 112, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 35 194 262 13 112 36 89 153 281), lower := (rows 35 194 262 13 112 36 64 128 256), losses := [] }

theorem u24929 : Upper (D 6) (R 6) [34,192,258,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24930 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 194 262 13 112 40 85 149 277), lower := (rows 35 194 262 13 112 40 64 128 256), losses := [] }

theorem u24930 : Upper (D 6) (R 6) [34,192,258,5,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24930 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24931 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 262 13 112 48 77 141 269), lower := (rows 35 194 262 13 112 48 64 128 256), losses := [] }

theorem u24931 : Upper (D 6) (R 6) [34,192,258,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24931 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24932 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 262 25 28 33 100 228 356), lower := (rows 35 194 262 25 28 33 64 128 256), losses := [] }

theorem u24932 : Upper (D 6) (R 6) [34,192,258,17,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24933 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 262 25 28 36 97 225 353), lower := (rows 35 194 262 25 28 36 64 128 256), losses := [] }

theorem u24933 : Upper (D 6) (R 6) [34,192,258,17,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24934 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 262 25 28 96 101 165 293), lower := (rows 35 194 262 25 28 96 64 128 256), losses := [] }

theorem u24934 : Upper (D 6) (R 6) [34,192,258,17,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24935 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 262 25 52 33 76 204 332), lower := (rows 35 194 262 25 52 33 64 128 256), losses := [] }

theorem u24935 : Upper (D 6) (R 6) [34,192,258,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24936 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 262 25 52 36 73 201 329), lower := (rows 35 194 262 25 52 36 64 128 256), losses := [] }

theorem u24936 : Upper (D 6) (R 6) [34,192,258,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24937 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 194 262 25 52 40 69 197 325), lower := (rows 35 194 262 25 52 40 64 128 256), losses := [] }

theorem u24937 : Upper (D 6) (R 6) [34,192,258,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24937 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24938 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 262 25 52 96 77 141 269), lower := (rows 35 194 262 25 52 96 64 128 256), losses := [] }

theorem u24938 : Upper (D 6) (R 6) [34,192,258,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24939 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 194 262 25 84 33 108 172 300), lower := (rows 35 194 262 25 84 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 24 16 63 64 128 256), good := (rows 35 227 291 57 121 33 64 128 256) }] }

theorem u24939 : Upper (D 6) (R 6) [34,192,258,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24940 : Route 9 := (fun mask => (mask,id))

def c24940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24940 : Upper (D 6) (R 6) [34,192,258,17,68,4] 13 := by
  apply FastRouting.sound _ _ [34,192,258,17,68,4] 13 (by decide) (choices 1) [1,8,32] r24940 c24940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7745
  · exact u7746
  · exact u7747

def r24941 : Route 9 := (fun mask => (mask,id))

def c24941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24941 : Upper (D 6) (R 6) [34,192,258,17,68,8] 13 := by
  apply FastRouting.sound _ _ [34,192,258,17,68,8] 13 (by decide) (choices 1) [1,4,32] r24941 c24941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7748
  · exact u7749
  · exact u7750

def b24942 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 194 262 25 88 33 100 164 292), lower := (rows 35 194 262 25 88 33 64 128 256), losses := [] }

theorem u24942 : Upper (D 6) (R 6) [34,192,258,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24943 : Route 9 := (fun mask => (mask,id))

def c24943 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24943 : Upper (D 6) (R 6) [34,192,258,17,72,4] 13 := by
  apply FastRouting.sound _ _ [34,192,258,17,72,4] 13 (by decide) (choices 1) [1,4,32] r24943 c24943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7751
  · exact u7752
  · exact u7753

def b24944 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 262 25 112 33 76 140 268), lower := (rows 35 194 262 25 112 33 64 128 256), losses := [] }

theorem u24944 : Upper (D 6) (R 6) [34,192,258,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24945 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 194 262 25 112 36 77 141 269), lower := (rows 35 194 262 25 112 36 64 128 256), losses := [] }

theorem u24945 : Upper (D 6) (R 6) [34,192,258,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24946 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 194 262 25 112 40 69 133 261), lower := (rows 35 194 262 25 112 40 64 128 256), losses := [] }

theorem u24946 : Upper (D 6) (R 6) [34,192,258,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24946 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24947 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 262 28 56 33 69 197 325), lower := (rows 35 194 262 28 56 33 64 128 256), losses := [] }

theorem u24947 : Upper (D 6) (R 6) [34,192,258,20,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24948 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 24, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 194 262 28 56 36 65 193 321), lower := (rows 35 194 262 28 56 36 64 128 256), losses := [] }

theorem u24948 : Upper (D 6) (R 6) [34,192,258,20,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24949 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 194 262 28 56 96 69 133 261), lower := (rows 35 194 262 28 56 96 64 128 256), losses := [] }

theorem u24949 : Upper (D 6) (R 6) [34,192,258,20,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24950 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 262 28 81 33 108 172 300), lower := (rows 35 194 262 28 81 33 64 128 256), losses := [] }

theorem u24950 : Upper (D 6) (R 6) [34,192,258,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24951 : Route 9 := (fun mask => (mask,id))

def c24951 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24951 : Upper (D 6) (R 6) [34,192,258,20,65,4] 13 := by
  apply FastRouting.sound _ _ [34,192,258,20,65,4] 13 (by decide) (choices 1) [1,8,32] r24951 c24951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7754
  · exact u7755
  · exact u7756

def b24952 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 260, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 194 262 28 81 40 101 165 293), lower := (rows 35 194 262 28 81 40 64 128 256), losses := [{ target := 6, region := (rows 1 2 5 24 16 56 0 145 273), good := (rows 423 130 262 444 445 40 0 128 256) }] }

theorem u24952 : Upper (D 6) (R 6) [34,192,258,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24952 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24953 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 293, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 262 28 88 33 101 165 293), lower := (rows 35 194 262 28 88 33 64 128 256), losses := [] }

theorem u24953 : Upper (D 6) (R 6) [34,192,258,20,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24954 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 293, targets := 64 },{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 194 262 28 88 36 97 161 289), lower := (rows 35 194 262 28 88 36 64 128 256), losses := [] }

theorem u24954 : Upper (D 6) (R 6) [34,192,258,20,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24955 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 262 28 112 33 77 141 269), lower := (rows 35 194 262 28 112 33 64 128 256), losses := [] }

theorem u24955 : Upper (D 6) (R 6) [34,192,258,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24956 : Route 9 := (fun mask => (mask,id))

def c24956 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24956 : Upper (D 6) (R 6) [34,192,258,20,96,4] 13 := by
  apply FastRouting.sound _ _ [34,192,258,20,96,4] 13 (by decide) (choices 1) [1,8] r24956 c24956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7757
  · exact u7758

def b24957 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 194 262 28 112 40 69 133 261), lower := (rows 35 194 262 28 112 40 64 128 256), losses := [] }

theorem u24957 : Upper (D 6) (R 6) [34,192,258,20,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24957 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24958 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 194 262 44 81 33 92 156 284), lower := (rows 35 194 262 44 81 33 64 128 256), losses := [] }

theorem u24958 : Upper (D 6) (R 6) [34,192,258,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24959 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 194 262 44 81 36 89 153 281), lower := (rows 35 194 262 44 81 36 64 128 256), losses := [] }

theorem u24959 : Upper (D 6) (R 6) [34,192,258,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24959
end Delivery.IrregularNine14.P06
