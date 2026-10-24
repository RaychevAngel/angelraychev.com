import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0169
import IrregularNine14P06C0170

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28860 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 84 104 145 295 327 391 263), lower := (rows 7 42 84 104 145 32 64 128 256), losses := [] }

theorem u28860 : Upper (D 6) (R 6) [6,40,80,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28860
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28861 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 84 104 146 293 325 389 261), lower := (rows 7 42 84 104 146 32 64 128 256), losses := [] }

theorem u28861 : Upper (D 6) (R 6) [6,40,80,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28861
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28862 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 84 104 148 291 323 387 259), lower := (rows 7 42 84 104 148 32 64 128 256), losses := [] }

theorem u28862 : Upper (D 6) (R 6) [6,40,80,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28862
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28863 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 84 104 400 39 71 135 263), lower := (rows 7 42 84 104 400 32 64 128 256), losses := [] }

theorem u28863 : Upper (D 6) (R 6) [6,40,80,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28863
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28864 : Route 9 := (fun mask => (mask,id))

def c28864 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28864 : Upper (D 6) (R 6) [6,40,80,129,257] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,257] 13 (by decide) (choices 1) [2,4,64] r28864 c28864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10151
  · exact u10152
  · exact u10153

def r28865 : Route 9 := (fun mask => (mask,id))

def c28865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28865 : Upper (D 6) (R 6) [6,40,80,129,258] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,258] 13 (by decide) (choices 1) [1,4,64] r28865 c28865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10154
  · exact u10155
  · exact u10156

def r28866 : Route 9 := (fun mask => (mask,id))

def c28866 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28866 : Upper (D 6) (R 6) [6,40,80,129,260] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,260] 13 (by decide) (choices 1) [1,2,64] r28866 c28866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10157
  · exact u10158
  · exact u10159

def r28867 : Route 9 := (fun mask => (mask,id))

def c28867 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28867 : Upper (D 6) (R 6) [6,40,80,129,288] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,288] 13 (by decide) (choices 1) [1,2,4,64] r28867 c28867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10160
  · exact u10161
  · exact u10162
  · exact u10163

def b28868 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 84 137 336 39 103 167 295), lower := (rows 7 42 84 137 336 32 64 128 256), losses := [] }

theorem u28868 : Upper (D 6) (R 6) [6,40,80,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28868
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28869 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 234, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 84 138 276 97 97 225 353), lower := (rows 7 42 84 138 276 32 64 128 256), losses := [] }

theorem u28869 : Upper (D 6) (R 6) [6,40,80,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28869
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28870 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 84 138 304 101 69 197 325), lower := (rows 7 42 84 138 304 32 64 128 256), losses := [] }

theorem u28870 : Upper (D 6) (R 6) [6,40,80,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28870
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28871 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 84 138 336 37 101 165 293), lower := (rows 7 42 84 138 336 32 64 128 256), losses := [] }

theorem u28871 : Upper (D 6) (R 6) [6,40,80,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28871
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28872 : Route 9 := (fun mask => (mask,id))

def c28872 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28872 : Upper (D 6) (R 6) [6,40,80,132,258] 13 := by
  apply FastRouting.sound _ _ [6,40,80,132,258] 13 (by decide) (choices 1) [1,64] r28872 c28872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10164
  · exact u10165

def r28873 : Route 9 := (fun mask => (mask,id))

def c28873 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28873 : Upper (D 6) (R 6) [6,40,80,132,288] 13 := by
  apply FastRouting.sound _ _ [6,40,80,132,288] 13 (by decide) (choices 1) [1,2,64] r28873 c28873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10166
  · exact u10167
  · exact u10168

def b28874 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 84 140 336 35 99 163 291), lower := (rows 7 42 84 140 336 32 64 128 256), losses := [] }

theorem u28874 : Upper (D 6) (R 6) [6,40,80,132,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28874
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28875 : Route 9 := (fun mask => (mask,id))

def c28875 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28875 : Upper (D 6) (R 6) [6,40,80,192,288] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,288] 13 (by decide) (choices 1) [1,2,4] r28875 c28875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10169
  · exact u10170
  · exact u10171

def b28876 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 42 100 25 19 484 452 452 452), lower := (rows 7 42 100 25 19 32 64 128 256), losses := [] }

theorem u28876 : Upper (D 6) (R 6) [6,40,96,17,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28876
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28877 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 24, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 7 42 100 25 21 482 450 450 450), lower := (rows 7 42 100 25 21 32 64 128 256), losses := [] }

theorem u28877 : Upper (D 6) (R 6) [6,40,96,17,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28877
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28878 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 25 22 481 449 449 449), lower := (rows 7 42 100 25 22 32 64 128 256), losses := [] }

theorem u28878 : Upper (D 6) (R 6) [6,40,96,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28878
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28879 : PairBound 9 := { available := 390, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 42 100 25 81 422 454 390 390), lower := (rows 7 42 100 25 81 32 64 128 256), losses := [] }

theorem u28879 : Upper (D 6) (R 6) [6,40,96,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28879
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28880 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 42 100 25 82 421 453 389 389), lower := (rows 7 42 100 25 82 32 64 128 256), losses := [] }

theorem u28880 : Upper (D 6) (R 6) [6,40,96,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28880
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28881 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 42 100 25 84 419 451 387 387), lower := (rows 7 42 100 25 84 32 64 128 256), losses := [] }

theorem u28881 : Upper (D 6) (R 6) [6,40,96,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28881
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28882 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 7 42 100 25 145 358 326 454 326), lower := (rows 7 42 100 25 145 32 64 128 256), losses := [] }

theorem u28882 : Upper (D 6) (R 6) [6,40,96,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28882
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28883 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 42 100 25 146 357 325 453 325), lower := (rows 7 42 100 25 146 32 64 128 256), losses := [] }

theorem u28883 : Upper (D 6) (R 6) [6,40,96,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28883
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28884 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 354, targets := 4 }], pairs := [(1,2),(3,5),(4,5)], upper := (rows 7 42 100 25 148 355 323 451 323), lower := (rows 7 42 100 25 148 32 64 128 256), losses := [] }

theorem u28884 : Upper (D 6) (R 6) [6,40,96,17,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28884
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28885 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(1,6),(3,5),(4,5)], upper := (rows 7 42 100 25 208 295 327 391 263), lower := (rows 7 42 100 25 208 32 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 16 33 0 129 257), good := (rows 423 42 36 443 144 32 0 128 256) }] }

theorem u28885 : Upper (D 6) (R 6) [6,40,96,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28885
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28886 : Route 9 := (fun mask => (mask,id))

def c28886 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28886 : Upper (D 6) (R 6) [6,40,96,17,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17,384] 13 (by decide) (choices 1) [1,2,4,64] r28886 c28886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10172
  · exact u10173
  · exact u10174
  · exact u10175

def b28887 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,2),(4,6)], upper := (rows 7 42 100 137 19 372 340 468 340), lower := (rows 7 42 100 137 19 32 64 128 256), losses := [] }

theorem u28887 : Upper (D 6) (R 6) [6,40,96,129,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28887
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28888 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,1),(4,6)], upper := (rows 7 42 100 137 21 370 338 466 338), lower := (rows 7 42 100 137 21 32 64 128 256), losses := [] }

theorem u28888 : Upper (D 6) (R 6) [6,40,96,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28888
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28889 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 7 42 100 137 22 369 337 465 337), lower := (rows 7 42 100 137 22 32 64 128 256), losses := [] }

theorem u28889 : Upper (D 6) (R 6) [6,40,96,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28889
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28890 : Route 9 := (fun mask => (mask,id))

def c28890 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28890 : Upper (D 6) (R 6) [6,40,96,129,65] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,65] 13 (by decide) (choices 1) [2,4,16,256] r28890 c28890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10176
  · exact u10177
  · exact u10178
  · exact u10179

def r28891 : Route 9 := (fun mask => (mask,id))

def c28891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28891 : Upper (D 6) (R 6) [6,40,96,129,66] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,66] 13 (by decide) (choices 1) [1,4,16,256] r28891 c28891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10180
  · exact u10181
  · exact u10182
  · exact u10183

def b28892 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 42 100 137 84 307 339 403 275), lower := (rows 7 42 100 137 84 32 64 128 256), losses := [] }

theorem u28892 : Upper (D 6) (R 6) [6,40,96,129,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28892
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28893 : Route 9 := (fun mask => (mask,id))

def c28893 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28893 : Upper (D 6) (R 6) [6,40,96,129,257] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,257] 13 (by decide) (choices 1) [2,4,16,64] r28893 c28893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10184
  · exact u10185
  · exact u10186
  · exact u10187

def r28894 : Route 9 := (fun mask => (mask,id))

def c28894 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28894 : Upper (D 6) (R 6) [6,40,96,129,258] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,258] 13 (by decide) (choices 1) [1,4,16,64] r28894 c28894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10188
  · exact u10189
  · exact u10190
  · exact u10191

def r28895 : Route 9 := (fun mask => (mask,id))

def c28895 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28895 : Upper (D 6) (R 6) [6,40,96,129,260] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,260] 13 (by decide) (choices 1) [1,2,16,64] r28895 c28895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10192
  · exact u10193
  · exact u10194
  · exact u10195

def r28896 : Route 9 := (fun mask => (mask,id))

def c28896 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28896 : Upper (D 6) (R 6) [6,40,96,129,320] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,320] 13 (by decide) (choices 1) [1,2,4,16] r28896 c28896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10196
  · exact u10197
  · exact u10198
  · exact u10199

def b28897 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,2),(4,6)], upper := (rows 7 42 100 152 19 357 325 453 325), lower := (rows 7 42 100 152 19 32 64 128 256), losses := [] }

theorem u28897 : Upper (D 6) (R 6) [6,40,96,144,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28897
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28898 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,1),(4,6)], upper := (rows 7 42 100 152 21 355 323 451 323), lower := (rows 7 42 100 152 21 32 64 128 256), losses := [] }

theorem u28898 : Upper (D 6) (R 6) [6,40,96,144,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28898
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28899 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 7 42 100 152 22 353 321 449 321), lower := (rows 7 42 100 152 22 32 64 128 256), losses := [] }

theorem u28899 : Upper (D 6) (R 6) [6,40,96,144,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28899
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28900 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(1,6),(3,5),(4,5)], upper := (rows 7 42 100 152 81 295 327 391 263), lower := (rows 7 42 100 152 81 32 64 128 256), losses := [{ target := 6, region := (rows 1 18 4 24 16 33 0 129 257), good := (rows 423 42 36 154 443 32 0 128 256) }] }

theorem u28900 : Upper (D 6) (R 6) [6,40,96,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28900
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28901 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 42 100 152 82 293 325 389 261), lower := (rows 7 42 100 152 82 32 64 128 256), losses := [] }

theorem u28901 : Upper (D 6) (R 6) [6,40,96,144,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28901
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28902 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 42 100 152 84 291 323 387 259), lower := (rows 7 42 100 152 84 32 64 128 256), losses := [] }

theorem u28902 : Upper (D 6) (R 6) [6,40,96,144,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28902
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28903 : Route 9 := (fun mask => (mask,id))

def c28903 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28903 : Upper (D 6) (R 6) [6,40,96,144,257] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,257] 13 (by decide) (choices 1) [1,2,4,64] r28903 c28903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10200
  · exact u10201
  · exact u10202
  · exact u10203

def b28904 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 42 100 152 274 101 69 197 325), lower := (rows 7 42 100 152 274 32 64 128 256), losses := [] }

theorem u28904 : Upper (D 6) (R 6) [6,40,96,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28904
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28905 : Route 9 := (fun mask => (mask,id))

def c28905 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28905 : Upper (D 6) (R 6) [6,40,96,144,260] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,260] 13 (by decide) (choices 1) [1,2,64] r28905 c28905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10204
  · exact u10205
  · exact u10206

def r28906 : Route 9 := (fun mask => (mask,id))

def c28906 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28906 : Upper (D 6) (R 6) [6,40,96,144,320] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,320] 13 (by decide) (choices 1) [1,2,4] r28906 c28906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10207
  · exact u10208
  · exact u10209

def b28907 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,2),(4,6)], upper := (rows 7 42 100 392 19 117 85 213 341), lower := (rows 7 42 100 392 19 32 64 128 256), losses := [] }

theorem u28907 : Upper (D 6) (R 6) [6,40,96,384,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28907
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28908 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 16, targets := 66 },{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,1),(4,6)], upper := (rows 7 42 100 392 21 115 83 211 339), lower := (rows 7 42 100 392 21 32 64 128 256), losses := [] }

theorem u28908 : Upper (D 6) (R 6) [6,40,96,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28908
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28909 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 7 42 100 392 22 113 81 209 337), lower := (rows 7 42 100 392 22 32 64 128 256), losses := [] }

theorem u28909 : Upper (D 6) (R 6) [6,40,96,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28909
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28910 : Route 9 := (fun mask => (mask,id))

def c28910 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28910 : Upper (D 6) (R 6) [6,40,96,384,65] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,65] 13 (by decide) (choices 1) [1,2,4,16] r28910 c28910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10210
  · exact u10211
  · exact u10212
  · exact u10213

def r28911 : Route 9 := (fun mask => (mask,id))

def c28911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28911 : Upper (D 6) (R 6) [6,40,96,384,66] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,66] 13 (by decide) (choices 1) [1,4,16] r28911 c28911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10214
  · exact u10215
  · exact u10216

def b28912 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 42 100 392 84 51 83 147 275), lower := (rows 7 42 100 392 84 32 64 128 256), losses := [] }

theorem u28912 : Upper (D 6) (R 6) [6,40,96,384,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28912
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28913 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 42 133 25 22 352 352 480 352), lower := (rows 7 42 133 25 22 32 64 128 256), losses := [] }

theorem u28913 : Upper (D 6) (R 6) [6,40,129,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28913
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28914 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 42 133 25 50 356 324 452 324), lower := (rows 7 42 133 25 50 32 64 128 256), losses := [] }

theorem u28914 : Upper (D 6) (R 6) [6,40,129,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28914
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28915 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 133 25 52 354 322 450 322), lower := (rows 7 42 133 25 52 32 64 128 256), losses := [] }

theorem u28915 : Upper (D 6) (R 6) [6,40,129,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28915
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28916 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 368, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 42 133 25 82 356 356 484 356), lower := (rows 7 42 133 25 82 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 25 37 69 133 261), good := (rows 502 58 500 506 82 32 64 128 256) }] }

theorem u28916 : Upper (D 6) (R 6) [6,40,129,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28916
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28917 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 354, targets := 5 },{ cop := 0, region := 368, targets := 1 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 42 133 25 84 354 354 482 354), lower := (rows 7 42 133 25 84 32 64 128 256), losses := [] }

theorem u28917 : Upper (D 6) (R 6) [6,40,129,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28917
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28918 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 368, targets := 1 }], pairs := [(0,5),(2,5),(4,0)], upper := (rows 7 42 133 25 112 358 326 454 326), lower := (rows 7 42 133 25 112 32 64 128 256), losses := [] }

theorem u28918 : Upper (D 6) (R 6) [6,40,129,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28918
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28919 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 368, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 42 133 25 274 100 100 228 356), lower := (rows 7 42 133 25 274 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 25 37 69 133 261), good := (rows 502 58 500 506 274 32 64 128 256) }] }

theorem u28919 : Upper (D 6) (R 6) [6,40,129,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28919
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u28919
end Delivery.IrregularNine14.P06
