import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b840 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 74 140 25 304 34 96 133 261), lower := (rows 7 74 140 25 304 34 96 128 256), losses := [] }

theorem u840 : Upper (D 5) (R 5) [6,72,136,17,288,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b840
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b841 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 140 56 274 33 65 164 292), lower := (rows 7 74 140 56 274 33 65 128 256), losses := [] }

theorem u841 : Upper (D 5) (R 5) [6,72,136,48,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b841
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b842 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 140 56 274 33 68 161 289), lower := (rows 7 74 140 56 274 33 68 128 256), losses := [] }

theorem u842 : Upper (D 5) (R 5) [6,72,136,48,258,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b842
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b843 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 74 140 56 274 33 96 133 261), lower := (rows 7 74 140 56 274 33 96 128 256), losses := [] }

theorem u843 : Upper (D 5) (R 5) [6,72,136,48,258,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b843
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b844 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 140 56 274 36 65 161 289), lower := (rows 7 74 140 56 274 36 65 128 256), losses := [] }

theorem u844 : Upper (D 5) (R 5) [6,72,136,48,258,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b844
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b845 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 74 140 56 274 36 96 129 257), lower := (rows 7 74 140 56 274 36 96 128 256), losses := [] }

theorem u845 : Upper (D 5) (R 5) [6,72,136,48,258,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b845
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b846 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 74, targets := 4 }], pairs := [(1,2)], upper := (rows 7 74 148 42 49 288 65 140 268), lower := (rows 7 74 148 42 49 288 65 128 256), losses := [] }

theorem u846 : Upper (D 5) (R 5) [6,72,144,34,33,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b846
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b847 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(3,2)], upper := (rows 7 74 148 42 49 288 68 137 265), lower := (rows 7 74 148 42 49 288 68 128 256), losses := [] }

theorem u847 : Upper (D 5) (R 5) [6,72,144,34,33,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b847
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b848 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 436, targets := 2 }], pairs := [(2,1)], upper := (rows 7 74 148 42 49 288 72 133 261), lower := (rows 7 74 148 42 49 288 72 128 256), losses := [] }

theorem u848 : Upper (D 5) (R 5) [6,72,144,34,33,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b848
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b849 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 148 42 273 33 68 168 296), lower := (rows 7 74 148 42 273 33 68 128 256), losses := [] }

theorem u849 : Upper (D 5) (R 5) [6,72,144,34,257,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b849
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b850 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 436, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 148 42 273 33 72 164 292), lower := (rows 7 74 148 42 273 33 72 128 256), losses := [] }

theorem u850 : Upper (D 5) (R 5) [6,72,144,34,257,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b850
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b851 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 74, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 148 42 273 33 96 140 268), lower := (rows 7 74 148 42 273 33 96 128 256), losses := [] }

theorem u851 : Upper (D 5) (R 5) [6,72,144,34,257,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b851
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b852 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 74 148 42 273 36 65 168 296), lower := (rows 7 74 148 42 273 36 65 128 256), losses := [{ target := 0, region := (rows 0 66 20 73 16 53 64 217 345), good := (rows 430 458 436 426 444 36 490 128 256) }] }

theorem u852 : Upper (D 5) (R 5) [6,72,144,34,257,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b852
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b853 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 436, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 148 42 273 36 72 161 289), lower := (rows 7 74 148 42 273 36 72 128 256), losses := [] }

theorem u853 : Upper (D 5) (R 5) [6,72,144,34,257,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b853
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b854 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 74, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 148 42 273 36 96 137 265), lower := (rows 7 74 148 42 273 36 96 128 256), losses := [] }

theorem u854 : Upper (D 5) (R 5) [6,72,144,34,257,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b854
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b855 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 148 42 280 33 65 164 292), lower := (rows 7 74 148 42 280 33 65 128 256), losses := [] }

theorem u855 : Upper (D 5) (R 5) [6,72,144,34,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b855
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b856 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 148 42 280 33 68 161 289), lower := (rows 7 74 148 42 280 33 68 128 256), losses := [] }

theorem u856 : Upper (D 5) (R 5) [6,72,144,34,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b856
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b857 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 74, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 148 42 280 33 96 133 261), lower := (rows 7 74 148 42 280 33 96 128 256), losses := [] }

theorem u857 : Upper (D 5) (R 5) [6,72,144,34,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b857
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b858 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 74 148 42 280 36 65 161 289), lower := (rows 7 74 148 42 280 36 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 73 16 37 64 128 256), good := (rows 46 74 180 42 280 36 106 128 256) }] }

theorem u858 : Upper (D 5) (R 5) [6,72,144,34,264,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b858
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b859 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 74, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 148 42 280 36 96 129 257), lower := (rows 7 74 148 42 280 36 96 128 256), losses := [] }

theorem u859 : Upper (D 5) (R 5) [6,72,144,34,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b859
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b860 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 148 42 304 33 65 140 268), lower := (rows 7 74 148 42 304 33 65 128 256), losses := [] }

theorem u860 : Upper (D 5) (R 5) [6,72,144,34,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b860
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b861 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 148 42 304 33 68 137 265), lower := (rows 7 74 148 42 304 33 68 128 256), losses := [] }

theorem u861 : Upper (D 5) (R 5) [6,72,144,34,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b861
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b862 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 436, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 148 42 304 33 72 133 261), lower := (rows 7 74 148 42 304 33 72 128 256), losses := [] }

theorem u862 : Upper (D 5) (R 5) [6,72,144,34,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b862
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b863 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 74 148 42 304 36 65 137 265), lower := (rows 7 74 148 42 304 36 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 73 16 37 64 128 256), good := (rows 46 74 180 42 304 36 106 128 256) }] }

theorem u863 : Upper (D 5) (R 5) [6,72,144,34,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b863
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b864 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 436, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 74 148 42 304 36 72 129 257), lower := (rows 7 74 148 42 304 36 72 128 256), losses := [] }

theorem u864 : Upper (D 5) (R 5) [6,72,144,34,288,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b864
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b865 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 148 44 273 34 65 168 296), lower := (rows 7 74 148 44 273 34 65 128 256), losses := [] }

theorem u865 : Upper (D 5) (R 5) [6,72,144,36,257,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b865
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b866 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 437, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 148 44 273 34 72 161 289), lower := (rows 7 74 148 44 273 34 72 128 256), losses := [] }

theorem u866 : Upper (D 5) (R 5) [6,72,144,36,257,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b866
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b867 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 74 148 44 273 34 96 137 265), lower := (rows 7 74 148 44 273 34 96 128 256), losses := [] }

theorem u867 : Upper (D 5) (R 5) [6,72,144,36,257,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b867
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b868 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 148 44 274 33 65 168 296), lower := (rows 7 74 148 44 274 33 65 128 256), losses := [] }

theorem u868 : Upper (D 5) (R 5) [6,72,144,36,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b868
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b869 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 437, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 148 44 274 33 72 161 289), lower := (rows 7 74 148 44 274 33 72 128 256), losses := [] }

theorem u869 : Upper (D 5) (R 5) [6,72,144,36,258,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b869
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b870 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 74 148 44 274 33 96 137 265), lower := (rows 7 74 148 44 274 33 96 128 256), losses := [] }

theorem u870 : Upper (D 5) (R 5) [6,72,144,36,258,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b870
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b871 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 148 44 280 33 65 162 290), lower := (rows 7 74 148 44 280 33 65 128 256), losses := [] }

theorem u871 : Upper (D 5) (R 5) [6,72,144,36,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b871
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b872 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 148 44 280 33 66 161 289), lower := (rows 7 74 148 44 280 33 66 128 256), losses := [] }

theorem u872 : Upper (D 5) (R 5) [6,72,144,36,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b872
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b873 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 74 148 44 280 33 96 131 259), lower := (rows 7 74 148 44 280 33 96 128 256), losses := [] }

theorem u873 : Upper (D 5) (R 5) [6,72,144,36,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b873
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b874 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 148 44 280 34 65 161 289), lower := (rows 7 74 148 44 280 34 65 128 256), losses := [] }

theorem u874 : Upper (D 5) (R 5) [6,72,144,36,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b874
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b875 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 74 148 44 280 34 96 129 257), lower := (rows 7 74 148 44 280 34 96 128 256), losses := [] }

theorem u875 : Upper (D 5) (R 5) [6,72,144,36,264,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b875
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b876 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 148 266 56 33 65 164 292), lower := (rows 7 74 148 266 56 33 65 128 256), losses := [] }

theorem u876 : Upper (D 5) (R 5) [6,72,144,258,40,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b876
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b877 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 148 266 56 33 68 161 289), lower := (rows 7 74 148 266 56 33 68 128 256), losses := [] }

theorem u877 : Upper (D 5) (R 5) [6,72,144,258,40,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b877
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b878 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 148 266 56 33 96 133 261), lower := (rows 7 74 148 266 56 33 96 128 256), losses := [] }

theorem u878 : Upper (D 5) (R 5) [6,72,144,258,40,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b878
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b879 : PairBound 9 := { available := 33, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 74 148 266 56 36 65 161 289), lower := (rows 7 74 148 266 56 36 65 128 256), losses := [{ target := 1, region := (rows 1 0 7 8 26 111 65 193 321), good := (rows 501 508 180 316 56 36 485 128 256) }] }

theorem u879 : Upper (D 5) (R 5) [6,72,144,258,40,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b879
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b880 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 264, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 74 148 266 56 36 96 129 257), lower := (rows 7 74 148 266 56 36 96 128 256), losses := [] }

theorem u880 : Upper (D 5) (R 5) [6,72,144,258,40,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b880
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b881 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 74 148 268 56 33 65 162 290), lower := (rows 7 74 148 268 56 33 65 128 256), losses := [] }

theorem u881 : Upper (D 5) (R 5) [6,72,144,260,40,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b881
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b882 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 148 268 56 33 66 161 289), lower := (rows 7 74 148 268 56 33 66 128 256), losses := [] }

theorem u882 : Upper (D 5) (R 5) [6,72,144,260,40,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b882
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b883 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 148 268 56 33 96 131 259), lower := (rows 7 74 148 268 56 33 96 128 256), losses := [] }

theorem u883 : Upper (D 5) (R 5) [6,72,144,260,40,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b883
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b884 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 148 296 25 33 66 164 292), lower := (rows 7 74 148 296 25 33 66 128 256), losses := [] }

theorem u884 : Upper (D 5) (R 5) [6,72,144,288,9,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b884
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b885 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 148 296 25 33 68 162 290), lower := (rows 7 74 148 296 25 33 68 128 256), losses := [] }

theorem u885 : Upper (D 5) (R 5) [6,72,144,288,9,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b885
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b886 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 149, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 74 148 296 25 33 96 134 262), lower := (rows 7 74 148 296 25 33 96 128 256), losses := [] }

theorem u886 : Upper (D 5) (R 5) [6,72,144,288,9,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b886
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b887 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 296, targets := 1 },{ cop := 4, region := 66, targets := 4 }], pairs := [(1,2),(3,0)], upper := (rows 7 74 148 296 25 34 65 164 292), lower := (rows 7 74 148 296 25 34 65 128 256), losses := [] }

theorem u887 : Upper (D 5) (R 5) [6,72,144,288,9,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b887
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b888 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 148 296 25 34 68 161 289), lower := (rows 7 74 148 296 25 34 68 128 256), losses := [] }

theorem u888 : Upper (D 5) (R 5) [6,72,144,288,9,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b888
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b889 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 106, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 74 148 296 25 34 96 133 261), lower := (rows 7 74 148 296 25 34 96 128 256), losses := [] }

theorem u889 : Upper (D 5) (R 5) [6,72,144,288,9,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b889
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b890 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 66, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 74 148 296 25 36 65 162 290), lower := (rows 7 74 148 296 25 36 65 128 256), losses := [] }

theorem u890 : Upper (D 5) (R 5) [6,72,144,288,9,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b890
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b891 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 148 296 25 36 66 161 289), lower := (rows 7 74 148 296 25 36 66 128 256), losses := [] }

theorem u891 : Upper (D 5) (R 5) [6,72,144,288,9,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b891
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b892 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 149, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 74 148 296 25 36 96 131 259), lower := (rows 7 74 148 296 25 36 96 128 256), losses := [] }

theorem u892 : Upper (D 5) (R 5) [6,72,144,288,9,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b892
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b893 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 25 274 33 68 168 296), lower := (rows 7 74 164 25 274 33 68 128 256), losses := [] }

theorem u893 : Upper (D 5) (R 5) [6,72,160,17,258,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b893
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b894 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 74 164 25 274 33 72 164 292), lower := (rows 7 74 164 25 274 33 72 128 256), losses := [] }

theorem u894 : Upper (D 5) (R 5) [6,72,160,17,258,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b894
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b895 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 74 164 25 274 33 96 140 268), lower := (rows 7 74 164 25 274 33 96 128 256), losses := [] }

theorem u895 : Upper (D 5) (R 5) [6,72,160,17,258,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b895
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b896 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 74 164 25 274 40 65 164 292), lower := (rows 7 74 164 25 274 40 65 128 256), losses := [] }

theorem u896 : Upper (D 5) (R 5) [6,72,160,17,258,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b896
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b897 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 74 164 25 274 40 68 161 289), lower := (rows 7 74 164 25 274 40 68 128 256), losses := [] }

theorem u897 : Upper (D 5) (R 5) [6,72,160,17,258,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b897
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b898 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 74 164 25 274 40 96 133 261), lower := (rows 7 74 164 25 274 40 96 128 256), losses := [] }

theorem u898 : Upper (D 5) (R 5) [6,72,160,17,258,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b898
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b899 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 74 164 25 276 33 66 168 296), lower := (rows 7 74 164 25 276 33 66 128 256), losses := [] }

theorem u899 : Upper (D 5) (R 5) [6,72,160,17,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b899
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u899
end Delivery.IrregularNine14.P05
