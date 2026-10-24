import FiniteExclusionBoolean
import FiniteExclusionPrefixConjugacy
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x3x3
open Bounds BoundTreeRows Extremal
def a (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 4
  | 4 => 5
  | 5 => 3
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def f1 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g1 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut1 : Conjugacy a a where
  toFun := f1
  invFun := g1
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f2 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g2 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut2 : Conjugacy a a where
  toFun := f2
  invFun := g2
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f3 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 5
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g3 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 3
  | 5 => 4
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut3 : Conjugacy a a where
  toFun := f3
  invFun := g3
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f6 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 3
  | 5 => 4
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g6 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 5
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut6 : Conjugacy a a where
  toFun := f6
  invFun := g6
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f9 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | _ => 0

def g9 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | _ => 0

def aut9 : Conjugacy a a where
  toFun := f9
  invFun := g9
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f10 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 4
  | 7 => 5
  | 8 => 3
  | _ => 0

def g10 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 8
  | 4 => 6
  | 5 => 7
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | _ => 0

def aut10 : Conjugacy a a where
  toFun := f10
  invFun := g10
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f11 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 5
  | 7 => 3
  | 8 => 4
  | _ => 0

def g11 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 7
  | 4 => 8
  | 5 => 6
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | _ => 0

def aut11 : Conjugacy a a where
  toFun := f11
  invFun := g11
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f18 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g18 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut18 : Conjugacy a a where
  toFun := f18
  invFun := g18
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f21 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 4
  | 4 => 5
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g21 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 5
  | 4 => 3
  | 5 => 4
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut21 : Conjugacy a a where
  toFun := f21
  invFun := g21
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f24 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 5
  | 4 => 3
  | 5 => 4
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g24 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 4
  | 4 => 5
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut24 : Conjugacy a a where
  toFun := f24
  invFun := g24
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f36 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g36 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut36 : Conjugacy a a where
  toFun := f36
  invFun := g36
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f39 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 4
  | 4 => 5
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g39 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 5
  | 4 => 3
  | 5 => 4
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut39 : Conjugacy a a where
  toFun := f39
  invFun := g39
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f42 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 5
  | 4 => 3
  | 5 => 4
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g42 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 4
  | 4 => 5
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut42 : Conjugacy a a where
  toFun := f42
  invFun := g42
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f45 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | _ => 0

def g45 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | _ => 0

def aut45 : Conjugacy a a where
  toFun := f45
  invFun := g45
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f46 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 4
  | 7 => 5
  | 8 => 3
  | _ => 0

def g46 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 8
  | 4 => 6
  | 5 => 7
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | _ => 0

def aut46 : Conjugacy a a where
  toFun := f46
  invFun := g46
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f47 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 5
  | 7 => 3
  | 8 => 4
  | _ => 0

def g47 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 7
  | 4 => 8
  | 5 => 6
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | _ => 0

def aut47 : Conjugacy a a where
  toFun := f47
  invFun := g47
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f54 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g54 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut54 : Conjugacy a a where
  toFun := f54
  invFun := g54
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f55 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g55 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut55 : Conjugacy a a where
  toFun := f55
  invFun := g55
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f56 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g56 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut56 : Conjugacy a a where
  toFun := f56
  invFun := g56
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f57 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g57 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut57 : Conjugacy a a where
  toFun := f57
  invFun := g57
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f58 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g58 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut58 : Conjugacy a a where
  toFun := f58
  invFun := g58
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f59 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g59 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut59 : Conjugacy a a where
  toFun := f59
  invFun := g59
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f61 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g61 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut61 : Conjugacy a a where
  toFun := f61
  invFun := g61
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f62 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g62 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut62 : Conjugacy a a where
  toFun := f62
  invFun := g62
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f73 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g73 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut73 : Conjugacy a a where
  toFun := f73
  invFun := g73
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f74 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g74 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut74 : Conjugacy a a where
  toFun := f74
  invFun := g74
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f75 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g75 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut75 : Conjugacy a a where
  toFun := f75
  invFun := g75
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f76 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g76 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut76 : Conjugacy a a where
  toFun := f76
  invFun := g76
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f77 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g77 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut77 : Conjugacy a a where
  toFun := f77
  invFun := g77
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f79 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g79 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut79 : Conjugacy a a where
  toFun := f79
  invFun := g79
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f80 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g80 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut80 : Conjugacy a a where
  toFun := f80
  invFun := g80
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f90 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g90 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut90 : Conjugacy a a where
  toFun := f90
  invFun := g90
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f91 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g91 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut91 : Conjugacy a a where
  toFun := f91
  invFun := g91
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f92 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g92 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut92 : Conjugacy a a where
  toFun := f92
  invFun := g92
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f93 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g93 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut93 : Conjugacy a a where
  toFun := f93
  invFun := g93
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f94 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g94 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut94 : Conjugacy a a where
  toFun := f94
  invFun := g94
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f95 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g95 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut95 : Conjugacy a a where
  toFun := f95
  invFun := g95
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f97 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g97 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut97 : Conjugacy a a where
  toFun := f97
  invFun := g97
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f98 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 3
  | 2 => 4
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g98 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut98 : Conjugacy a a where
  toFun := f98
  invFun := g98
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

end Delivery.FiniteExclusion.Sharp3x3x3
