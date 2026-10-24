import FiniteExclusionBoolean
import FiniteExclusionPrefixConjugacy
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x2x2x3
open Bounds BoundTreeRows Extremal
def a (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | 5 => 4
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
  | 3 => 3
  | 4 => 5
  | 5 => 4
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g3 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
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
  | 2 => 3
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g6 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2
  | 4 => 4
  | 5 => 5
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

def f12 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | 4 => 2
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g12 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | 4 => 2
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut12 : Conjugacy a a where
  toFun := f12
  invFun := g12
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f15 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | 4 => 3
  | 5 => 2
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g15 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 5
  | 3 => 4
  | 4 => 2
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut15 : Conjugacy a a where
  toFun := f15
  invFun := g15
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f24 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g24 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
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

def f25 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g25 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut25 : Conjugacy a a where
  toFun := f25
  invFun := g25
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f30 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g30 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut30 : Conjugacy a a where
  toFun := f30
  invFun := g30
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f31 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g31 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut31 : Conjugacy a a where
  toFun := f31
  invFun := g31
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f33 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | 5 => 4
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g33 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | 5 => 4
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut33 : Conjugacy a a where
  toFun := f33
  invFun := g33
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f36 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | 3 => 5
  | 4 => 2
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g36 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | 3 => 5
  | 4 => 2
  | 5 => 3
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

def f37 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | 3 => 5
  | 4 => 2
  | 5 => 3
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g37 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | 3 => 5
  | 4 => 2
  | 5 => 3
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut37 : Conjugacy a a where
  toFun := f37
  invFun := g37
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f38 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | 3 => 5
  | 4 => 2
  | 5 => 3
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g38 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | 3 => 5
  | 4 => 2
  | 5 => 3
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut38 : Conjugacy a a where
  toFun := f38
  invFun := g38
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f39 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | 3 => 5
  | 4 => 3
  | 5 => 2
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g39 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 5
  | 3 => 4
  | 4 => 2
  | 5 => 3
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

def f48 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g48 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut48 : Conjugacy a a where
  toFun := f48
  invFun := g48
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f49 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g49 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut49 : Conjugacy a a where
  toFun := f49
  invFun := g49
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f51 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 5
  | 5 => 4
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g51 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 5
  | 5 => 4
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut51 : Conjugacy a a where
  toFun := f51
  invFun := g51
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f52 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 5
  | 5 => 4
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g52 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 5
  | 5 => 4
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut52 : Conjugacy a a where
  toFun := f52
  invFun := g52
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f54 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g54 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 4
  | 5 => 5
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
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 4
  | 5 => 5
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g55 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 4
  | 5 => 5
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
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 4
  | 5 => 5
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g56 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 4
  | 5 => 5
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
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 5
  | 5 => 4
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g57 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 5
  | 5 => 4
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
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 5
  | 5 => 4
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g58 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 5
  | 5 => 4
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

def f60 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 0
  | 5 => 1
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g60 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut60 : Conjugacy a a where
  toFun := f60
  invFun := g60
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f61 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
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
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
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

def f63 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 1
  | 5 => 0
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g63 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut63 : Conjugacy a a where
  toFun := f63
  invFun := g63
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f64 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 1
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g64 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut64 : Conjugacy a a where
  toFun := f64
  invFun := g64
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f65 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 1
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g65 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut65 : Conjugacy a a where
  toFun := f65
  invFun := g65
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f66 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | 3 => 4
  | 4 => 0
  | 5 => 1
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g66 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 0
  | 3 => 1
  | 4 => 3
  | 5 => 2
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut66 : Conjugacy a a where
  toFun := f66
  invFun := g66
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f69 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | 3 => 4
  | 4 => 1
  | 5 => 0
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g69 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 0
  | 3 => 1
  | 4 => 3
  | 5 => 2
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut69 : Conjugacy a a where
  toFun := f69
  invFun := g69
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f70 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | 3 => 4
  | 4 => 1
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g70 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 0
  | 3 => 1
  | 4 => 3
  | 5 => 2
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut70 : Conjugacy a a where
  toFun := f70
  invFun := g70
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f72 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g72 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut72 : Conjugacy a a where
  toFun := f72
  invFun := g72
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f73 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g73 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 4
  | 5 => 5
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
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g74 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 4
  | 5 => 5
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
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 5
  | 5 => 4
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g75 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 5
  | 5 => 4
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

def f77 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 5
  | 5 => 4
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g77 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 5
  | 5 => 4
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

def f78 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g78 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut78 : Conjugacy a a where
  toFun := f78
  invFun := g78
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f79 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 4
  | 5 => 5
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g79 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 4
  | 5 => 5
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
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 4
  | 5 => 5
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g80 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 4
  | 5 => 5
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

def f81 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 5
  | 5 => 4
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g81 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 5
  | 5 => 4
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut81 : Conjugacy a a where
  toFun := f81
  invFun := g81
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f82 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 5
  | 5 => 4
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g82 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 5
  | 5 => 4
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut82 : Conjugacy a a where
  toFun := f82
  invFun := g82
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f84 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 4
  | 3 => 5
  | 4 => 0
  | 5 => 1
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g84 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut84 : Conjugacy a a where
  toFun := f84
  invFun := g84
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f87 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 4
  | 3 => 5
  | 4 => 1
  | 5 => 0
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g87 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut87 : Conjugacy a a where
  toFun := f87
  invFun := g87
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f90 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 5
  | 3 => 4
  | 4 => 0
  | 5 => 1
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g90 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 2
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
  | 0 => 3
  | 1 => 2
  | 2 => 5
  | 3 => 4
  | 4 => 0
  | 5 => 1
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g91 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 2
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

def f93 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 5
  | 3 => 4
  | 4 => 1
  | 5 => 0
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g93 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 2
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
  | 0 => 3
  | 1 => 2
  | 2 => 5
  | 3 => 4
  | 4 => 1
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g94 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 2
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
  | 0 => 3
  | 1 => 2
  | 2 => 5
  | 3 => 4
  | 4 => 1
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g95 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 2
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

def f96 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g96 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 0
  | 5 => 1
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut96 : Conjugacy a a where
  toFun := f96
  invFun := g96
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f97 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g97 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 0
  | 5 => 1
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
  | 0 => 4
  | 1 => 5
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g98 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 0
  | 5 => 1
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

def f103 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | 5 => 3
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g103 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 4
  | 3 => 5
  | 4 => 0
  | 5 => 1
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut103 : Conjugacy a a where
  toFun := f103
  invFun := g103
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f104 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | 5 => 3
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g104 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 4
  | 3 => 5
  | 4 => 0
  | 5 => 1
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut104 : Conjugacy a a where
  toFun := f104
  invFun := g104
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f105 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 2
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g105 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 5
  | 3 => 4
  | 4 => 0
  | 5 => 1
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut105 : Conjugacy a a where
  toFun := f105
  invFun := g105
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f106 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 2
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g106 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 5
  | 3 => 4
  | 4 => 0
  | 5 => 1
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut106 : Conjugacy a a where
  toFun := f106
  invFun := g106
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f107 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 2
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g107 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 5
  | 3 => 4
  | 4 => 0
  | 5 => 1
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut107 : Conjugacy a a where
  toFun := f107
  invFun := g107
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f110 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 2
  | 3 => 3
  | 4 => 0
  | 5 => 1
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g110 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 2
  | 3 => 3
  | 4 => 0
  | 5 => 1
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut110 : Conjugacy a a where
  toFun := f110
  invFun := g110
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f113 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 2
  | 3 => 3
  | 4 => 1
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g113 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 2
  | 3 => 3
  | 4 => 0
  | 5 => 1
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut113 : Conjugacy a a where
  toFun := f113
  invFun := g113
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f115 (x : Fin 9) : Fin 9 :=
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

def g115 (x : Fin 9) : Fin 9 :=
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

def aut115 : Conjugacy a a where
  toFun := f115
  invFun := g115
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f116 (x : Fin 9) : Fin 9 :=
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

def g116 (x : Fin 9) : Fin 9 :=
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

def aut116 : Conjugacy a a where
  toFun := f116
  invFun := g116
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f117 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g117 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut117 : Conjugacy a a where
  toFun := f117
  invFun := g117
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f118 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g118 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut118 : Conjugacy a a where
  toFun := f118
  invFun := g118
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f119 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g119 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut119 : Conjugacy a a where
  toFun := f119
  invFun := g119
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f121 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g121 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 1
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut121 : Conjugacy a a where
  toFun := f121
  invFun := g121
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f122 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g122 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 1
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut122 : Conjugacy a a where
  toFun := f122
  invFun := g122
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f123 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 0
  | 3 => 1
  | 4 => 3
  | 5 => 2
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g123 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | 3 => 4
  | 4 => 1
  | 5 => 0
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut123 : Conjugacy a a where
  toFun := f123
  invFun := g123
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f127 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | 5 => 3
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g127 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 4
  | 3 => 5
  | 4 => 1
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut127 : Conjugacy a a where
  toFun := f127
  invFun := g127
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f128 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | 5 => 3
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g128 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 4
  | 3 => 5
  | 4 => 1
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut128 : Conjugacy a a where
  toFun := f128
  invFun := g128
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f129 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 2
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g129 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 5
  | 3 => 4
  | 4 => 1
  | 5 => 0
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut129 : Conjugacy a a where
  toFun := f129
  invFun := g129
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f130 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 2
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g130 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 5
  | 3 => 4
  | 4 => 1
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut130 : Conjugacy a a where
  toFun := f130
  invFun := g130
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f131 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 2
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g131 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 5
  | 3 => 4
  | 4 => 1
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut131 : Conjugacy a a where
  toFun := f131
  invFun := g131
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f139 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g139 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut139 : Conjugacy a a where
  toFun := f139
  invFun := g139
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f140 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g140 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 4
  | 1 => 5
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut140 : Conjugacy a a where
  toFun := f140
  invFun := g140
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f142 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def g142 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut142 : Conjugacy a a where
  toFun := f142
  invFun := g142
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f143 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 8
  | 7 => 6
  | 8 => 7
  | _ => 0

def g143 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 7
  | 7 => 8
  | 8 => 6
  | _ => 0

def aut143 : Conjugacy a a where
  toFun := f143
  invFun := g143
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

end Delivery.FiniteExclusion.Sharp2x2x2x3
