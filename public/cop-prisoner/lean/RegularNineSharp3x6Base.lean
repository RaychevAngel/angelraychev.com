import FiniteExclusionBoolean
import FiniteExclusionPrefixConjugacy
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp3x6
open Bounds BoundTreeRows Extremal
def a (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 3
  | _ => 0

def f1 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 3
  | _ => 0

def g1 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 8
  | 4 => 3
  | 5 => 4
  | 6 => 5
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
  | 3 => 5
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 3
  | 8 => 4
  | _ => 0

def g2 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 7
  | 4 => 8
  | 5 => 3
  | 6 => 4
  | 7 => 5
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
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | _ => 0

def g3 (x : Fin 9) : Fin 9 :=
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

def aut3 : Conjugacy a a where
  toFun := f3
  invFun := g3
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f4 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 7
  | 4 => 8
  | 5 => 3
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def g4 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 3
  | 8 => 4
  | _ => 0

def aut4 : Conjugacy a a where
  toFun := f4
  invFun := g4
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f5 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 8
  | 4 => 3
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def g5 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 3
  | _ => 0

def aut5 : Conjugacy a a where
  toFun := f5
  invFun := g5
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f6 (x : Fin 9) : Fin 9 :=
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

def g6 (x : Fin 9) : Fin 9 :=
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

def aut6 : Conjugacy a a where
  toFun := f6
  invFun := g6
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f7 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 3
  | _ => 0

def g7 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 8
  | 4 => 3
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut7 : Conjugacy a a where
  toFun := f7
  invFun := g7
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f8 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 5
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 3
  | 8 => 4
  | _ => 0

def g8 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 7
  | 4 => 8
  | 5 => 3
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def aut8 : Conjugacy a a where
  toFun := f8
  invFun := g8
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f9 (x : Fin 9) : Fin 9 :=
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

def g9 (x : Fin 9) : Fin 9 :=
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

def aut9 : Conjugacy a a where
  toFun := f9
  invFun := g9
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f12 (x : Fin 9) : Fin 9 :=
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

def g12 (x : Fin 9) : Fin 9 :=
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

def aut12 : Conjugacy a a where
  toFun := f12
  invFun := g12
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f13 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 3
  | _ => 0

def g13 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 8
  | 4 => 3
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut13 : Conjugacy a a where
  toFun := f13
  invFun := g13
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f14 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 5
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 3
  | 8 => 4
  | _ => 0

def g14 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 7
  | 4 => 8
  | 5 => 3
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def aut14 : Conjugacy a a where
  toFun := f14
  invFun := g14
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f15 (x : Fin 9) : Fin 9 :=
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

def g15 (x : Fin 9) : Fin 9 :=
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

def aut15 : Conjugacy a a where
  toFun := f15
  invFun := g15
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f16 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 7
  | 4 => 8
  | 5 => 3
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def g16 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 5
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 3
  | 8 => 4
  | _ => 0

def aut16 : Conjugacy a a where
  toFun := f16
  invFun := g16
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f17 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 8
  | 4 => 3
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def g17 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 3
  | _ => 0

def aut17 : Conjugacy a a where
  toFun := f17
  invFun := g17
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

end Delivery.FiniteExclusion.Sharp3x6
