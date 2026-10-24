import FiniteExclusionBoolean
import FiniteExclusionPrefixConjugacy
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x7
open Bounds BoundTreeRows Extremal
def a (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 2
  | _ => 0

def f1 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 2
  | _ => 0

def g1 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 8
  | 3 => 2
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
  | 2 => 4
  | 3 => 5
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 2
  | 8 => 3
  | _ => 0

def g2 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 7
  | 3 => 8
  | 4 => 2
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
  | 2 => 5
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 2
  | 7 => 3
  | 8 => 4
  | _ => 0

def g3 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
  | 4 => 8
  | 5 => 2
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
  | 2 => 6
  | 3 => 7
  | 4 => 8
  | 5 => 2
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | _ => 0

def g4 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 5
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 2
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
  | 2 => 7
  | 3 => 8
  | 4 => 2
  | 5 => 3
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def g5 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 2
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
  | 0 => 0
  | 1 => 1
  | 2 => 8
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def g6 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 2
  | _ => 0

def aut6 : Conjugacy a a where
  toFun := f6
  invFun := g6
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f8 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 2
  | _ => 0

def g8 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 8
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
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
  | 1 => 0
  | 2 => 4
  | 3 => 5
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 2
  | 8 => 3
  | _ => 0

def g9 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 7
  | 3 => 8
  | 4 => 2
  | 5 => 3
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def aut9 : Conjugacy a a where
  toFun := f9
  invFun := g9
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f10 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 5
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 2
  | 7 => 3
  | 8 => 4
  | _ => 0

def g10 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 6
  | 3 => 7
  | 4 => 8
  | 5 => 2
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

end Delivery.FiniteExclusion.Sharp2x7
