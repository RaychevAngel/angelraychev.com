import FiniteExclusionBoolean
import FiniteExclusionPrefixConjugacy
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x3x4
open Bounds BoundTreeRows Extremal
def a (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 4
  | 4 => 2
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 5
  | _ => 0

def f1 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 5
  | _ => 0

def g1 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 8
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
  | 3 => 3
  | 4 => 4
  | 5 => 7
  | 6 => 8
  | 7 => 5
  | 8 => 6
  | _ => 0

def g2 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 7
  | 6 => 8
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
  | 3 => 3
  | 4 => 4
  | 5 => 8
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def g3 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 6
  | 6 => 7
  | 7 => 8
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
  | 2 => 3
  | 3 => 4
  | 4 => 2
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g4 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 2
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut4 : Conjugacy a a where
  toFun := f4
  invFun := g4
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f8 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 2
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g8 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 4
  | 4 => 2
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut8 : Conjugacy a a where
  toFun := f8
  invFun := g8
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f12 (x : Fin 9) : Fin 9 :=
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

def g12 (x : Fin 9) : Fin 9 :=
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

def aut12 : Conjugacy a a where
  toFun := f12
  invFun := g12
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f13 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 5
  | _ => 0

def g13 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 8
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
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 7
  | 6 => 8
  | 7 => 5
  | 8 => 6
  | _ => 0

def g14 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 7
  | 6 => 8
  | 7 => 5
  | 8 => 6
  | _ => 0

def aut14 : Conjugacy a a where
  toFun := f14
  invFun := g14
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f16 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 4
  | 4 => 2
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g16 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | 3 => 2
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut16 : Conjugacy a a where
  toFun := f16
  invFun := g16
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f18 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 4
  | 4 => 2
  | 5 => 7
  | 6 => 8
  | 7 => 5
  | 8 => 6
  | _ => 0

def g18 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | 3 => 2
  | 4 => 3
  | 5 => 7
  | 6 => 8
  | 7 => 5
  | 8 => 6
  | _ => 0

def aut18 : Conjugacy a a where
  toFun := f18
  invFun := g18
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f20 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | 3 => 2
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g20 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 4
  | 4 => 2
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def aut20 : Conjugacy a a where
  toFun := f20
  invFun := g20
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f22 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | 3 => 2
  | 4 => 3
  | 5 => 7
  | 6 => 8
  | 7 => 5
  | 8 => 6
  | _ => 0

def g22 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 4
  | 4 => 2
  | 5 => 7
  | 6 => 8
  | 7 => 5
  | 8 => 6
  | _ => 0

def aut22 : Conjugacy a a where
  toFun := f22
  invFun := g22
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

end Delivery.FiniteExclusion.Sharp2x3x4
