import FiniteExclusionBoolean
import FiniteExclusionPrefixConjugacy
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
namespace Delivery.FiniteExclusion.Sharp2x2x5
open Bounds BoundTreeRows Extremal
def a (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 4
  | _ => 0

def f1 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 4
  | _ => 0

def g1 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 8
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
  | 3 => 3
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 4
  | 8 => 5
  | _ => 0

def g2 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 7
  | 5 => 8
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
  | 3 => 3
  | 4 => 7
  | 5 => 8
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def g3 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 6
  | 5 => 7
  | 6 => 8
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
  | 3 => 3
  | 4 => 8
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def g4 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
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
  | 2 => 3
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | _ => 0

def g5 (x : Fin 9) : Fin 9 :=
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

def aut5 : Conjugacy a a where
  toFun := f5
  invFun := g5
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f10 (x : Fin 9) : Fin 9 :=
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

def g10 (x : Fin 9) : Fin 9 :=
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

def aut10 : Conjugacy a a where
  toFun := f10
  invFun := g10
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f11 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 4
  | _ => 0

def g11 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 8
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut11 : Conjugacy a a where
  toFun := f11
  invFun := g11
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f12 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 4
  | 8 => 5
  | _ => 0

def g12 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 7
  | 5 => 8
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def aut12 : Conjugacy a a where
  toFun := f12
  invFun := g12
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f15 (x : Fin 9) : Fin 9 :=
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

def g15 (x : Fin 9) : Fin 9 :=
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

def aut15 : Conjugacy a a where
  toFun := f15
  invFun := g15
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f16 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 4
  | _ => 0

def g16 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 8
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut16 : Conjugacy a a where
  toFun := f16
  invFun := g16
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f17 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 4
  | 8 => 5
  | _ => 0

def g17 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 7
  | 5 => 8
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def aut17 : Conjugacy a a where
  toFun := f17
  invFun := g17
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f20 (x : Fin 9) : Fin 9 :=
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

def g20 (x : Fin 9) : Fin 9 :=
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

def aut20 : Conjugacy a a where
  toFun := f20
  invFun := g20
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f21 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 4
  | _ => 0

def g21 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 8
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut21 : Conjugacy a a where
  toFun := f21
  invFun := g21
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f22 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 4
  | 8 => 5
  | _ => 0

def g22 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 7
  | 5 => 8
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def aut22 : Conjugacy a a where
  toFun := f22
  invFun := g22
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f23 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 7
  | 5 => 8
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def g23 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 4
  | 8 => 5
  | _ => 0

def aut23 : Conjugacy a a where
  toFun := f23
  invFun := g23
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f24 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 8
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def g24 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 4
  | _ => 0

def aut24 : Conjugacy a a where
  toFun := f24
  invFun := g24
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f25 (x : Fin 9) : Fin 9 :=
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

def g25 (x : Fin 9) : Fin 9 :=
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

def aut25 : Conjugacy a a where
  toFun := f25
  invFun := g25
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f26 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 4
  | _ => 0

def g26 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 8
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut26 : Conjugacy a a where
  toFun := f26
  invFun := g26
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f27 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 4
  | 8 => 5
  | _ => 0

def g27 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 7
  | 5 => 8
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def aut27 : Conjugacy a a where
  toFun := f27
  invFun := g27
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f28 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 7
  | 5 => 8
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def g28 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 4
  | 8 => 5
  | _ => 0

def aut28 : Conjugacy a a where
  toFun := f28
  invFun := g28
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f29 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 8
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def g29 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 4
  | _ => 0

def aut29 : Conjugacy a a where
  toFun := f29
  invFun := g29
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f31 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 4
  | _ => 0

def g31 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 8
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut31 : Conjugacy a a where
  toFun := f31
  invFun := g31
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f32 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 4
  | 8 => 5
  | _ => 0

def g32 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 7
  | 5 => 8
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def aut32 : Conjugacy a a where
  toFun := f32
  invFun := g32
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f33 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 7
  | 5 => 8
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def g33 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 4
  | 8 => 5
  | _ => 0

def aut33 : Conjugacy a a where
  toFun := f33
  invFun := g33
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f34 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 8
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def g34 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 4
  | _ => 0

def aut34 : Conjugacy a a where
  toFun := f34
  invFun := g34
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f36 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 4
  | _ => 0

def g36 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 8
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def aut36 : Conjugacy a a where
  toFun := f36
  invFun := g36
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f37 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 4
  | 8 => 5
  | _ => 0

def g37 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 7
  | 5 => 8
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def aut37 : Conjugacy a a where
  toFun := f37
  invFun := g37
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f38 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 7
  | 5 => 8
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def g38 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 6
  | 5 => 7
  | 6 => 8
  | 7 => 4
  | 8 => 5
  | _ => 0

def aut38 : Conjugacy a a where
  toFun := f38
  invFun := g38
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

def f39 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 8
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | _ => 0

def g39 (x : Fin 9) : Fin 9 :=
  match x.val with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 4
  | _ => 0

def aut39 : Conjugacy a a where
  toFun := f39
  invFun := g39
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  commute := by decide +kernel

end Delivery.FiniteExclusion.Sharp2x2x5
