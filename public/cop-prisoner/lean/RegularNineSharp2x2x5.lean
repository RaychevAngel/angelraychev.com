import RegularNineSharp2x2x5C009
namespace Delivery.FiniteExclusion.Sharp2x2x5
open Extremal
theorem upper (b : Assignment 9) (valid : Valid a b) : score (edgeOf a b)≤30 :=
  node606 b valid (by intro i h; simp at h)
#print axioms upper
end Delivery.FiniteExclusion.Sharp2x2x5
