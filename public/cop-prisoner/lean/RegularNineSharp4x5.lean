import RegularNineSharp4x5C020
namespace Delivery.FiniteExclusion.Sharp4x5
open Extremal
theorem upper (b : Assignment 9) (valid : Valid a b) : score (edgeOf a b)≤30 :=
  node1296 b valid (by intro i h; simp at h)
#print axioms upper
end Delivery.FiniteExclusion.Sharp4x5
