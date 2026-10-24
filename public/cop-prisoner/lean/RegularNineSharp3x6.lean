import RegularNineSharp3x6C025
namespace Delivery.FiniteExclusion.Sharp3x6
open Extremal
theorem upper (b : Assignment 9) (valid : Valid a b) : score (edgeOf a b)≤30 :=
  node1617 b valid (by intro i h; simp at h)
#print axioms upper
end Delivery.FiniteExclusion.Sharp3x6
