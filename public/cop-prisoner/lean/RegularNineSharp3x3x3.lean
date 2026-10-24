import RegularNineSharp3x3x3C007
namespace Delivery.FiniteExclusion.Sharp3x3x3
open Extremal
theorem upper (b : Assignment 9) (valid : Valid a b) : score (edgeOf a b)≤30 :=
  node477 b valid (by intro i h; simp at h)
#print axioms upper
end Delivery.FiniteExclusion.Sharp3x3x3
