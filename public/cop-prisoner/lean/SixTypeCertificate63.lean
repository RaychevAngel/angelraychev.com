import SixTypeObjective63Transfer
import SixTypeObjective63Delivery0
import SixTypeObjective63Delivery1
import SixTypeObjective63Delivery2
import SixTypeObjective63Delivery3
import SixTypeObjective63Delivery4
import SixTypeObjective63Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate63
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern63.pattern := by
  constructor
  · exact ⟨SixTypeObjective63Transfer.data, SixTypeObjective63Transfer.checked, SixTypeObjective63Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective63Delivery0.data, SixTypeObjective63Delivery0.checked, SixTypeObjective63Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective63Delivery1.data, SixTypeObjective63Delivery1.checked, SixTypeObjective63Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective63Delivery2.data, SixTypeObjective63Delivery2.checked, SixTypeObjective63Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective63Delivery3.data, SixTypeObjective63Delivery3.checked, SixTypeObjective63Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective63Delivery4.data, SixTypeObjective63Delivery4.checked, SixTypeObjective63Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective63Delivery5.data, SixTypeObjective63Delivery5.checked, SixTypeObjective63Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate63
