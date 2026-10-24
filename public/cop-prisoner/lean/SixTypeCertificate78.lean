import SixTypeObjective78Transfer
import SixTypeObjective78Delivery0
import SixTypeObjective78Delivery1
import SixTypeObjective78Delivery2
import SixTypeObjective78Delivery3
import SixTypeObjective78Delivery4
import SixTypeObjective78Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate78
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern78.pattern := by
  constructor
  · exact ⟨SixTypeObjective78Transfer.data, SixTypeObjective78Transfer.checked, SixTypeObjective78Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective78Delivery0.data, SixTypeObjective78Delivery0.checked, SixTypeObjective78Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective78Delivery1.data, SixTypeObjective78Delivery1.checked, SixTypeObjective78Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective78Delivery2.data, SixTypeObjective78Delivery2.checked, SixTypeObjective78Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective78Delivery3.data, SixTypeObjective78Delivery3.checked, SixTypeObjective78Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective78Delivery4.data, SixTypeObjective78Delivery4.checked, SixTypeObjective78Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective78Delivery5.data, SixTypeObjective78Delivery5.checked, SixTypeObjective78Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate78
