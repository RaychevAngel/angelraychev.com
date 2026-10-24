import OddEndpointObjective118Transfer
import OddEndpointObjective118Delivery0
import OddEndpointObjective118Delivery1
import OddEndpointObjective118Delivery2
import OddEndpointObjective118Delivery3
import OddEndpointObjective118Delivery4
import OddEndpointObjective118Delivery5
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointCertificate118
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
open OddEndpointPattern118
noncomputable def certificates : Certificates residue patchAnchor where
  transfer := OddEndpointObjective118Transfer.certificate
  delivery := by
    intro j allowed
    apply Classical.choice
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by
      have finite : ∀ j : Fin 6, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by decide +kernel
      exact finite j
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨OddEndpointObjective118Delivery0.certificate⟩
    · exact ⟨OddEndpointObjective118Delivery1.certificate⟩
    · exact ⟨OddEndpointObjective118Delivery2.certificate⟩
    · exact ⟨OddEndpointObjective118Delivery3.certificate⟩
    · exact ⟨OddEndpointObjective118Delivery4.certificate⟩
    · exact ⟨OddEndpointObjective118Delivery5.certificate⟩
#print axioms certificates
end Delivery.OddEndpointCertificate118
