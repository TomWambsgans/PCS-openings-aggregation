-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Review experiment (F0a/F2/F4 review):
-- the axioms of the three layers' end theorems and of the kernel-decided facts they use.
import QuotientSecurity.Statement
import WhirBridge
import Compose.ComposedKC
import Compose.Extract

#print axioms QuotientSecurity.Instance.soundness_circuit
#print axioms QuotientSecurity.Instance.soundness_circuit_bits
#print axioms QuotientSecurity.laid_wiringOf
#print axioms QuotientSecurity.Instance.relation_statementWords
#print axioms WhirBridge.ours_sound
#print axioms WhirBridge.opening_sound
#print axioms WhirBridge.openingVerify_imp
#print axioms WhirBridge.opening_bound_le
#print axioms WhirBridge.layouts_ok
#print axioms WhirBridge.layouts_valid
#print axioms WhirBridge.layouts_shape
#print axioms WhirBridge.candidates_ours
#print axioms WhirBridge.variantQueries_eq
#print axioms Compose.knowledgeSoundness_merkle_kc
#print axioms Compose.knowledgeSoundness_merkle_certified
#print axioms Compose.wordOfMerkle_eq_extract
