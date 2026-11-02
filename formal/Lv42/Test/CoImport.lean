-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
--
-- Run from `formal/EndToEnd`: `lake env lean ../Lv42/Test/CoImport.lean` (after `lake build Lv42 WhirBridge
-- PcsQuotient Soundness`).
import Lv42
import LeanVM
import Statement.LeanVmVerifier
import WhirBridge
import PcsQuotient
import Soundness

-- Lv42 next to head's Keccak-era leanVM (its whole `LeanVM` root, `Statement.LeanIsa` included),
-- WhirBridge and the Statement: no declaration of one clashes with the other's.
#check @Lv42.Protocol.M3Holds
#check @LeanVM.Protocol.M3Holds
#check @Lv42.Semantics.ValidExecution
#check @LeanVM.Semantics.ValidExecution
example (n : ℕ) : LeanVM.Protocol.Column n = LeanVM.Protocol.Column n := rfl
