-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.VerifierH

/-!
# When the whole verifier accepts

`verifyWithH` (the run, then five `PCS_OPEN` calls) accepts at pure `H`, `F` when the run accepts with the three
point claims on `C1`, `C2` and the setup in order and Flock's claim on `A0`, `B0`, and each of the five openings
accepts (`verifyWithH_of_calls`).
-/

namespace UniComplete

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- **The verifier accepts** when its run does, with the three point claims and Flock's matrices' claim, and the
five openings accept. -/
theorem verifyWithH_of_calls (H : List UInt8 → Digest) (F : KeccakState → KeccakState) (shape : Shape)
    (iv : List UInt8) (roots : SetupRoots) (input : Vector UInt8 32) (π : UniProof) (o : Outcome) (r : Reduced)
    (p1 p2 p3 : List E) (v1 v2 v3 : E) (mc : Flock.MatrixClaim)
    (hrun : runWithH (m := Id) (fun b ↦ pure (H b)) shape iv input.toList π.stream (.flock flockMain) .point = o)
    (hacc : o.accepts = true) (hres : o.result = .ok r)
    (hop : r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none), (.setup, .point p3 v3 none)])
    (hmat : r.matrices = some mc)
    (h1 : pcsOpenWithH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s))
      (layoutWordVars ((layoutWords shape).getD 0 [])) (rootOf r.roots.1) [⟨p1, v1⟩] π.c1 = true)
    (h2 : pcsOpenWithH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s))
      (layoutWordVars ((layoutWords shape).getD 1 [])) (rootOf r.roots.2) [⟨p2, v2⟩] π.c2 = true)
    (h3 : pcsOpenWithH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s))
      (layoutWordVars ((layoutWords shape).getD 2 [])) roots.bytecode [⟨p3, v3⟩] π.setup = true)
    (ha : pcsOpenWithH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s))
      (layoutWordVars ((layoutWords shape).getD 3 [])) roots.a0 [⟨mc.point, mc.a⟩] π.a0 = true)
    (hb : pcsOpenWithH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s))
      (layoutWordVars ((layoutWords shape).getD 4 [])) roots.b0 [⟨mc.point, mc.b⟩] π.b0 = true) :
    verifyWithH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s)) shape iv roots input π = true := by
  unfold verifyWithH
  simp only [hrun]
  simp only [bind, pure, List.getD_eq_getElem?_getD] at h1 h2 h3 ha hb ⊢
  simp only [hacc, hres, hop, hmat, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp [commitments, h1, h2, h3, ha, hb]
  rfl

end UniComplete

/-- info: 'UniComplete.verifyWithH_of_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.verifyWithH_of_calls
