/-
  **The decoder shared by every record machine** (docs/24 P7a–P7d, P9).

  For a machine-specific readout `readN : Code → Option (ℕ × List ℕ)` that returns, from a code
  of U's halting ID, the number `|C|` of CTSH productions and the final CTSH string as numbers
  (`1 = Y`, anything else `= N`; `U10_8.chOf`), the decoder is

      dOf readN g = (readN g).bind fun p => decMid p.1 (p.2.map chOf)

  with the middle decoder `Chain10_8.decMid` (ϕ⁻¹, the 2-TS readback, the TRM readback) of the
  (10,8) chain. `dOf_computable`: it is computable as soon as `readN` is primitive recursive.

  The readout is on numbers, so that no `Primcodable` instance on `CTSH.Ch` appears in the
  statement (`ComputableDec` and `ComputableEnc` use two different ones).
-/
import LeanUniv.ComputableDec

namespace URTM.Univ.GenDec
open URTM URTM.Spec Primrec

attribute [local instance] ComputableDec.chPrimcodable ComputableDec.ch_finite

/-- **The decoder** built from a machine-specific readout `readN`. -/
def dOf (readN : Code → Option (ℕ × List ℕ)) (g : Code) : Option Code :=
  (readN g).bind fun p => Chain10_8.decMid p.1 (p.2.map U10_8.chOf)

theorem dOf_primrec {readN : Code → Option (ℕ × List ℕ)} (h : Primrec readN) :
    Primrec (dOf readN) :=
  (option_bind h (ComputableDec.decMid_primrec.comp (fst.comp snd)
    (list_map (snd.comp snd) (ComputableDec.chOf_primrec.comp snd).to₂)).to₂).of_eq fun _ => rfl

/-- The decoder is computable when the readout is primitive recursive. -/
theorem dOf_computable {readN : Code → Option (ℕ × List ℕ)} (h : Primrec readN) :
    Computable (dOf readN) := (dOf_primrec h).to_comp

end URTM.Univ.GenDec
