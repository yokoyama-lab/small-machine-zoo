import Lean
import URTMMeta
/-!
  Whole-environment audit run by tools/verify.py. For each imported declaration
  in URTMMeta and URTM, collect axiom dependencies and reject unsafe, opaque,
  implemented_by, or extern declarations. Source comments are not evidence.
-/
open Lean

def sweep (roots : List String) : CoreM Unit := do
  let env ← getEnv
  let mut axs : NameSet := {}
  let mut cnt := 0
  let mut thms := 0
  let mut flagged : Array String := #[]
  let mut noncomp : Array Name := #[]
  for (nm, ci) in env.constants.map₁.toList do
    match env.getModuleIdxFor? nm with
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      if roots.contains mod.getRoot.toString then
        cnt := cnt + 1
        if ci.isTheorem then thms := thms + 1
        for a in (← collectAxioms nm) do axs := axs.insert a
        if ci.isUnsafe then flagged := flagged.push s!"unsafe:{nm}"
        if ci matches .opaqueInfo .. then flagged := flagged.push s!"opaque:{nm}"
        if (Compiler.getImplementedBy? env nm).isSome then flagged := flagged.push s!"implemented_by:{nm}"
        if isExtern env nm then flagged := flagged.push s!"extern:{nm}"
        if isNoncomputable env nm then noncomp := noncomp.push nm
    | none => pure ()
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let extra := axs.toList.filter (fun a => !std.contains a)
  if !extra.isEmpty || !flagged.isEmpty then
    throwError "Unexpected axioms or unsafe declarations: {extra}; {flagged}"
  IO.println s!"SWEEP roots={roots} constants={cnt} theorems={thms} nonstandard_axioms={extra} flagged={flagged.toList} noncomputable={noncomp.toList}"

#eval sweep ["URTMMeta", "URTM"]
