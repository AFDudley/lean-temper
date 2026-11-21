import ArmadaLean
open Lean Meta

/-- The 36 alias findings of alias-internal-36.json: declaration and variable. -/
def findings : List (Name × Name) := [
  (`ArmadaLean.Nitro.latest_state_finalizable_two, `c1),
  (`ArmadaLean.Nitro.latest_state_finalizable_two, `c2),
  (`ArmadaLean.Nitro.consensus_checkpoint_resolves, `c),
  (`ArmadaLean.Nitro.consensus_checkpoint_resolves, `t),
  (`ArmadaLean.Nitro.consensus_round_safe, `Ω1),
  (`ArmadaLean.Nitro.consensus_round_safe, `t),
  (`ArmadaLean.withPositionsFrom_leaf_matches, `start),
  (`ArmadaLean.Nitro.Adjudicator.dest_mem_requiredNodes, `m),
  (`ArmadaLean.Nitro.consensus_round_safe_core, `Ω1),
  (`ArmadaLean.Nitro.virtualTurnBound_mem, `c),
  (`ArmadaLean.Nitro.before_remove_mid, `l),
  (`ArmadaLean.Nitro.NonVacuity.concludeRound, `Ω),
  (`ArmadaLean.Nitro.NonVacuity.concludeRound, `sent0),
  (`ArmadaLean.Nitro.exists_topo_list, `n),
  (`ArmadaLean.Nitro.round_keeps_status, `Ω),
  (`ArmadaLean.Nitro.round_keeps_status, `t),
  (`ArmadaLean.recordStep_preserves_consistency, `c),
  (`ArmadaLean.withTreePositionsFrom_leaf_matches, `start),
  (`ArmadaLean.Nitro.consensus_round_safe_nil, `Ω1),
  (`ArmadaLean.Nitro.turboValueAlong_eq_add_credits_aux, `order),
  (`ArmadaLean.Nitro.turboValues_order_indep, `n),
  (`ArmadaLean.Nitro.latest_round_keeps_status_two, `c1),
  (`ArmadaLean.Nitro.latest_round_keeps_status_two, `c2),
  (`ArmadaLean.Nitro.latest_round_keeps_status_two, `t),
  (`ArmadaLean.Nitro.latest_round_keeps_status_two_ordered, `c1),
  (`ArmadaLean.Nitro.latest_round_keeps_status_two_ordered, `c2),
  (`ArmadaLean.Nitro.late_round_keeps_status, `c),
  (`ArmadaLean.Nitro.late_round_keeps_status, `t),
  (`ArmadaLean.Nitro.land_own_challenge_transitions_status, `c),
  (`ArmadaLean.Nitro.directly_funded_round, `t),
  (`ArmadaLean.Nitro.conclude_round_finalized, `Ω),
  (`ArmadaLean.Nitro.not_edge_of_before_split, `l),
  (`ArmadaLean.insertLeaves_leavesAt_new_matches, `tn),
  (`ArmadaLean.Nitro.mirror_land, `sx),
  (`ArmadaLean.Nitro.mirror_land, `sy),
  (`ArmadaLean.Nitro.NonVacuity.conclude_strategy, `Ω)]

/-- One finding, read from the elaborated declaration: the variable's position and
    binder kind, its equation's position and direction, whether the value mentions a
    later parameter, how many parameters mention the variable, and whether the proof
    term uses the equation. -/
def inspect (d v : Name) : MetaM String := do
  let ci ← getConstInfo d
  let some val := ci.value? (allowOpaque := true) | return s!"{d} {v}: no value"
  forallTelescope ci.type fun xs _ => do
    let names ← xs.mapM fun x => x.fvarId!.getUserName
    let some vi := names.findIdx? (· == v) | return s!"{d} {v}: variable not found"
    let x := xs[vi]!
    let bi ← x.fvarId!.getBinderInfo
    let mut hv? : Option (Nat × String × Expr) := none
    for j in [0:xs.size] do
      if hv?.isNone then
        let t ← instantiateMVars (← inferType xs[j]!)
        if t.isAppOfArity ``Eq 3 then
          let a := t.getArg! 1
          let b := t.getArg! 2
          if a == x && !b.containsFVar x.fvarId! then hv? := some (j, "v = e", b)
          else if b == x && !a.containsFVar x.fvarId! then hv? := some (j, "e = v", a)
    let some (hj, dir, e) := hv? | return s!"{d} {v}: no equation"
    let later := (List.range xs.size).filter fun k => k > vi && e.containsFVar xs[k]!.fvarId!
    let mut mention := 0
    for k in [0:xs.size] do
      if k != vi && k != hj then
        if (← inferType xs[k]!).containsFVar x.fvarId! then mention := mention + 1
    let body := (mkAppN val xs).headBeta
    let used := body.containsFVar xs[hj]!.fvarId!
    let vUsed := body.containsFVar x.fvarId!
    let kind := match bi with | .implicit => "implicit" | .strictImplicit => "strict-implicit" | .instImplicit => "instance" | .default => "explicit"
    return s!"{d.toString.replace "ArmadaLean." ""} {v}: var#{vi} {kind}; eq#{hj} {names[hj]!} ({dir}); value-uses-later-params {later.length}; params-mentioning-var {mention}; proof-uses-eq {used}; proof-uses-var {vUsed}"

def main : IO Unit := unsafe do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `ArmadaLean}] {} (loadExts := true)
  for (d, v) in findings do
    let (s, _) ← (inspect d v).run'.toIO { fileName := "inv", fileMap := default } { env }
    IO.println s
