(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols
open EcLocation
open EcPath
open EcParsetree
open EcTypes
open EcDecl
open EcModules

module Mid  = EcIdent.Mid
module MSym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type action = {
  for_loading  : exn -> exn;
}

(* -------------------------------------------------------------------- *)
module type IOptions = sig
  type option

  val register          : action -> exn -> option
  val register_identity : exn -> option

  type options

  val init         : unit -> options
  val get          : options -> option -> exn
  val set          : options -> option -> exn -> options
  val for_loading  : options -> options
  val for_subscope : options -> options
end

(* -------------------------------------------------------------------- *)
module Options : IOptions = struct
  type option = int

  type options = (action * exn) Mint.t

  let known_options : options ref = ref Mint.empty

  let identity = {
    for_loading  = (fun x -> x);
  }

  let count = ref 0
  let initialized = ref false

  let register action exn =
    if !initialized then assert false;
    let opt = !count in
    incr count;
    known_options := Mint.add opt (action,exn) !known_options;
    opt

  let register_identity = register identity

  let init () =
    initialized := true;
    !known_options

  let get options opt =
    snd (Mint.find opt options)

  let set options opt exn =
    Mint.change
      (function None -> assert false | Some(act,_) -> Some (act, exn))
      opt options

  let for_loading options =
    Mint.map (fun (act, exn) -> act, act.for_loading exn) options

  let for_subscope options = options
end

(* -------------------------------------------------------------------- *)
module Notifier = struct
  exception Verbose of [`ForLoading | `Verbose of bool]

  let for_loading = function
    | Verbose _ -> Verbose `ForLoading
    | exn -> exn

  let default = Verbose (`Verbose true)

  let mode = Options.register { for_loading } default

  let verbose options =
    match Options.get options mode with
    | Verbose b -> b
    | _ -> assert false

  let set options b =
    match Options.get options mode with
    | Verbose (`ForLoading) -> options
    | Verbose (`Verbose _)  -> Options.set options mode (Verbose (`Verbose b))
    | _ -> assert false
end

(* -------------------------------------------------------------------- *)
module Check_mode = struct
  exception Full_check    (* Disable: checkproof off, i.e. check everything *)
  exception Check of bool (* true check proofs, false do not check *)

  let for_loading = function
    | Check _ -> Check false
    | exn     -> exn

  let default = Check true

  let mode = Options.register { for_loading } default

  let check options =
    match Options.get options mode with
    | Check b -> b
    | _       -> true

  let check_proof options b =
    match Options.get options mode with
    | Check b' when b <> b' ->
        Options.set options mode (Check b')
    | _ -> options

  let full_check options =
    Options.set options mode Full_check
end

(* -------------------------------------------------------------------- *)
module Prover_info = struct
  exception PI of EcProvers.prover_infos

  let npi = Options.register_identity (PI EcProvers.dft_prover_infos)

  let set options pi =
    Options.set options npi (PI pi)

  let get options =
    match Options.get options npi with
    | PI pi -> pi
    | _     -> assert false
end

(* -------------------------------------------------------------------- *)
type proof_uc = {
  puc_name : string;
  puc_jdg :  EcBaseLogic.judgment_uc;
}

(* -------------------------------------------------------------------- *)
type scope = {
  sc_name       : symbol;
  sc_env        : EcEnv.env;
  sc_top        : scope option;
  sc_loaded     : (EcEnv.ctheory_w3 * symbol list) Msym.t;
  sc_required   : symbol list;
  sc_pr_uc      : proof_uc list;
  sc_options    : Options.options ref;
}

(* -------------------------------------------------------------------- *)
let empty =
  let env = EcEnv.initial in
    { sc_name       = EcPath.basename (EcEnv.root env);
      sc_env        = EcEnv.initial;
      sc_top        = None;
      sc_loaded     = Msym.empty;
      sc_required   = [];
      sc_pr_uc      = [];
      sc_options    = ref (Options.init ());
    }

(* -------------------------------------------------------------------- *)
let name (scope : scope) =
  scope.sc_name

(* -------------------------------------------------------------------- *)
let path (scope : scope) =
  EcEnv.root scope.sc_env

(* -------------------------------------------------------------------- *)
let env (scope : scope) =
  scope.sc_env

(* -------------------------------------------------------------------- *)
let attop (scope : scope) =
  scope.sc_top = None

(* -------------------------------------------------------------------- *)
let goal (scope : scope) =
  scope.sc_pr_uc

(* -------------------------------------------------------------------- *)
let verbose (scope : scope) =
  match Notifier.verbose !(scope.sc_options) with
  | `ForLoading -> false
  | `Verbose b  -> b

(* -------------------------------------------------------------------- *)
let set_verbose (scope : scope) (b : bool) =
  scope.sc_options := Notifier.set !(scope.sc_options) b;
  scope

(* -------------------------------------------------------------------- *)
let for_loading (scope : scope) =
  { empty with
      sc_loaded  = scope.sc_loaded;
      sc_options = ref (Options.for_loading !(scope.sc_options)); }

(* -------------------------------------------------------------------- *)
let subscope (scope : scope) (name : symbol) =
  let env = EcEnv.Theory.enter name scope.sc_env in

  { sc_name       = name;
    sc_env        = env;
    sc_top        = Some scope;
    sc_loaded     = scope.sc_loaded;
    sc_required   = scope.sc_required;
    sc_pr_uc      = [];
    sc_options    = ref (Options.for_subscope !(scope.sc_options));
  }

(* -------------------------------------------------------------------- *)
module Op = struct
  open EcTypes
  open EcDecl
  open EcEnv

  module TT = EcTyping

  let bind (scope : scope) ((x, op) : _ * operator) =
    { scope with
        sc_env = EcEnv.Op.bind x op scope.sc_env; }

  let add (scope : scope) (op : poperator located) =
    let op = op.pl_desc and loc = op.pl_loc in
    let ue = TT.ue_for_decl scope.sc_env (loc, op.po_tyvars) in
    let tp = TT.tp_relax in

    let (ty, body) =
      match op.po_def with
      | POabstr pty ->
          TT.transty tp scope.sc_env ue pty, None

      | POconcr (bd, pty, pe) ->
          let env     = scope.sc_env in
          let codom   = TT.transty tp env ue pty in 
          let env, xs = TT.transbinding env ue bd in
          let body    = TT.transexpcast env ue codom pe in
          let lam     = EcTypes.e_lam xs body in
            lam.EcTypes.e_ty, Some lam
    in

    let uni     = Tuni.subst (EcUnify.UniEnv.close ue) in
    let body    = omap body (e_mapty uni) in
    let ty      = uni ty in
    let tparams = EcUnify.UniEnv.tparams ue in
    let tyop    = EcDecl.mk_op tparams ty body in

      bind scope (unloc op.po_name, tyop)
end

(* -------------------------------------------------------------------- *)
module Pred = struct
  module TT = EcTyping

  let add (scope : scope) (op : ppredicate located) =
    let op = op.pl_desc and loc = op.pl_loc in
    let ue     = TT.ue_for_decl scope.sc_env (loc, op.pp_tyvars) in
    let tp     = TT.tp_relax in
    let dom, body = 
      match op.pp_def with
      | PPabstr ptys -> 
        List.map (TT.transty tp scope.sc_env ue) ptys, None
      | PPconcr(bd,pe) ->
        let env, xs = TT.transbinding scope.sc_env ue bd in
        let body = TT.transformula env ue pe in
        let dom = List.map snd xs in
        let xs = List.map (fun (x,ty) -> x, EcFol.GTty ty) xs in
        let lam = EcFol.f_lambda xs body in
        dom, Some lam in
    let uni     = EcUnify.UniEnv.close ue in
    let body    = omap body (EcFol.Fsubst.uni uni) in
    let dom     = List.map (Tuni.subst uni) dom in
    let tparams = EcUnify.UniEnv.tparams ue in
    let tyop    = EcDecl.mk_pred tparams dom body in

      Op.bind scope (unloc op.pp_name, tyop)

end

(* -------------------------------------------------------------------- *)
module Ty = struct
  open EcDecl
  open EcTyping

  let bind (scope : scope) ((x, tydecl) : (_ * tydecl)) =
    { scope with
        sc_env = EcEnv.Ty.bind x tydecl scope.sc_env; }

  let add (scope : scope) info =
    let (args, name) = info.pl_desc and loc = info.pl_loc in
    let ue     = ue_for_decl scope.sc_env (loc, Some args) in
    let tydecl = {
      tyd_params = EcUnify.UniEnv.tparams ue;
      tyd_type   = None;
    } in
      bind scope (unloc name, tydecl)

  let define (scope : scope) info body =
    let (args, name) = info.pl_desc and loc = info.pl_loc in
    let ue     = ue_for_decl scope.sc_env (loc, Some args) in
    let body   = transty tp_tydecl scope.sc_env ue body in
    let tydecl = {
      tyd_params = EcUnify.UniEnv.tparams ue;
      tyd_type   = Some body;
    } in
      bind scope (unloc name, tydecl)
end

(* -------------------------------------------------------------------- *)
module Mod = struct
  let bind (scope : scope) (m : module_expr) =
    { scope with
        sc_env = EcEnv.Mod.bind m.me_name m scope.sc_env; }

  let add (scope : scope) (name : symbol) m =
    let m = EcTyping.transmod scope.sc_env name m in
    bind scope m
end

(* -------------------------------------------------------------------- *)
module ModType = struct
  let bind (scope : scope) ((x, tysig) : _ * module_sig) =
    { scope with
        sc_env = EcEnv.ModTy.bind x tysig scope.sc_env; }

  let add (scope : scope) (name : symbol) (i : pmodule_sig) =
    let tysig = EcTyping.transmodsig scope.sc_env name i in
      bind scope (name, tysig)
end

(* -------------------------------------------------------------------- *)
module Theory = struct
  open EcTheory

  exception TopScope

  (* ------------------------------------------------------------------ *)
  let bind (scope : scope) ((x, cth) : _ * EcEnv.ctheory_w3) =
    { scope with
        sc_env = EcEnv.Theory.bind x cth scope.sc_env; }

  (* ------------------------------------------------------------------ *)
  let required (scope : scope) (name : symbol) =
    List.exists (fun x -> x = name) scope.sc_required

  (* ------------------------------------------------------------------ *)
  let enter (scope : scope) (name : symbol) =
    subscope scope name

  (* ------------------------------------------------------------------ *)
  let rec require_loaded id scope =
    if required scope id then
      scope
    else
      match Msym.find_opt id scope.sc_loaded with
      | Some (rth, ids) ->
          let scope = List.fold_right require_loaded ids scope in
          let env   = EcEnv.Theory.require id rth scope.sc_env in
            { scope with
              sc_env = env;
              sc_required = id :: scope.sc_required; }

      | None -> assert false

  (* -------------------------------------------------------------------- *)
  let exit_r (scope : scope) =
    match scope.sc_top with
    | None     -> raise TopScope
    | Some sup ->
        let cth    = EcEnv.Theory.close scope.sc_env in
        let loaded = scope.sc_loaded in
        let required = scope.sc_required in
        let sup = { sup with sc_loaded = loaded } in
          ((cth, required), scope.sc_name, sup)

  (* ------------------------------------------------------------------ *)
  let exit (scope : scope) =
    let ((cth, required), name, scope) = exit_r scope in
    let scope = List.fold_right require_loaded required scope in
      (name, bind scope (name, cth))

  (* ------------------------------------------------------------------ *)
  let import (scope : scope) (name : qsymbol) =
    let path = fst (EcEnv.Theory.lookup name scope.sc_env) in
    { scope with
        sc_env = EcEnv.Theory.import path scope.sc_env }

  (* ------------------------------------------------------------------ *)
  let export (scope : scope) (name : qsymbol) =
    let path = fst (EcEnv.Theory.lookup name scope.sc_env) in
    { scope with
      sc_env = EcEnv.Theory.export path scope.sc_env }

  (* ------------------------------------------------------------------ *)
  let check_end_required scope thname =
    if scope.sc_name <> thname then
      begin
        let msg =
          Printf.sprintf
            "end-of-file while processing external theory %s %s"
            scope.sc_name thname in
        failwith msg
      end;
    if scope.sc_pr_uc <> [] then
      let msg =
        Printf.sprintf
          "end-of-file while processing proof %s" scope.sc_name
      in
        failwith msg

  (* -------------------------------------------------------------------- *)
  let require (scope : scope) (name : symbol) loader =
    if required scope name then
      scope
    else
      match Msym.find_opt name scope.sc_loaded with
      | Some _ -> require_loaded name scope

      | None ->
          let imported = enter (for_loading scope) name in
          let thname   = imported.sc_name in
          let imported = loader imported in
          check_end_required imported thname;
          let cthr, name, imported = exit_r imported in
          let scope =
            { scope with
                sc_loaded = Msym.add name cthr imported.sc_loaded; }
          in
            require_loaded name scope

  (* ------------------------------------------------------------------ *)
  let clone (scope : scope) (thcl : theory_cloning) =
    let (name, nth) = EcThCloning.clone scope.sc_env thcl in
      { scope with
          sc_env =
            EcEnv.Theory.bind name nth scope.sc_env; }

  (* ------------------------------------------------------------------ *)
  let import_w3 scope dir file renaming =
    let mk_renaming (l,k,s) =
      let k =
        match k with
        | RNty -> EcWhy3.RDts
        | RNop -> EcWhy3.RDls
        | RNpr -> EcWhy3.RDpr
      in
        (l, k, s)
    in

    let renaming = List.map mk_renaming renaming in
    let env      = fst (EcEnv.import_w3_dir scope.sc_env dir file renaming) in
      { scope with sc_env = env }
end

(* -------------------------------------------------------------------- *)
module Prover = struct
  exception Unknown_prover of string

  let pp_error fmt exn =
    match exn with
    | Unknown_prover s ->
        Format.fprintf fmt "Unknown prover %s" s
    | _ -> raise exn

  let _ = EcPException.register pp_error

  let check_prover_name name =
    let s = unloc name in
    if not (EcProvers.check_prover_name s) then
      EcLocation.locate_error name.pl_loc (Unknown_prover s);
    s

  let mk_prover_info scope max time ns =
    let dft = Prover_info.get !(scope.sc_options) in
    let time = odfl dft.EcProvers.prover_timelimit time in
    let time = if time < 1 then 1 else time in
    let provers = odfl dft.EcProvers.prover_names ns in
    let provers = List.filter (fun s -> s <> "Yices")
        (Array.to_list provers) in
    let max     = odfl dft.EcProvers.prover_max_run max in
    { EcProvers.prover_max_run   = max;
      EcProvers.prover_names     = Array.of_list provers;
      EcProvers.prover_timelimit = time }

  let set_prover_info scope max time ns =
    let pi = mk_prover_info scope max time ns in
      scope.sc_options := Prover_info.set !(scope.sc_options) pi;
      scope

  let set_all scope =
    let provers = Array.of_list (EcProvers.known_provers ()) in
    set_prover_info scope None None (Some provers)

  let set_default scope max provers =
    let provers =
      match provers with
      | None -> List.filter EcProvers.check_prover_name ["Alt-Ergo";"Z3";"Vampire";"Eprover";"Yices"]
      | Some ps -> List.iter (fun s -> if not (EcProvers.check_prover_name s) then raise (Unknown_prover s)) ps;ps
    in
    let provers = Array.of_list provers in
    let time = 3 in
    set_prover_info scope (Some max) (Some time) (Some provers)
(*    set_all scope*)

  let process scope pi =
    let max  = pi.pprov_max in
    let time = pi.pprov_time in
    let ns   = pi.pprov_names in
    let ns   = omap ns (List.map check_prover_name) in
    let ns   = omap ns Array.of_list in
    set_prover_info scope max time ns

  let mk_prover_info scope pi =
    let max  = pi.pprov_max in
    let time = pi.pprov_time in
    let ns   = pi.pprov_names in
    let ns   = omap ns (List.map check_prover_name) in
    let ns   = omap ns Array.of_list in
    mk_prover_info scope max time ns

  let full_check scope =
    scope.sc_options := Check_mode.full_check !(scope.sc_options);
    scope

  let check_proof scope b =
    scope.sc_options := Check_mode.check_proof !(scope.sc_options) b;
    scope
end

module Tactic = struct
  open EcFol
  open EcBaseLogic
  open EcLogic
  open EcPhl

  module TT = EcTyping
  module UE = EcUnify.UniEnv

  type tac_error =
    | UnknownHypSymbol of symbol
    | UnknownAxiom of qsymbol
    | UnknownOperator of qsymbol
    | BadTyinstance
    | NothingToIntro
    | FormulaExpected
    | MemoryExpected
    | UnderscoreExpected
    | ModuleExpected
    | ElimDoNotWhatToDo
    | NoCurrentGoal

  exception TacError of tac_error

  let pp_tac_error fmt =
    function
      | UnknownHypSymbol s ->
        Format.fprintf fmt "Unknown hypothesis or logical variable %s" s
      | UnknownAxiom qs ->
        Format.fprintf fmt "Unknown axioms or hypothesis : %a"
          pp_qsymbol qs
      | UnknownOperator qs ->
        Format.fprintf fmt "Unknown operator or logical variable %a"
          pp_qsymbol qs
      | BadTyinstance ->
        Format.fprintf fmt "Invalid type instance"
      | NothingToIntro ->
        Format.fprintf fmt "Nothing to introduce"
      | FormulaExpected ->
        Format.fprintf fmt "formula expected"
      | MemoryExpected ->
        Format.fprintf fmt "Memory expected"
      | UnderscoreExpected ->
        Format.fprintf fmt "_ expected"
      | ModuleExpected ->
        Format.fprintf fmt "module expected"
      | ElimDoNotWhatToDo ->
        Format.fprintf fmt "Elim : do not known what to do"
      | NoCurrentGoal ->
        Format.fprintf fmt "No current goal"

  let _ = EcPException.register (fun fmt exn ->
    match exn with
    | TacError e -> pp_tac_error fmt e
    | _ -> raise exn)

  let error loc e = EcLocation.locate_error loc (TacError e)

  let process_tyargs env hyps tvi =
    let ue = EcUnify.UniEnv.create (Some hyps.h_tvar) in
      omap tvi (TT.transtvi env ue)

  let process_instanciate env hyps ({pl_desc = pq; pl_loc = loc} ,tvi) =
    let (p, ax) =
      try EcEnv.Ax.lookup pq env
      with _ -> error loc (UnknownAxiom pq) in
    let args = process_tyargs env hyps tvi in
    let args =
      match ax.EcDecl.ax_tparams, args with
      | [], None -> []
      | [], Some _ -> error loc BadTyinstance
      | ltv, Some (UE.TVIunamed l) ->
          if not (List.length ltv = List.length l) then error loc BadTyinstance;
          l
      | ltv, Some (UE.TVInamed l) ->
          let get id =
            try List.assoc (EcIdent.name id) l
            with _ -> error loc BadTyinstance in
          List.map get ltv
      | _, None -> error loc BadTyinstance in
    p,args

  let process_global loc env tvi g =
    let hyps = get_hyps g in
    let p, tyargs = process_instanciate env hyps tvi in
    set_loc loc t_glob env p tyargs g

  let process_assumption loc env (pq,tvi) g =
    let hyps,concl = get_goal g in
    match pq with
    | None ->
        if (tvi <> None) then error loc BadTyinstance;
        let h  =
          try find_in_hyps env concl hyps
          with _ -> assert false in
        t_hyp env h g
    | Some pq ->
        match unloc pq with
        | ([],ps) when LDecl.has_hyp ps hyps ->
            if (tvi <> None) then error pq.pl_loc BadTyinstance;
            set_loc loc (t_hyp env (fst (LDecl.lookup_hyp ps hyps))) g
        | _ -> process_global loc env (pq,tvi) g

  let process_intros env pis =
    let mk_id s = EcIdent.create (odfl "_" s) in
      t_intros env (List.map (lmap mk_id) pis)

  let process_elim_arg env hyps oty a =
    let ue  = EcUnify.UniEnv.create (Some hyps.h_tvar) in
    let env = tyenv_of_hyps env hyps in
    match a.pl_desc, oty with
    | EA_form pf, Some (GTty ty) ->
      let ff = TT.transform env ue pf ty in
      AAform (EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) ff)
    | _, Some (GTty _) ->
      error a.pl_loc FormulaExpected
    | EA_mem mem, Some (GTmem _) ->
      AAmem (TT.transmem env mem)
    | _, Some (GTmem _)->
      error a.pl_loc MemoryExpected
    | EA_none, None ->
      AAnode
    | EA_mp mp , Some (GTmodty _) ->
      let (mp, mt) = TT.trans_msymbol env (mk_loc a.pl_loc mp) in
        AAmp (mp, mt)
    | _, Some (GTmodty _) ->
      error a.pl_loc ModuleExpected
    | _, None ->
      error a.pl_loc UnderscoreExpected

  let process_form_opt env hyps pf oty =
    let env = tyenv_of_hyps env hyps in
    let ue  = EcUnify.UniEnv.create (Some hyps.h_tvar) in
    let ff  = TT.transform_opt env ue pf oty in
    EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) ff

  let process_form env hyps pf ty =
    process_form_opt env hyps pf (Some ty)

  let process_formula env g pf =
    let hyps = get_hyps g in
    process_form env hyps pf tbool

  let process_phl_form ty env g phi =
    let hyps, concl = get_goal g in
    let m = 
      try 
        let hs = set_loc phi.pl_loc destr_hoareS concl in
        hs.hs_m
      with _ ->
        let hs = set_loc phi.pl_loc destr_bdHoareS concl in
        hs.bhs_m
    in
    let env = EcEnv.Memory.push_active m env in
    process_form env hyps phi ty

  let process_prhl_form ty env g phi =
    let hyps, concl = get_goal g in
    let es = set_loc phi.pl_loc destr_equivS concl in
    let env = EcEnv.Memory.push_all [es.es_ml; es.es_mr] env in
    process_form env hyps phi ty

  let process_phl_formula = process_phl_form tbool

  let process_prhl_formula = process_prhl_form tbool
      
  let process_mkn_apply process_cut env pe (juc, _ as g) = 
    let hyps = get_hyps g in
    let args = pe.fp_args in
    let (juc,fn), fgs =
      match pe.fp_kind with
      | FPNamed (pq,tvi) ->
        begin match unloc pq with
        | ([],ps) when LDecl.has_hyp ps hyps ->
          (* FIXME warning if tvi is not None *)
          let id,_ = LDecl.lookup_hyp ps hyps in
          mkn_hyp juc hyps id, []
        | _ ->
          let p,tys = process_instanciate env hyps (pq,tvi) in
          mkn_glob env juc hyps p tys, []
        end
      | FPCut pf ->
        let f = process_cut env g pf in
        let juc, fn = new_goal juc (hyps, f) in
        (juc,fn), [fn]
    in
    let (juc,an), ags = mkn_apply process_elim_arg env (juc,fn) args in
    (juc,an), fgs@ags

  let process_apply loc env pe (_,n as g) =
    let (juc,an), gs = process_mkn_apply process_formula env pe g in
    set_loc loc (t_use env an gs) (juc,n)

  let process_elim loc env pe (_,n as g) =
    let (juc,an), gs = process_mkn_apply process_formula env pe g in
    let (_,f) = get_node (juc, an) in
    t_on_first (set_loc loc (t_elim env f) (juc,n)) (t_use env an gs)

  let process_rewrite loc env (s,pe) (_,n as g) =
    set_loc loc (t_rewrite_node env 
                   (process_mkn_apply process_formula env pe g) s) n

  let process_trivial scope pi env g =
    let pi = Prover.mk_prover_info scope pi in
    t_trivial pi env g

  let process_cut name env phi g =
    let phi = process_formula env g phi in
    t_on_last (t_cut env phi g)
      (process_intros env [lmap (fun x -> Some x) name])

  let process_generalize env l =
    let pr1 pf g =
      let hyps = get_hyps g in
      match pf.pl_desc with
      | PFident({pl_desc = ([],s)},None) when LDecl.has_symbol s hyps ->
        let id = fst (LDecl.lookup s hyps) in
        t_generalize_hyp env id g
      | _ ->
        let f = process_form_opt env hyps pf None in
        t_generalize_form None env f g in
    t_lseq (List.rev_map pr1 l)

  let process_clear l g =
    let hyps = get_hyps g in
    let toid ps =
      let s = ps.pl_desc in
      if LDecl.has_symbol s hyps then (fst (LDecl.lookup s hyps))
      else error ps.pl_loc (UnknownHypSymbol s) in
    let ids = EcIdent.Sid.of_list (List.map toid l) in
    t_clear ids g

  let process_exists env fs g =
    gen_t_exists process_elim_arg env fs g

  let process_change env pf g =
    let f = process_formula env g pf in
    set_loc pf.pl_loc (t_change env f) g

  let process_simplify env ri g =
    let hyps = get_hyps g in
    let delta_p, delta_h =
      match ri.pdelta with
      | None -> None, None
      | Some l ->
        let sop = ref Sp.empty and sid = ref EcIdent.Sid.empty in
        let do1 ps =
          match ps.pl_desc with
          | ([],s) when LDecl.has_symbol s hyps ->
            let id = fst (LDecl.lookup s hyps) in
            sid := EcIdent.Sid.add id !sid;
          | qs ->
            let p =
              try EcEnv.Op.lookup_path qs env
              with _ -> error ps.pl_loc (UnknownOperator qs) in
            sop := Sp.add p !sop in
        List.iter do1 l;
        Some !sop, Some !sid in
    let ri = {
      EcReduction.beta    = ri.pbeta;
      EcReduction.delta_p = delta_p;
      EcReduction.delta_h = delta_h;
      EcReduction.zeta    = ri.pzeta;
      EcReduction.iota    = ri.piota;
      EcReduction.logic   = ri.plogic; 
      EcReduction.modpath = ri.pmodpath;
    } in
    t_simplify env ri g

  let process_elimT loc env (pf,qs) g =
    let p = set_loc qs.pl_loc (EcEnv.Ax.lookup_path qs.pl_desc) env in
    let f = process_form_opt env (get_hyps g) pf None in
    t_seq (set_loc loc (t_elimT env f p))
      (t_simplify env EcReduction.beta_red) g

  let process_case loc env pf g =
    let concl = get_concl g in
    match concl.f_node with
    | FhoareS _ ->
      let f = process_phl_formula env g pf in
      t_hoare_case f g
    | FequivS _ ->
      let f = process_prhl_formula env g pf in
      t_equiv_case f g
    | _ ->
      let f = process_formula env g pf in
      t_seq (set_loc loc (t_case env f))
        (t_simplify env EcReduction.betaiota_red) g

  let process_subst loc env ri g =
    if ri = [] then t_subst_all env g
    else
      let hyps = get_hyps g in
      let totac ps =
        let s = ps.pl_desc in
        try t_subst1 env (Some (fst (LDecl.lookup_var s hyps)))
        with _ -> error ps.pl_loc (UnknownHypSymbol s) in
      let tacs = List.map totac ri in
      set_loc loc (t_lseq tacs) g

  let process_app env dir k phi bd_opt g =
    let concl = get_concl g in
    match k, bd_opt with
      | Single i, None when is_hoareS concl ->
        let phi = process_phl_formula env g phi in
        t_hoare_app i phi g
      | Single i, _ when is_bdHoareS concl ->
        let phi = process_phl_formula env g phi in
        let bd_opt = omap bd_opt (process_phl_form treal env g) in
        t_bdHoare_app dir i phi bd_opt g
      | Double(i,j), None ->
        let phi = process_prhl_formula env g phi in
        t_equiv_app (i,j) phi g
      | Single _, None ->
        cannot_apply "app" "wrong position parameter"
      | _, Some _ ->
        cannot_apply "app" "optional bound parameter not supported"

  let process_while env phi g =
    let concl = get_concl g in
    if is_hoareS concl then
      t_hoare_while env (process_phl_formula env g phi) g
    else if is_equivS concl then
      t_equiv_while env (process_prhl_formula env g phi) g
    else cannot_apply "while" "the conclusion is not a hoare or a equiv"

  let process_call env side pre post g =
    let hyps,concl = get_goal g in
    match concl.f_node, side with
    | FhoareS hs, None ->
      let (_,f,_),_ = s_last_call "call" hs.hs_s in
      let penv, qenv = EcEnv.Fun.hoareF f env in
      let pre  = process_form penv hyps pre tbool in
      let post = process_form qenv hyps post tbool in
      t_hoare_call env pre post g
    | FhoareS _, Some _ ->
      cannot_apply "call" "side can only be given for prhl judgements"
    | FequivS es, None ->
      let (_,fl,_),(_,fr,_),_,_ = s_last_calls "call" es.es_sl es.es_sr in
      let env' = tyenv_of_hyps env hyps in
      let penv, qenv = EcEnv.Fun.equivF fl fr env' in
      let pre  = process_form penv hyps pre tbool in
      let post = process_form qenv hyps post tbool in
      t_equiv_call env pre post g
    | FequivS es, Some side ->
      let fstmt = match side with true -> es.es_sl | false -> es.es_sr in
      let (_,f,_),_ = s_last_call "call" fstmt in
      let penv, qenv = EcEnv.Fun.hoareF f env in
      let pre  = process_form penv hyps pre tbool in
      let post = process_form qenv hyps post tbool in
      t_equiv_call1 env side pre post g
    | _ -> cannot_apply "call" "the conclusion is not a hoare or a equiv"

  let process_cond env side g =
    let concl = get_concl g in
    if is_equivS concl then
      t_equiv_cond env side g
    else if is_hoareS concl || is_bdHoareS concl then
      match side with
        | Some _ -> cannot_apply "cond" "Unexpected side in non relational goal"
        | None ->
          if is_hoareS concl then t_hoare_cond env g else t_bdHoare_cond env g
    else cannot_apply "cond" "the conclusion is not a hoare or a equiv goal"

  let rec process_swap1 env info g =
    let side,pos = info.pl_desc in
    match side with
    | None ->
      t_seq (process_swap1 env {info with pl_desc = (Some true, pos)})
        (process_swap1 env {info with pl_desc = (Some false, pos)}) g
    | Some side ->
      let tac =
        match pos with
        | SKbase(p1,p2,p3) -> t_equiv_swap env side p1 p2 p3
        | SKmove p ->
          if 0 < p then t_equiv_swap env side 1 2 (p+1)
          else if p < 0 then
            let concl = get_concl g in
            let es = set_loc info.pl_loc destr_equivS concl in
            let s = if side then es.es_sl else es.es_sr in
            let len = List.length s.s_node in
            t_equiv_swap env side (len+p) len len
          else (* p = 0 *) t_id None
        | SKmovei(i,p) ->
          if 0 < p then t_equiv_swap env side i (i+1) (i+p)
          else if p < 0 then t_equiv_swap env side (i+p) i i
          else (* p = 0 *) t_id None
        | SKmoveinter(i1,i2,p) ->
          if 0 < p then t_equiv_swap env side i1 (i2+1) (i2+p)
          else if p < 0 then t_equiv_swap env side (i1+p) i1 i2
          else (* p = 0 *) t_id None
      in
      set_loc info.pl_loc tac g

  let process_swap env info =
    t_lseq (List.map (process_swap1 env) info)

  (* TODO move this *)
  let pat_all fs s =
    let rec aux_i i = 
      match i.i_node with
      | Scall(_,f,_) -> 
        if EcPath.Sx.mem f fs then Some IPpat else None
      | Sif(_,s1,s2) -> 
        let sp1 = aux_s 0 s1.s_node in
        let sp2 = aux_s 0 s2.s_node in
        if sp1 = [] && sp2 = [] then None 
        else Some (IPif(sp1,sp2))
      | Swhile(_,s) ->
        let sp = aux_s 0 s.s_node in
        if sp = [] then None else Some (IPwhile(sp)) 
      | _ -> None
    and aux_s n s = 
      match s with
      | [] -> []
      | i::s ->
        match aux_i i with
        | Some ip -> (n,ip) :: aux_s 0 s 
        | None -> aux_s (n+1) s in
    aux_s 0 s.s_node
    
  let rec process_inline_all env side fs g =
    let concl = get_concl g in
    match concl.f_node, side with
    | FequivS _, None ->
        t_seq
          (process_inline_all env (Some true ) fs)
          (process_inline_all env (Some false) fs) g
    | FequivS es, Some b ->
        let sp = pat_all fs (if b then es.es_sl else es.es_sr) in
          if   sp = []
          then t_id None g
          else t_seq
                 (t_inline_equiv env b sp)
                 (process_inline_all env side fs) g
    | FhoareS hs, None ->
        let sp = pat_all fs hs.hs_s in
          if   sp = []
          then t_id None g
          else t_seq
                 (t_inline_hoare env sp)
                 (process_inline_all env side fs) g

    | _, _ -> assert false (* FIXME error message *)
    
  let pat_of_occs cond occs s =
    let occs = ref occs in
    let rec aux_i occ i = 
      match i.i_node with
      | Scall (_,f,_) -> 
        if cond f then 
          let occ = 1 + occ in
          if Sint.mem occ !occs then begin
            occs := Sint.remove occ !occs; 
            occ, Some IPpat
          end else occ, None
        else occ, None
      | Sif(_,s1,s2) ->
        let occ, sp1 = aux_s occ 0 s1.s_node in
        let occ, sp2 = aux_s occ 0 s2.s_node in
        let ip = if sp1 = [] && sp2 = [] then None else Some(IPif(sp1,sp2)) in
        occ, ip
      | Swhile(_,s) ->
        let occ, sp = aux_s occ 0 s.s_node in
        let ip = if sp = [] then None else Some(IPwhile sp) in
        occ, ip
      | _ -> occ, None 
    and aux_s occ n s =
      match s with
      | [] -> occ, []
      | i::s ->
        match aux_i occ i with
        | occ, Some ip -> 
          let occ, sp = aux_s occ 0 s in
          occ, (n,ip) :: sp
        | occ, None -> aux_s occ (n+1) s in
    let _, sp = aux_s 0 0 s.s_node in
    assert (Sint.is_empty !occs); (* FIXME error message *)
    sp

  let process_inline_occs env side fs occs g =
    let cond = 
      if EcPath.Sx.is_empty fs then fun _ -> true
      else fun f -> EcPath.Sx.mem f fs in
    let occs = Sint.of_list occs in
    let concl = get_concl g in
    match concl.f_node, side with
    | FequivS es, Some b ->
      let sp =  pat_of_occs cond occs (if b then es.es_sl else es.es_sr) in
      t_inline_equiv env b sp g 
    | FhoareS hs, None ->
      let sp =  pat_of_occs cond occs hs.hs_s in
      t_inline_hoare env sp g 
    | _, _ -> assert false (* FIXME error message *)
    

  let process_inline env infos g =
    match infos with
    | `ByName (side, (fs, occs)) -> begin
        let hyps = get_hyps g in
        let env' = tyenv_of_hyps env hyps in
        let fs = 
          List.fold_left (fun fs f ->
            let f = EcTyping.trans_gamepath env' f in
            EcPath.Sx.add f fs) EcPath.Sx.empty fs 
        in
        match occs with
        | None -> process_inline_all env side fs g
        | Some occs -> process_inline_occs env side fs occs g
      end

    | `ByPattern _ -> failwith "not-implemented"

  let process_alias env (side, cpos, id) g =
    t_alias env side cpos id g

  let process_rnd side env tac_info g =
    let concl = get_concl g in
    match side, tac_info with 
      | None, (None, None) when is_hoareS concl -> t_hoare_rnd env g
      | None, (opt_bd, opt_event) when is_bdHoareS concl ->
        let opt_bd = omap opt_bd (process_phl_form treal env g)  in
        let event ty = omap opt_event (process_phl_form (tfun ty tbool) env g) in
        t_bd_hoare_rnd env (opt_bd,event) g
      | _ when is_equivS concl ->
        let process_form f ty1 ty2 = process_prhl_form (tfun ty1 ty2) env g f in
        let bij_info = match tac_info with
          | None,None -> None, None
          | Some f, None | None, Some f -> Some (process_form f), None
          | Some f, Some finv -> Some (process_form f), Some (process_form finv)
        in
        t_equiv_rnd side env bij_info g
      | _ -> cannot_apply "rnd" "unexpected instruction or wrong arguments"

  let process_equiv_deno env info (_,n as g) = 
    let process_cut env g (pre,post) = 
      let hyps,concl = get_goal g in
      let _op, f1, f2 =
        match concl.f_node with
        | Fapp({f_node = Fop(op,_)}, [f1;f2]) when is_pr f1 && is_pr f2 -> 
          op, f1, f2
        | _ -> cannot_apply "equiv_deno" "" in (* FIXME error message *) 
      let _,fl,_,_ = destr_pr f1 in
      let _,fr,_,_ = destr_pr f2 in
      let penv, qenv = EcEnv.Fun.equivF fl fr env in
      let pre  = omap_dfl pre  f_true (fun p -> process_form penv hyps p tbool) in
      let post = omap_dfl post f_true (fun p -> process_form qenv hyps p tbool) in
      f_equivF pre fl fr post in
    let (juc,an), gs = process_mkn_apply process_cut env info g in
    let pre,post =
      let (_,f) = get_node (juc,an) in
      let ef = destr_equivF f in
      ef.ef_pr, ef.ef_po in
    t_on_first (t_equiv_deno env pre post (juc,n)) (t_use env an gs)

  let process_conseq env info (_, n as g) =
    let t_pre = ref (t_id None) and t_post = ref (t_id None) in
    let tac1 g =
      let hyps = get_hyps g in
      let m, h = match LDecl.fresh_ids hyps ["&m";"H"] with
        | [m;h] -> m,h
        | _ -> assert false in
      t_seq (t_intros_i env [m;h]) (t_hyp env h) g in
    let tac2 g =
      let hyps = get_hyps g in
      let m1,m2, h = match LDecl.fresh_ids hyps ["&m";"&m";"H"] with
        | [m1;m2;h] -> m1,m2,h
        | _ -> assert false in
      t_seq (t_intros_i env [m1;m2;h]) (t_hyp env h) g in
    let process_cut env g (pre,post) =
      let hyps,concl = get_goal g in        
      let tac, penv, qenv, gpre, gpost, fmake = 
        match concl.f_node with
        | FhoareF hf ->
          let penv, qenv = EcEnv.Fun.hoareF hf.hf_f env in
          tac1, penv, qenv, hf.hf_pr, hf.hf_po, 
          (fun pre post -> f_hoareF pre hf.hf_f post)
        | FhoareS hs ->
          let env = EcEnv.Memory.push_active hs.hs_m env in
          tac1, env, env, hs.hs_pr, hs.hs_po,
          (fun pre post -> f_hoareS_r { hs with hs_pr = pre; hs_po = post })
        | FequivF ef ->
          let penv, qenv = EcEnv.Fun.equivF ef.ef_fl ef.ef_fr env in
          tac2, penv, qenv, ef.ef_pr, ef.ef_po,
          (fun pre post -> f_equivF pre ef.ef_fl ef.ef_fr post)
        | FequivS es -> 
          let env = EcEnv.Memory.push_all [es.es_ml; es.es_mr] env in
          tac2, env, env, es.es_pr, es.es_po,
          (fun pre post -> f_equivS_r { es with es_pr = pre; es_po = post }) 
        | _ -> assert false (* FIXME error message *)
      in
      let pre = match pre with
        | None -> t_pre := tac; gpre 
        | Some pre ->  process_form penv hyps pre tbool in
      let post = match post with
        | None -> t_post := tac; gpost 
        | Some post ->  process_form qenv hyps post tbool in
      fmake pre post in
    let (juc,an), gs = process_mkn_apply process_cut env info g in
    let t_conseq = 
      let (_,f) = get_node (juc,an) in
      match f.f_node with
      | FhoareF hf -> t_hoareF_conseq env hf.hf_pr hf.hf_po
      | FhoareS hs -> t_hoareS_conseq env hs.hs_pr hs.hs_po
      | FequivF ef -> t_equivF_conseq env ef.ef_pr ef.ef_po
      | FequivS es -> t_equivS_conseq env es.es_pr es.es_po 
      | _ -> assert false (* FIXME error message *) in
    t_seq_subgoal t_conseq
      [!t_pre; !t_post; t_use env an gs] (juc,n)
    
  let process_fun_abs env inv g =
    let env' = EcEnv.Fun.inv_memenv env in
    let inv = process_formula env' g inv in
    t_equivF_abs env inv g
    
  let process_fun_upto env (bad, p, o) g =
    let env' = EcEnv.Fun.inv_memenv env in 
    let p = process_formula env' g p in
    let q = 
      match o with
      | None -> EcFol.f_true
      | Some q -> process_formula env' g q in
    let bad = 
      let env =  EcEnv.Memory.push_active (EcFol.mhr,None) env in
      process_formula env g bad in
    t_equivF_abs_upto env bad p q g
      
  let process_phl loc env ptac g =
    let t =
      match ptac with
      | Pfun_def -> EcPhl.t_fun_def env
      | Pfun_abs f -> process_fun_abs env f
      | Pfun_upto info -> process_fun_upto env info 
      | Pskip    -> EcPhl.t_skip
      | Papp (dir,k,phi,f) -> process_app env dir k phi f
      | Pwp  k   -> t_wp env k
      | Prcond (side,b,i) -> t_rcond side b i
      | Pcond side   -> process_cond env side
      | Pwhile phi -> process_while env phi
      | Pcall(side, (pre, post)) -> process_call env side pre post
      | Pswap info -> process_swap env info
      | Pinline info -> process_inline env info
      | Palias info -> process_alias env info
      | Prnd (side,info) -> process_rnd side env info
      | Pconseq info -> process_conseq env info
      | Pequivdeno info -> process_equiv_deno env info
    in
    set_loc loc t g

  let process_debug env =
    let l = fun x -> EcLocation.mk_loc EcLocation._dummy x in
    let (p, _) = EcTyping.trans_msymbol env (l [(l "M", Some [l [(l "K", None)]])]) in
      ignore (EcEnv.Mod.by_mpath p env)

  let rec process_logic_tacs scope env (tacs:ptactics) (gs:goals) : goals =
    match tacs with
    | [] -> gs
    | {pl_desc = Psubgoal tacs1; pl_loc = loc } :: tacs2 ->
        let gs =
          set_loc loc
            (t_subgoal (List.map (process_logic_tac scope env) tacs1)) gs in
        process_logic_tacs scope env tacs2 gs
    | tac1 :: tacs2 ->
        let gs = t_on_goals (process_logic_tac scope env tac1) gs in
        process_logic_tacs scope env tacs2 gs

  and process_logic_tac scope env (tac:ptactic) (g:goal) : goals =
    let loc = tac.pl_loc in
    let tac =
      match unloc tac with
      | Pidtac msg     -> t_id msg
      | Prepeat t      -> t_repeat (process_logic_tac scope env t)
      | Pdo (None,t)   -> 
        let tac = (process_logic_tac scope env t) in
        t_seq tac (t_repeat tac)
      | Pdo (Some i, t) -> t_do i (process_logic_tac scope env t)
      | Ptry t         -> t_try (process_logic_tac scope env t)
      | Passumption pq -> process_assumption loc env pq
      | Ptrivial pi    -> process_trivial scope pi env
      | Pintro pi      -> process_intros env pi
      | Psplit         -> t_split env
      | Pexists fs     -> process_exists env fs
      | Pleft          -> t_left env
      | Pright         -> t_right env
      | Pelim pe       -> process_elim  loc env pe
      | Papply pe      -> process_apply loc env pe
      | Pcut (name,phi)-> process_cut name env phi
      | Pgeneralize l  -> process_generalize env l
      | Pclear l       -> process_clear l
      | Prewrite ri    -> process_rewrite loc env ri
      | Psubst   ri    -> process_subst loc env ri
      | Psimplify ri   -> process_simplify env ri
      | Pchange pf     -> process_change env pf
      | PelimT i       -> process_elimT loc env i
      | Pcase  i       -> process_case  loc env i
      | Pseq tacs      ->
          fun (juc,n) -> process_logic_tacs scope env tacs (juc,[n])
      | Psubgoal _     -> assert false

      | Padmit         -> t_admit
      | Pdebug         -> process_debug env; t_id None

      | PPhl tac       -> process_phl loc env tac
    in
    set_loc loc tac g

  let process_logic scope env juc loc tacs =
    let (juc,n) =
      try get_first_goal juc
      with _ -> error loc NoCurrentGoal in
    EcBaseLogic.upd_done (fst (process_logic_tacs scope env tacs (juc,[n])))

  let process scope tac =
    if Check_mode.check !(scope.sc_options) then
      let loc = match tac with | [] -> assert false | t::_ -> t.pl_loc in
      match scope.sc_pr_uc with
      | [] -> error loc NoCurrentGoal
      | puc :: pucs ->
          let juc = process_logic scope scope.sc_env puc.puc_jdg loc tac in
          { scope with
            sc_pr_uc = { puc with puc_jdg = juc } :: pucs }
    else scope
end

(* -------------------------------------------------------------------- *)
module Ax = struct
  open EcParsetree
  open EcTypes
  open EcDecl

  module TT = EcTyping

  let bind (scope : scope) ((x, ax) : _ * axiom) =
   let res =
    { scope with
        sc_env  = EcEnv.Ax.bind x ax scope.sc_env; }
      in
   res

  let start_lemma scope name tparams concl =
    let hyps = { EcBaseLogic.h_tvar = tparams;
                 EcBaseLogic.h_local = []; } in
    let puc = {
      puc_name = name ;
      puc_jdg = EcBaseLogic.open_juc (hyps, concl) } in
    { scope with
      sc_pr_uc = puc :: scope.sc_pr_uc }

  let save scope loc =
    if Check_mode.check !(scope.sc_options) then
      match scope.sc_pr_uc with
      | [] -> Tactic.error loc Tactic.NoCurrentGoal
      | { puc_name = name; puc_jdg = juc } :: pucs ->
          let pr = EcBaseLogic.close_juc juc in
          let hyps,concl = (EcBaseLogic.get_goal (juc,0)).EcBaseLogic.pj_decl in
          let tparams = hyps.EcBaseLogic.h_tvar in
          assert (hyps.EcBaseLogic.h_local = []);
          let axd = { ax_tparams = tparams;
                      ax_spec = Some concl;
                      ax_kind = Lemma (Some pr) } in
          let scope = { scope with sc_pr_uc = pucs } in
          Some name, bind scope (name, axd)
    else None, scope

  let add (scope : scope) (ax : paxiom) =
    let ue = EcUnify.UniEnv.create None in
    let concl = TT.transformula scope.sc_env ue ax.pa_formula in
    let concl =
      EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) concl in
    let tparams = EcUnify.UniEnv.tparams ue in
    let check = Check_mode.check !(scope.sc_options) in
    let loc = ax.pa_name.pl_loc in

    match ax.pa_kind with
    | PILemma when check ->
        None, start_lemma scope (unloc ax.pa_name) tparams concl
    | PLemma when check ->
        let scope = start_lemma scope (unloc ax.pa_name) tparams concl in
        let scope =
          Tactic.process scope
            [{ pl_loc = loc; pl_desc = Ptrivial empty_pprover }] in
        let name, scope = save scope loc in
        name, scope
    | _ ->
        let axd = { ax_tparams = tparams;
                    ax_spec = Some concl;
                    ax_kind = Axiom } in
        Some (unloc ax.pa_name), bind scope (unloc ax.pa_name, axd)
end
