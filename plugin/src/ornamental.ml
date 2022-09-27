let __coq_plugin_name = "ornamental"
let _ = Mltop.add_known_module __coq_plugin_name

# 3 "src/ornamental.mlg"
 
open Stdarg
open Frontend


let () = Vernacextend.vernac_extend ~command:"FindOrnament" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Find", 
                                     Vernacextend.TyTerminal ("ornament", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("as", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                    Vernacextend.TyNil)))))), 
         (let coqpp_body d_old d_new n
         () = Vernacextend.VtDefault (fun () -> 
# 11 "src/ornamental.mlg"
    find_ornament (Some n) d_old d_new None 
              ) in fun d_old
         d_new n ~atts -> coqpp_body d_old d_new n
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Find", 
                                    Vernacextend.TyTerminal ("ornament", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("as", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyTerminal ("{", 
                                                                   Vernacextend.TyTerminal ("mapping", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_int), 
                                                                   Vernacextend.TyTerminal ("}", 
                                                                   Vernacextend.TyNil)))))))))), 
         (let coqpp_body d_old d_new n i
         () = Vernacextend.VtDefault (fun () -> 
# 13 "src/ornamental.mlg"
    find_ornament (Some n) d_old d_new (Some i) 
              ) in fun d_old
         d_new n i ~atts -> coqpp_body d_old d_new n i
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Find", 
                                    Vernacextend.TyTerminal ("ornament", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNil)))), (let coqpp_body d_old
                                                            d_new
                                                            () = Vernacextend.VtDefault (fun () -> 
                                                                 
# 15 "src/ornamental.mlg"
    find_ornament None d_old d_new None 
                                                                 ) in fun d_old
                                                            d_new ~atts
                                                            -> coqpp_body d_old
                                                            d_new
                                                            (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Find", 
                                    Vernacextend.TyTerminal ("ornament", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("{", Vernacextend.TyTerminal ("mapping", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_int), 
                                                                  Vernacextend.TyTerminal ("}", 
                                                                  Vernacextend.TyNil)))))))), 
         (let coqpp_body d_old d_new i
         () = Vernacextend.VtDefault (fun () -> 
# 17 "src/ornamental.mlg"
    find_ornament None d_old d_new (Some i) 
              ) in fun d_old
         d_new i ~atts -> coqpp_body d_old d_new i
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"SaveOrnament" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Save", 
                                     Vernacextend.TyTerminal ("ornament", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("{", Vernacextend.TyTerminal ("promote", 
                                                                   Vernacextend.TyTerminal ("=", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal (";", 
                                                                   Vernacextend.TyTerminal ("forget", 
                                                                   Vernacextend.TyTerminal ("=", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("}", 
                                                                   Vernacextend.TyNil))))))))))))), 
         (let coqpp_body d_old d_new d_orn d_orn_inv
         () = Vernacextend.VtDefault (fun () -> 
# 23 "src/ornamental.mlg"
    save_ornament d_old d_new (Some d_orn) (Some d_orn_inv) false 
              ) in fun d_old
         d_new d_orn d_orn_inv ~atts -> coqpp_body d_old d_new d_orn
         d_orn_inv (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Save", 
                                    Vernacextend.TyTerminal ("ornament", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("{", Vernacextend.TyTerminal ("promote", 
                                                                  Vernacextend.TyTerminal ("=", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                  Vernacextend.TyTerminal ("}", 
                                                                  Vernacextend.TyNil))))))))), 
         (let coqpp_body d_old d_new d_orn
         () = Vernacextend.VtDefault (fun () -> 
# 25 "src/ornamental.mlg"
    save_ornament d_old d_new (Some d_orn) None false 
              ) in fun d_old
         d_new d_orn ~atts -> coqpp_body d_old d_new d_orn
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Save", 
                                    Vernacextend.TyTerminal ("ornament", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("{", Vernacextend.TyTerminal ("forget", 
                                                                  Vernacextend.TyTerminal ("=", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                  Vernacextend.TyTerminal ("}", 
                                                                  Vernacextend.TyNil))))))))), 
         (let coqpp_body d_old d_new d_orn_inv
         () = Vernacextend.VtDefault (fun () -> 
# 27 "src/ornamental.mlg"
    save_ornament d_old d_new None (Some d_orn_inv) false 
              ) in fun d_old
         d_new d_orn_inv ~atts -> coqpp_body d_old d_new d_orn_inv
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Save", 
                                    Vernacextend.TyTerminal ("equivalence", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("{", Vernacextend.TyTerminal ("promote", 
                                                                  Vernacextend.TyTerminal ("=", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                  Vernacextend.TyTerminal (";", 
                                                                  Vernacextend.TyTerminal ("forget", 
                                                                  Vernacextend.TyTerminal ("=", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                  Vernacextend.TyTerminal ("}", 
                                                                  Vernacextend.TyNil))))))))))))), 
         (let coqpp_body d_old d_new d_orn d_orn_inv
         () = Vernacextend.VtDefault (fun () -> 
# 29 "src/ornamental.mlg"
    save_ornament d_old d_new (Some d_orn) (Some d_orn_inv) true 
              ) in fun d_old
         d_new d_orn d_orn_inv ~atts -> coqpp_body d_old d_new d_orn
         d_orn_inv (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"LiftOrnament" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Lift", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                    Vernacextend.TyNil))))))), 
         (let coqpp_body d_orn d_orn_inv d_old n
         () = Vernacextend.VtDefault (fun () -> 
# 35 "src/ornamental.mlg"
    lift_by_ornament n d_orn d_orn_inv d_old false 
              ) in fun d_orn
         d_orn_inv d_old n ~atts -> coqpp_body d_orn d_orn_inv d_old n
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Lift", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyTerminal ("{", 
                                                                   Vernacextend.TyTerminal ("opaque", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                   Vernacextend.TyTerminal ("}", 
                                                                   Vernacextend.TyNil))))))))))), 
         (let coqpp_body d_orn d_orn_inv d_old n opaques
         () = Vernacextend.VtDefault (fun () -> 
# 37 "src/ornamental.mlg"
    lift_by_ornament ~opaques:opaques n d_orn d_orn_inv d_old false 
              ) in fun d_orn
         d_orn_inv d_old n opaques ~atts -> coqpp_body d_orn d_orn_inv d_old
         n opaques (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Lift", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyTerminal ("..", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyNil)))))))), 
         (let coqpp_body d_orn d_orn_inv d_old n
         () = Vernacextend.VtDefault (fun () -> 
# 39 "src/ornamental.mlg"
    lift_by_ornament ~suffix:true n d_orn d_orn_inv d_old false 
              ) in fun d_orn
         d_orn_inv d_old n ~atts -> coqpp_body d_orn d_orn_inv d_old n
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Lift", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyTerminal ("..", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyTerminal ("{", 
                                                                   Vernacextend.TyTerminal ("opaque", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                   Vernacextend.TyTerminal ("}", 
                                                                   Vernacextend.TyNil)))))))))))), 
         (let coqpp_body d_orn d_orn_inv d_old n opaques
         () = Vernacextend.VtDefault (fun () -> 
# 41 "src/ornamental.mlg"
    lift_by_ornament ~opaques:opaques ~suffix:true n d_orn d_orn_inv d_old false 
              ) in fun d_orn
         d_orn_inv d_old n opaques ~atts -> coqpp_body d_orn d_orn_inv d_old
         n opaques (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Lift", 
                                    Vernacextend.TyTerminal ("Module", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyNil)))))))), 
         (let coqpp_body d_orn d_orn_inv mod_ref id
         () = Vernacextend.VtDefault (fun () -> 
# 43 "src/ornamental.mlg"
    lift_module_by_ornament id d_orn d_orn_inv mod_ref 
              ) in fun d_orn
         d_orn_inv mod_ref id ~atts -> coqpp_body d_orn d_orn_inv mod_ref id
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Lift", 
                                    Vernacextend.TyTerminal ("Module", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyTerminal ("{", 
                                                                   Vernacextend.TyTerminal ("opaque", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                   Vernacextend.TyTerminal ("}", 
                                                                   Vernacextend.TyNil)))))))))))), 
         (let coqpp_body d_orn d_orn_inv mod_ref id opaques
         () = Vernacextend.VtDefault (fun () -> 
# 45 "src/ornamental.mlg"
    lift_module_by_ornament ~opaques:opaques id d_orn d_orn_inv mod_ref 
              ) in fun d_orn
         d_orn_inv mod_ref id opaques ~atts -> coqpp_body d_orn d_orn_inv
         mod_ref id opaques (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ConfigureLift" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Configure", 
                                     Vernacextend.TyTerminal ("Lift", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("{", Vernacextend.TyTerminal ("opaque", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                   Vernacextend.TyTerminal ("}", 
                                                                   Vernacextend.TyNil)))))))), 
         (let coqpp_body d_orn d_orn_inv opaques
         () = Vernacextend.VtDefault (fun () -> 
# 51 "src/ornamental.mlg"
    add_lifting_opaques d_orn d_orn_inv opaques 
              ) in fun d_orn
         d_orn_inv opaques ~atts -> coqpp_body d_orn d_orn_inv opaques
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Configure", 
                                    Vernacextend.TyTerminal ("Lift", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("{", Vernacextend.TyTerminal ("~", 
                                                                  Vernacextend.TyTerminal ("opaque", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUlist1 (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                  Vernacextend.TyTerminal ("}", 
                                                                  Vernacextend.TyNil))))))))), 
         (let coqpp_body d_orn d_orn_inv opaques
         () = Vernacextend.VtDefault (fun () -> 
# 53 "src/ornamental.mlg"
    remove_lifting_opaques d_orn d_orn_inv opaques 
              ) in fun d_orn
         d_orn_inv opaques ~atts -> coqpp_body d_orn d_orn_inv opaques
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Configure", 
                                    Vernacextend.TyTerminal ("Lift", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("{", Vernacextend.TyTerminal ("constrs_a", 
                                                                  Vernacextend.TyTerminal ("=", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUlist0 (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                  Vernacextend.TyTerminal (";", 
                                                                  Vernacextend.TyTerminal ("constrs_b", 
                                                                  Vernacextend.TyTerminal ("=", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUlist0 (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                  Vernacextend.TyTerminal (";", 
                                                                  Vernacextend.TyTerminal ("elim_a", 
                                                                  Vernacextend.TyTerminal ("=", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                  Vernacextend.TyTerminal (";", 
                                                                  Vernacextend.TyTerminal ("elim_b", 
                                                                  Vernacextend.TyTerminal ("=", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                  Vernacextend.TyTerminal (";", 
                                                                  Vernacextend.TyTerminal ("eta_a", 
                                                                  Vernacextend.TyTerminal ("=", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                  Vernacextend.TyTerminal (";", 
                                                                  Vernacextend.TyTerminal ("eta_b", 
                                                                  Vernacextend.TyTerminal ("=", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                  Vernacextend.TyTerminal (";", 
                                                                  Vernacextend.TyTerminal ("iota_a", 
                                                                  Vernacextend.TyTerminal ("=", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUlist0 (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                  Vernacextend.TyTerminal (";", 
                                                                  Vernacextend.TyTerminal ("iota_b", 
                                                                  Vernacextend.TyTerminal ("=", 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUlist0 (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                  Vernacextend.TyTerminal ("}", 
                                                                  Vernacextend.TyNil))))))))))))))))))))))))))))))))))))), 
         (let coqpp_body d_orn d_orn_inv constrs_a constrs_b elim_a elim_b
         eta_a eta_b iota_a iota_b
         () = Vernacextend.VtDefault (fun () -> 
# 55 "src/ornamental.mlg"
    configure_manual d_orn d_orn_inv (constrs_a, constrs_b) (elim_a, elim_b) (eta_a, eta_b) (iota_a, iota_b) 
              ) in fun d_orn
         d_orn_inv constrs_a constrs_b elim_a elim_b eta_a eta_b iota_a
         iota_b ~atts -> coqpp_body d_orn d_orn_inv constrs_a constrs_b
         elim_a elim_b eta_a eta_b iota_a iota_b
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"RepairProof" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Repair", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                    Vernacextend.TyNil))))))), 
         (let coqpp_body d_orn d_orn_inv d_old n
         () = Vernacextend.VtDefault (fun () -> 
# 61 "src/ornamental.mlg"
    repair n d_orn d_orn_inv d_old false 
              ) in fun d_orn
         d_orn_inv d_old n ~atts -> coqpp_body d_orn d_orn_inv d_old n
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Repair", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyTerminal ("{", 
                                                                   Vernacextend.TyTerminal ("opaque", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                   Vernacextend.TyTerminal ("}", 
                                                                   Vernacextend.TyNil))))))))))), 
         (let coqpp_body d_orn d_orn_inv d_old n opaques
         () = Vernacextend.VtDefault (fun () -> 
# 63 "src/ornamental.mlg"
    repair ~opaques:opaques n d_orn d_orn_inv d_old false 
              ) in fun d_orn
         d_orn_inv d_old n opaques ~atts -> coqpp_body d_orn d_orn_inv d_old
         n opaques (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Repair", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyTerminal ("..", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyNil)))))))), 
         (let coqpp_body d_orn d_orn_inv d_old n
         () = Vernacextend.VtDefault (fun () -> 
# 65 "src/ornamental.mlg"
    repair ~suffix:true n d_orn d_orn_inv d_old false 
              ) in fun d_orn
         d_orn_inv d_old n ~atts -> coqpp_body d_orn d_orn_inv d_old n
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Repair", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyTerminal ("..", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyTerminal ("{", 
                                                                   Vernacextend.TyTerminal ("opaque", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                   Vernacextend.TyTerminal ("}", 
                                                                   Vernacextend.TyNil)))))))))))), 
         (let coqpp_body d_orn d_orn_inv d_old n opaques
         () = Vernacextend.VtDefault (fun () -> 
# 67 "src/ornamental.mlg"
    repair ~opaques:opaques ~suffix:true n d_orn d_orn_inv d_old false 
              ) in fun d_orn
         d_orn_inv d_old n opaques ~atts -> coqpp_body d_orn d_orn_inv d_old
         n opaques (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Repair", 
                                    Vernacextend.TyTerminal ("Module", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyNil)))))))), 
         (let coqpp_body d_orn d_orn_inv mod_ref id
         () = Vernacextend.VtDefault (fun () -> 
# 69 "src/ornamental.mlg"
    repair_module id d_orn d_orn_inv mod_ref 
              ) in fun d_orn
         d_orn_inv mod_ref id ~atts -> coqpp_body d_orn d_orn_inv mod_ref id
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Repair", 
                                    Vernacextend.TyTerminal ("Module", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyTerminal ("{", 
                                                                   Vernacextend.TyTerminal ("opaque", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                   Vernacextend.TyTerminal ("}", 
                                                                   Vernacextend.TyNil)))))))))))), 
         (let coqpp_body d_orn d_orn_inv mod_ref id opaques
         () = Vernacextend.VtDefault (fun () -> 
# 71 "src/ornamental.mlg"
    repair_module ~opaques:opaques id d_orn d_orn_inv mod_ref 
              ) in fun d_orn
         d_orn_inv mod_ref id opaques ~atts -> coqpp_body d_orn d_orn_inv
         mod_ref id opaques (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Repair", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyTerminal ("{", 
                                                                   Vernacextend.TyTerminal ("hint", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_string)), 
                                                                   Vernacextend.TyTerminal ("}", 
                                                                   Vernacextend.TyNil))))))))))), 
         (let coqpp_body d_orn d_orn_inv d_old n hints
         () = Vernacextend.VtDefault (fun () -> 
# 73 "src/ornamental.mlg"
    repair ~hints:hints n d_orn d_orn_inv d_old false 
              ) in fun d_orn
         d_orn_inv d_old n hints ~atts -> coqpp_body d_orn d_orn_inv d_old n
         hints (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Repair", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyTerminal ("{", 
                                                                   Vernacextend.TyTerminal ("opaque", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                   Vernacextend.TyTerminal (";", 
                                                                   Vernacextend.TyTerminal ("hint", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_string)), 
                                                                   Vernacextend.TyTerminal ("}", 
                                                                   Vernacextend.TyNil)))))))))))))), 
         (let coqpp_body d_orn d_orn_inv d_old n opaques hints
         () = Vernacextend.VtDefault (fun () -> 
# 75 "src/ornamental.mlg"
    repair ~opaques:opaques ~hints:hints n d_orn d_orn_inv d_old false 
              ) in fun d_orn
         d_orn_inv d_old n opaques hints ~atts -> coqpp_body d_orn d_orn_inv
         d_old n opaques hints (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Repair", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyTerminal ("..", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyTerminal ("{", 
                                                                   Vernacextend.TyTerminal ("hint", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_string)), 
                                                                   Vernacextend.TyTerminal ("}", 
                                                                   Vernacextend.TyNil)))))))))))), 
         (let coqpp_body d_orn d_orn_inv d_old n hints
         () = Vernacextend.VtDefault (fun () -> 
# 77 "src/ornamental.mlg"
    repair ~suffix:true ~hints:hints n d_orn d_orn_inv d_old false 
              ) in fun d_orn
         d_orn_inv d_old n hints ~atts -> coqpp_body d_orn d_orn_inv d_old n
         hints (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Repair", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyTerminal ("..", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyTerminal ("{", 
                                                                   Vernacextend.TyTerminal ("opaque", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                   Vernacextend.TyTerminal (";", 
                                                                   Vernacextend.TyTerminal ("hint", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_string)), 
                                                                   Vernacextend.TyTerminal ("}", 
                                                                   Vernacextend.TyNil))))))))))))))), 
         (let coqpp_body d_orn d_orn_inv d_old n opaques hints
         () = Vernacextend.VtDefault (fun () -> 
# 79 "src/ornamental.mlg"
    repair ~opaques:opaques ~suffix:true ~hints:hints n d_orn d_orn_inv d_old false 
              ) in fun d_orn
         d_orn_inv d_old n opaques hints ~atts -> coqpp_body d_orn d_orn_inv
         d_old n opaques hints (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Repair", 
                                    Vernacextend.TyTerminal ("Module", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyTerminal ("{", 
                                                                   Vernacextend.TyTerminal ("hint", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_string)), 
                                                                   Vernacextend.TyTerminal ("}", 
                                                                   Vernacextend.TyNil)))))))))))), 
         (let coqpp_body d_orn d_orn_inv mod_ref id hints
         () = Vernacextend.VtDefault (fun () -> 
# 81 "src/ornamental.mlg"
    repair_module ~hints:hints id d_orn d_orn_inv mod_ref 
              ) in fun d_orn
         d_orn_inv mod_ref id hints ~atts -> coqpp_body d_orn d_orn_inv
         mod_ref id hints (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Repair", 
                                    Vernacextend.TyTerminal ("Module", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyTerminal ("{", 
                                                                   Vernacextend.TyTerminal ("opaque", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                                   Vernacextend.TyTerminal (";", 
                                                                   Vernacextend.TyTerminal ("hint", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_string)), 
                                                                   Vernacextend.TyTerminal ("}", 
                                                                   Vernacextend.TyNil))))))))))))))), 
         (let coqpp_body d_orn d_orn_inv mod_ref id opaques hints
         () = Vernacextend.VtDefault (fun () -> 
# 83 "src/ornamental.mlg"
    repair_module ~opaques:opaques ~hints:hints id d_orn d_orn_inv mod_ref 
              ) in fun d_orn
         d_orn_inv mod_ref id opaques hints ~atts -> coqpp_body d_orn
         d_orn_inv mod_ref id opaques hints
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"UnpackSigma" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Unpack", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                     Vernacextend.TyTerminal ("as", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body const_ref id
         () = Vernacextend.VtDefault (fun () -> 
# 89 "src/ornamental.mlg"
    do_unpack_constant id const_ref 
              ) in fun const_ref
         id ~atts -> coqpp_body const_ref id
         (Attributes.unsupported_attributes atts)), None))]

