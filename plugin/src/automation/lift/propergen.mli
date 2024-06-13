val generate_proper_proof :
  Lifting.lifting ->
  Environ.env ->
  Evd.evar_map ->
  Names.Id.t ->
  Names.GlobRef.t ->
  Evd.evar_map * (Names.GlobRef.t option)
