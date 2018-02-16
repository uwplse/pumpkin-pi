
* Eventually, when supporting many changes, will want to chain these *)

* When we do that, we'll also want better detection. For now, we just assume only one at a time. We also assume same order for now, of parameters and constructors and so on.

* Better data representations for return types and so on.

* IR should mimic ornaments for generality.

* What happens when an indexed type isn't a measure, so you can't extract the index from the old type? When does that happen?

* Figuring out when we need more premises, too, as in bal_bintrees.

* Figuring out when we have extra premises, too (separate concerns, but makes indexing function ill-defined right now because we assume every nat is an index regardless of constructor arity; see vector3).
