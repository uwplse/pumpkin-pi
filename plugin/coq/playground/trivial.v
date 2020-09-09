(*
 * Equivalences do capture the set of all changes that one can make to a type,
 * including semantic changes, just not in a way that is practically useful!
 * So the challenge is determining when useful, nontrivial equivalences exist
 * that separate out new information into the left projection of the sigma type,
 * and then writing good interfaces for getting that new information.
 *)

Module Rudamentary.
(*
 * Here is the proof of the rudamentary case. Fix T1 and T2 arbitrary:
 *)
Parameter T1 : Type.
Parameter T2 : Type.

(*
 * In the case that T1 and T2 are completely distinct, the new information
 * for T1 will be all of T2, and the new information for T2 will be all of T1.
 * Accordingly:
 *)
Definition A := sigT (fun (t2 : T2) => T1).
Definition B := sigT (fun (t1 : T1) => T2).

(*
 * Then:
 *)
Definition f (a : A) : B := existT _ (projT2 a) (projT1 a).
Definition g (b : B) : A := existT _ (projT2 b) (projT1 b).

Lemma section: forall a, g (f a) = a.
Proof.
  intros. induction a. unfold g, f. reflexivity.
Defined.

Lemma retraction: forall b, f (g b) = b.
Proof.
  intros. induction b. unfold f, g. reflexivity.
Defined.
End Rudamentary.

(*
 * Of course, this is not useful! It doesn't make things any easier for the
 * user at all. But it captures the rudimentary most difficult case when
 * the types are totally distinct. It says, if you want proofs about T2,
 * and you have proofs about T1, you need to write proofs about T2 (obviously),
 * and that will give you proofs about T2 given T1 (of course).
 *
 * In more useful cases, the sigma will show up on just one side.
 * This is seen in the example change with algebraic ornaments, and that is one
 * we can handle usefully.
 *
 * But there are some like this that are possible but still not useful. 
 * One example of this is going between natural numbers 
 * and lists---the only way to do this is to provide enough information to 
 * construct a vector. Trivially, we can ask the user to prove things over vectors
 * as the new proof obligation, but this is obviously harder than just writing
 * proofs about lists to begin with. So if we want to support this case usefully,
 * the key challenge becomes presenting an interface to the user that prompts
 * them to provide enough information to construct a proof about vectors given a
 * proof about natural numbers, but is easier to work with than asking for
 * the vector proof directly, and easier than working with lists. We don't
 * know if this possible. The same goes for adding new constructors.
 *
 * The point here is that any question about scope really needs to ask about
 * the set of changes we can handle _usefully_, which is tied to the set of
 * changes we evaluate on real code and proofs. This is why we focused on
 * evaluating some cases and omitted the ones we knew we could handle in trivial
 * ways, but we did not yet know if we could handle in useful ways. This was 
 * probably not explicit enough, so we will need to make this more explicit.
 *)
