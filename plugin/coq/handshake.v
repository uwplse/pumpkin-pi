From Ornamental Require Import Ornaments.

(*
 * This is a test from a user that ensures record projections lift correctly.
 *)

Set DEVOID search prove equivalence.
Set DEVOID lift type.

Set Preprocess default opaque.

Module Handshake.

  Definition handshake : Type
    := (bool * bool).

End Handshake.

Module HandshakePP.

  Preprocess Module Handshake as HandshakePP.

End HandshakePP.

Import HandshakePP.

Module HandshakeRecord.

  Record Handshake :=
    MkHandshake
      {
        handshakeType : bool;
        messageNumber : bool;
      }.

  Scheme Induction for Handshake Sort Prop.
  Scheme Induction for Handshake Sort Type.
  Scheme Induction for Handshake Sort Set.

  Definition get_handshake_type (h : HandshakePP.handshake) : bool :=
    fst h.

  Definition get_message_number (h : HandshakePP.handshake) : bool :=
    snd h.

End HandshakeRecord.

Preprocess Module HandshakeRecord as HandshakeRecordPP.

Module HandshakeLift.

  Lift HandshakePP.handshake
       HandshakeRecordPP.Handshake
  in HandshakeRecordPP.get_handshake_type
  as getHandshakeType.

  Lift HandshakePP.handshake
       HandshakeRecordPP.Handshake
    in HandshakeRecordPP.get_message_number
    as getMessageNumber.

End HandshakeLift.

Module Connection.

  Definition connection : Type
    := (bool (* client_auth_flag *)
        * (bool (* corked *)
           * (bool (* corked_io *)
              * (Handshake.handshake
                 * (bool (* is_caching_enabled *)
                    * (bool (* key_exchange_eph *)
                       * (bool (* mode *)
                          * (bool (* resume_from_cache *)
                             * nat (* server_can_send_ocsp *)
                            )
                         )
                      )
                   )
                )
             )
          )
       )
  .

End Connection.

Module ConnectionPP.

  Preprocess Module Connection as ConnectionPP.

End ConnectionPP.

Import ConnectionPP.

Module ConnectionRecord.

  Record Connection :=
    MkConnection
      {
        clientAuthFlag    : bool;
        corked            : bool;
        corkedIO          : bool;
        handshake         : HandshakeRecord.Handshake;
        isCachingEnabled  : bool;
        keyExchangeEPH    : bool;
        mode              : bool;
        resumeFromCache   : bool;
        serverCanSendOCSP : nat;
      }.

  Scheme Induction for Connection Sort Prop.
  Scheme Induction for Connection Sort Type.
  Scheme Induction for Connection Sort Set.

  Definition get_client_auth_flag (c : Connection.connection) : bool :=
    fst c.

  Definition get_corked (c : Connection.connection) : bool :=
    fst (snd c).

  Definition get_corked_IO (c : Connection.connection) : bool :=
    fst (snd (snd c)).

  Definition get_handshake (c : Connection.connection) : Handshake.handshake :=
    fst (snd (snd (snd c))).

  Definition get_is_caching_enabled (c : Connection.connection) : bool :=
    fst (snd (snd (snd (snd c)))).

  Definition get_key_exchange_EPH (c : Connection.connection) : bool :=
    fst (snd (snd (snd (snd (snd c))))).

  Definition get_mode (c : Connection.connection) : bool :=
    fst (snd (snd (snd (snd (snd (snd c)))))).

  Definition get_resume_from_cache (c : Connection.connection) : bool :=
    fst (snd (snd (snd (snd (snd (snd (snd c))))))).

  Definition get_server_can_send_ocsp (c : Connection.connection) : nat :=
    snd (snd (snd (snd (snd (snd (snd (snd c))))))).

End ConnectionRecord.

Preprocess Module ConnectionRecord as ConnectionRecordPP0.

Print ConnectionRecordPP0.

Lift Module HandshakePP.handshake
            HandshakeRecordPP.Handshake
         in ConnectionRecordPP0
         as ConnectionRecordPP1.

(* We need to be able to talk about the type that is just like ConnectionPP.connection, but with
   HandshakePP.handshake replaced with HandshakeRecordPP.Handshake.
 *)
Lift Handshake.handshake
     HandshakeRecordPP.Handshake
  in ConnectionPP.connection
  as ConnectionPPHandshakeRecordPP. (* used to be connectionPP *)

Check (ConnectionRecordPP1.get_corked : ConnectionPPHandshakeRecordPP -> bool).

Lift HandshakeRecord.Handshake
     HandshakeRecordPP.Handshake
  in ConnectionRecordPP1.Connection
  as connectionRecordPP.

Print ConnectionRecordPP1.Connection.

Print ConnectionRecordPP1.

Print ConnectionPPHandshakeRecordPP.
Print connectionRecordPP.

Print ConnectionRecordPP1.
Find ornament ConnectionPPHandshakeRecordPP connectionRecordPP.

(* Problem 1: all liftings appear to fail here *)
Lift Module
     ConnectionPPHandshakeRecordPP (* used to be connectionPP *)
     connectionRecordPP (* used to be connectionRecordPP *)
  in ConnectionRecordPP1
  as ConnectionRecordPP.


(* Trying one field manually: *)
Lift HandshakePP.handshake
     HandshakeRecordPP.Handshake
  in ConnectionRecordPP0.get_corked
  as getCorked0.

Check (getCorked0 : ConnectionPPHandshakeRecordPP -> bool).

(* indeed it ought to be the same: *)
Lemma check1 : getCorked0 = ConnectionRecordPP1.get_corked.
Proof.
  reflexivity.
Qed.

(*
this fails here, but in my original file, it succeeds, and I'm having trouble
figuring out where I must have made a mistake...
 *)
Lift ConnectionPPHandshakeRecordPP
     connectionRecordPP
  in getCorked0
  as getCorked.
