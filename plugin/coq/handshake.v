From Ornamental Require Import Ornaments.

(* TODO clean, explain test, add to tests *)

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

End ConnectionRecord.

Preprocess Module ConnectionRecord as ConnectionRecordPP.

Module ConnectionLift.

  Print ConnectionRecordPP.get_client_auth_flag.

  Lift HandshakePP.handshake
       HandshakeRecordPP.Handshake
  in ConnectionRecordPP.get_client_auth_flag
  as getClientAuthFlag0.
  Print getClientAuthFlag0.

  (* We need to be able to talk about the type that is just like ConnectionPP.connection, but with
     HandshakePP.handshake replaced with HandshakeRecordPP.Handhake.
   *)
  Lift Handshake.handshake
       HandshakeRecordPP.Handshake
    in ConnectionPP.connection
    as connectionPP.

  Print connectionPP. (* ouch, of course there is a second unfortunate match! *)

  (* Checking that [getClientAuthFlag0] has indeed input type [connectionPP]: *)
  Check (getClientAuthFlag0 : connectionPP -> bool).

  Print getClientAuthFlag0.
  Print connectionPP.
  (* (bool *
 (bool *
  (bool * (HandshakeRecordPP.Handshake * (bool * (bool * (bool * (bool * nat))))))))%type *)
  Print getClientAuthFlag0.
  Print ConnectionRecordPP.Connection.
  (* Inductive Connection : Set :=
    MkConnection : bool ->
                   bool ->
                   bool ->
                   HandshakeRecord.Handshake ->
                   bool ->
                   bool -> bool -> bool -> nat -> ConnectionRecordPP.Connection *)
  Lift HandshakeRecord.Handshake
       HandshakeRecordPP.Handshake
    in ConnectionRecordPP.Connection
    as connectionRecordPP. 
  Print connectionRecordPP.
  Print ConnectionRecordPP.
  Print clientAuthFlag.

  Find ornament connectionPP connectionRecordPP as orn.
  Print orn.
  Print connectionPP.
  Print connectionRecordPP.

  Print connectionPP.
  Print connectionRecordPP.
  Print getClientAuthFlag0.

  Lift connectionPP
       connectionRecordPP
    in getClientAuthFlag0
    as getClientAuthFlag.

  Print getClientAuthFlag.

End ConnectionLift.
