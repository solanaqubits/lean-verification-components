import Verification.DistributedCoordinatedAttackImpossibility

open DistributedCoordinatedAttackImpossibility

example (T : ℕ) : ¬ ∃ (M S : Type) (P : Protocol T M S),
    Agreement P ∧ ValidityZero P ∧ ReliableSuccess P := no_correct_protocol T
example : ¬ ∃ (M S : Type) (P : Protocol 0 M S),
    Agreement P ∧ ValidityZero P ∧ ReliableSuccess P := no_correct_protocol 0
example : Agreement (retreatProtocol 7) ∧ ValidityZero (retreatProtocol 7) ∧
    ¬ ReliableSuccess (retreatProtocol 7) := trivial_retreat_protocol_satisfies_partial 7
example : ReliableSuccess ackProtocol := ack_reliable_success
example : ¬ Agreement ackProtocol := ack_protocol_not_agreement
example : decision ackProtocol (fun _ => 1) lostAckSchedule 0 = 0 ∧
    decision ackProtocol (fun _ => 1) lostAckSchedule 1 = 1 := ack_loss_counterexample.2.2
example : execution ackProtocol (fun _ => 1) lostAckSchedule 2 1 =
    execution ackProtocol (fun _ => 1) ackSchedule 2 1 := ack_loss_sender_unchanged
example : (deliveries ackSchedule).card = 2 := by decide
example : (deliveries lostAckSchedule).card = 1 := by decide
example (D : DeliverySchedule 3) :
    eraseDelivery (eraseDelivery D 0 2) 1 2 = eraseDelivery (eraseDelivery D 1 2) 0 2 :=
  erase_deliveries_commute D 0 1 2 2
example (M S : Type) (P : Protocol 2 M S) (ha : Agreement P) (hv : ValidityZero P)
    (x : Inputs) (p : Process) : decision P x lostAckSchedule p = 0 :=
  two_round_ack_safe_retreat P ha hv x p
example (M S : Type) (P : Protocol 4 M S) (x : Inputs) (D : DeliverySchedule 4)
    (s : Process) (r : Fin 4) :
    execution P x (eraseDelivery D s r) (r.val + 1) s = execution P x D (r.val + 1) s :=
  local_state_independent_of_undelivered_msg P x D s r
example : DistributedCoordinatedAttackImpossibilitySuite :=
  distributed_coordinated_attack_impossibility_master_suite
