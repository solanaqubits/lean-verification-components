import Verification.DistributedByzantineSignedGeneralsValidity

open DistributedByzantineSignedGeneralsValidity

example (n : ℕ) (P : Parameters n) : BroadcastCorrect P := signed_broadcast_correct P

example (n : ℕ) (P : Parameters n) (s : Config n) (hr : Run P s)
    (input : Node n → Finset (SignedChain n)) (hd : Delivery P s input)
    (i j : Node n) (hi : HonestLieutenant P i) (hj : HonestLieutenant P j)
    (v : Order) (hv : v ∈ s.views i) : v ∈ (advance P s input).views j :=
  order_propagation_step hr hd hi hv hj

example (n : ℕ) (P : Parameters n) (s : Config n) (hr : Run P s)
    (ht : s.round = P.bound + 1) (i j : Node n)
    (hi : HonestLieutenant P i) (hj : HonestLieutenant P j) : s.views i = s.views j :=
  honest_views_identical hr ht hi hj

-- A raw identity list with an honest signer is not a valid signature witness.
example : ¬ Derivable faultyCommander ∅ ⟨1, [0, 1]⟩ :=
  no_honest_signature_without_issuance (i := 1) (by decide) (by simp)

example : Run faultyCommander splitRoundTwo := split_round_two_reachable
example : splitRoundTwo.views 1 = {0, 1} ∧ splitRoundTwo.views 2 = {0, 1} := by decide
example : decide (splitRoundTwo.views 1) = 0 ∧ decide (splitRoundTwo.views 2) = 0 := by decide
example : Run honestExample honestRoundTwo := honest_round_two_reachable
example : honestRoundTwo.views 1 = {1} := by decide
example : Run faultyCommander silentRoundTwo := silent_round_two_reachable
example : silentRoundTwo.views 1 = ∅ ∧ silentRoundTwo.views 2 = ∅ := by decide

-- The late packet is genuinely admissible in the ideal signature environment.
example : Delivery faultyCommander silentRoundOne lateOrder := late_order_delivery
example : decide ((finalWithoutRoundFilter faultyCommander silentRoundOne lateOrder).views 1) = 1 ∧
    decide ((finalWithoutRoundFilter faultyCommander silentRoundOne lateOrder).views 2) = 0 := by
  decide
example : decide ((advance faultyCommander silentRoundOne lateOrder).views 1) = 0 ∧
    decide ((advance faultyCommander silentRoundOne lateOrder).views 2) = 0 := by decide

example : ¬ ValidChain faultyCommander ⟨1, []⟩ 1 := malformed_chains_rejected.1
example : ¬ ValidChain faultyCommander ⟨1, [0, 0]⟩ 2 := malformed_chains_rejected.2.1

-- Fault-free one-round boundary f=0, n=2.
def zeroFaults : Parameters 2 := ⟨0, ∅, 0, by decide, by decide, 1⟩
example : BroadcastCorrect zeroFaults := signed_broadcast_correct zeroFaults
example : (advance zeroFaults (initial zeroFaults) (initial zeroFaults).outbound).views 1 = {1} :=
  by decide

-- The pigeonhole and correctness statements also instantiate beyond three nodes.
def twoFaults : Parameters 4 := ⟨0, {0, 1}, 2, by decide, by decide, 1⟩
example : BroadcastCorrect twoFaults := signed_broadcast_correct twoFaults
example : ∃ i ∈ ([0, 1, 2] : List (Node 4)), i ∉ twoFaults.faults :=
  chain_pigeonhole_honest_signer twoFaults [0, 1, 2] (by decide) (by decide)

example : Function.Bijective toOralNode := topology_bijection
