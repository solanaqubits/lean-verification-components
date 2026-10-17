/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedTendermintEpochTransitionSafetyMasterContract

/-! Adjacent header verification from an externally trusted anchor. Signatures and
commit consistency are explicit semantic inputs. The ideal config commitment binds
ALL EpochConfig fields, including the analysis-only faulty set and interval; it is
stronger than the production validatorsHash encoding. No cryptographic hardness,
trusting-period validity, network delivery or light-client implementation is proved. -/
namespace DistributedTendermintHeaderChainEpochAuthContract
open Finset DistributedTendermintEpochIdentityContract
open DistributedTendermintUnbondingPeriodContract
open DistributedTendermintEpochTransitionSafetyMasterContract
open DistributedTendermintAccountableSafety

structure BlockHeader (D : Type) where
  chainId : ℕ
  height : ℕ
  epochId : ℕ
  validatorsHash : D
  nextValidatorsHash : D
  parentHeaderHash : D
  deriving DecidableEq

structure Entry (V D : Type) where
  header : BlockHeader D
  current : EpochConfig V
  next : EpochConfig V
  signers : Finset (Fin current.n)

/-- Pure encodings; binding is a separate assumption, so collision countermodels are expressible. -/
structure Codec (V D : Type) where
  configHash : EpochConfig V → D
  headerHash : BlockHeader D → D

structure Binding {V D : Type} (codec : Codec V D) : Prop where
  config : Function.Injective codec.configHash
  header : Function.Injective codec.headerHash

/-- `signed v header` means an authenticated PRECOMMIT by v for the entire header.
Its correspondence with signature bytes is an external obligation. -/
abbrev Authenticator (V D : Type) := V → BlockHeader D → Bool

variable {V D : Type} [DecidableEq D]

def RootValid (codec : Codec V D) (a : Entry V D) : Prop :=
  a.header.validatorsHash = codec.configHash a.current ∧
  a.header.nextValidatorsHash = codec.configHash a.next ∧
  a.current.firstHeight ≤ a.header.height ∧ a.header.height ≤ a.current.lastHeight ∧
  a.next.firstHeight ≤ a.header.height + 1 ∧ a.header.height + 1 ≤ a.next.lastHeight

instance (codec : Codec V D) (a : Entry V D) : Decidable (RootValid codec a) := by
  unfold RootValid; infer_instance

def EntryValid (codec : Codec V D) (signed : Authenticator V D) (a : Entry V D) : Prop :=
  RootValid codec a ∧
  2 * (∑ i : Fin a.current.n, a.current.weight i) <
    3 * (∑ i ∈ a.signers, a.current.weight i) ∧
  ∀ i ∈ a.signers, signed (a.current.toGlobal i) a.header = true

instance (codec : Codec V D) signed (a : Entry V D) : Decidable (EntryValid codec signed a) := by
  unfold EntryValid; infer_instance

/-- Each child is committed by its CURRENT set; the authenticated parent's next
commitment chooses that set. Unchanged full configurations retain the epoch number in this model. -/
def LinkValid (codec : Codec V D) (a b : Entry V D) : Prop :=
  b.header.chainId = a.header.chainId ∧ b.header.height = a.header.height + 1 ∧
  b.header.parentHeaderHash = codec.headerHash a.header ∧
  b.header.validatorsHash = a.header.nextValidatorsHash ∧
  b.header.epochId = if a.header.validatorsHash = a.header.nextValidatorsHash
    then a.header.epochId else a.header.epochId + 1

instance (codec : Codec V D) (a b : Entry V D) : Decidable (LinkValid codec a b) := by
  unfold LinkValid; infer_instance

def verifyFrom (codec : Codec V D) (signed : Authenticator V D) :
    Entry V D → List (Entry V D) → Bool
  | _, [] => true
  | a, b :: rest => decide (LinkValid codec a b ∧ EntryValid codec signed b) &&
      verifyFrom codec signed b rest

/-- The anchor's header digest is trusted externally; no self-signature upgrades it to trust. -/
def verifyChain (codec : Codec V D) (signed : Authenticator V D)
    (root : Entry V D) (tail : List (Entry V D)) : Bool :=
  decide (RootValid codec root) && verifyFrom codec signed root tail

/-- Coverage is per verified height, never extrapolated to the rest of an epoch interval. -/
def lookup (h : ℕ) : List (Entry V D) → Option (Entry V D)
  | [] => none
  | a :: rest => if a.header.height = h then some a else lookup h rest

def rawHistory (entries : List (Entry V D)) : HistoryRegistry V := fun h =>
  match lookup h entries with
  | none => []
  | some a => [a.current]

def checkedHistory (codec : Codec V D) (signed : Authenticator V D)
    (root : Entry V D) (tail : List (Entry V D)) : HistoryRegistry V :=
  if verifyChain codec signed root tail then rawHistory (root :: tail) else fun _ => []

theorem verifyFrom_cons (codec : Codec V D) signed a b rest :
    verifyFrom codec signed a (b :: rest) = true ↔
      LinkValid codec a b ∧ EntryValid codec signed b ∧ verifyFrom codec signed b rest = true := by
  simp [verifyFrom, and_assoc]

theorem verified_root (codec : Codec V D) signed root tail
    (hv : verifyChain codec signed root tail = true) : RootValid codec root := by
  simp only [verifyChain, Bool.and_eq_true, decide_eq_true_eq] at hv
  exact hv.1

theorem verified_tail (codec : Codec V D) signed root tail
    (hv : verifyChain codec signed root tail = true) :
    verifyFrom codec signed root tail = true := by
  simp only [verifyChain, Bool.and_eq_true, decide_eq_true_eq] at hv
  exact hv.2

theorem verifyFrom_entries (codec : Codec V D) signed root tail
    (hv : verifyFrom codec signed root tail = true) :
    ∀ a ∈ tail, EntryValid codec signed a := by
  induction tail generalizing root with
  | nil => simp
  | cons b rest ih =>
    obtain ⟨_, hb, hr⟩ := (verifyFrom_cons codec signed root b rest).mp hv
    intro a ha
    rcases List.mem_cons.mp ha with he | he
    · subst a; exact hb
    · exact ih b hr a he

theorem verified_entries (codec : Codec V D) signed root tail
    (hv : verifyChain codec signed root tail = true) :
    ∀ a ∈ root :: tail, RootValid codec a := by
  intro a ha
  rcases List.mem_cons.mp ha with he | he
  · subst a; exact verified_root codec signed root tail hv
  · exact (verifyFrom_entries codec signed root tail
      (verified_tail codec signed root tail hv) a he).1

theorem verified_successors (codec : Codec V D) signed root tail
    (hv : verifyFrom codec signed root tail = true) :
    ∀ a ∈ tail, a.header.chainId = root.header.chainId ∧ root.header.height < a.header.height := by
  induction tail generalizing root with
  | nil => simp
  | cons b rest ih =>
    obtain ⟨hl, _, ht⟩ := (verifyFrom_cons codec signed root b rest).mp hv
    have hheight := hl.2.1
    intro a ha
    rcases List.mem_cons.mp ha with he | he
    · subst a
      exact ⟨hl.1, by omega⟩
    · obtain ⟨hd, hh⟩ := ih b ht a he
      exact ⟨hd.trans hl.1, by omega⟩

theorem verified_height_order (codec : Codec V D) signed root tail
    (hv : verifyFrom codec signed root tail = true) :
    (root :: tail).Pairwise (fun a b => a.header.height < b.header.height) := by
  induction tail generalizing root with
  | nil => simp
  | cons b rest ih =>
    obtain ⟨_, _, ht⟩ := (verifyFrom_cons codec signed root b rest).mp hv
    exact List.pairwise_cons.mpr
      ⟨fun a ha => (verified_successors codec signed root (b :: rest) hv a ha).2, ih b ht⟩

theorem verified_domain (codec : Codec V D) signed root tail
    (hv : verifyChain codec signed root tail = true) a (ha : a ∈ root :: tail) :
    a.header.chainId = root.header.chainId := by
  rcases List.mem_cons.mp ha with he | he
  · subst a; rfl
  · exact (verified_successors codec signed root tail
      (verified_tail codec signed root tail hv) a he).1

omit [DecidableEq D] in
theorem lookup_member h (entries : List (Entry V D)) a
    (hl : lookup h entries = some a) : a ∈ entries ∧ a.header.height = h := by
  induction entries with
  | nil => simp [lookup] at hl
  | cons b rest ih =>
    by_cases hb : b.header.height = h
    · simp only [lookup, hb, ↓reduceIte, Option.some.injEq] at hl
      subst a; exact ⟨List.mem_cons_self, hb⟩
    · simp only [lookup, hb, ↓reduceIte] at hl
      obtain ⟨hm, hh⟩ := ih hl
      exact ⟨List.mem_cons_of_mem b hm, hh⟩

omit [DecidableEq D] in
theorem member_covered h (entries : List (Entry V D)) a (hm : a ∈ entries)
    (hh : a.header.height = h) : ∃ b, lookup h entries = some b := by
  induction entries with
  | nil => simp at hm
  | cons b rest ih =>
    by_cases hb : b.header.height = h
    · exact ⟨b, by simp [lookup, hb]⟩
    · have ht : a ∈ rest := (List.mem_cons.mp hm).resolve_left (fun he => hb (he ▸ hh))
      obtain ⟨c, hc⟩ := ih ht
      exact ⟨c, by simp [lookup, hb, hc]⟩

theorem authenticated_lookup (codec : Codec V D) signed root tail
    (hv : verifyChain codec signed root tail = true) h a
    (hl : lookup h (root :: tail) = some a) :
    resolveHistory (checkedHistory codec signed root tail) h = some a.current := by
  obtain ⟨hm, hh⟩ := lookup_member h (root :: tail) a hl
  have ha := verified_entries codec signed root tail hv a hm
  apply (resolve_iff _ h a.current).mpr
  refine ⟨?_, ?_⟩
  · simp [checkedHistory, hv, rawHistory, hl]
  · simpa only [hh] using And.intro ha.2.2.1 ha.2.2.2.1

theorem authenticated_lookup_bounds (codec : Codec V D) signed root tail
    (hv : verifyChain codec signed root tail = true) h a
    (hl : lookup h (root :: tail) = some a) :
    UnambiguousAt (checkedHistory codec signed root tail) h :=
  ⟨a.current, (resolve_iff _ h a.current).mp
    (authenticated_lookup codec signed root tail hv h a hl)⟩

theorem rejected_chain_empty (codec : Codec V D) signed root tail
    (hv : verifyChain codec signed root tail = false) h :
    checkedHistory codec signed root tail h = [] := by simp [checkedHistory, hv]

theorem uncovered_history_none (codec : Codec V D) signed root tail h
    (hl : lookup h (root :: tail) = none) :
    resolveHistory (checkedHistory codec signed root tail) h = none := by
  unfold checkedHistory
  split <;> simp [rawHistory, hl, resolveHistory]

/-- Consensus consistency is over authenticated HEADER DIGESTS at a common height.
It is not inferred merely from valid signatures, and does not assume history equality. -/
def CommitConsistency (codec : Codec V D) (left right : List (Entry V D)) : Prop :=
  ∀ a ∈ left, ∀ b ∈ right, a.header.chainId = b.header.chainId →
    a.header.height = b.header.height → codec.headerHash a.header = codec.headerHash b.header

theorem authenticated_history_unambiguous (codec : Codec V D) (binding : Binding codec)
    signed root left right
    (hl : verifyChain codec signed root left = true)
    (hr : verifyChain codec signed root right = true)
    (hc : CommitConsistency codec (root :: left) (root :: right)) h a b
    (ha : lookup h (root :: left) = some a) (hb : lookup h (root :: right) = some b) :
    a.current = b.current := by
  obtain ⟨hma, hha⟩ := lookup_member h _ a ha
  obtain ⟨hmb, hhb⟩ := lookup_member h _ b hb
  have hd := (verified_domain codec signed root left hl a hma).trans
    (verified_domain codec signed root right hr b hmb).symm
  have he := binding.header (hc a hma b hmb hd (hha.trans hhb.symm))
  have hva := verified_entries codec signed root left hl a hma
  have hvb := verified_entries codec signed root right hr b hmb
  apply binding.config
  rw [← hva.1, ← hvb.1, he]

/-- Two accepted views agree at covered heights even when their tips differ. -/
theorem authenticated_registry_agreement (codec : Codec V D) (binding : Binding codec)
    signed root left right
    (hl : verifyChain codec signed root left = true)
    (hr : verifyChain codec signed root right = true)
    (hc : CommitConsistency codec (root :: left) (root :: right)) h a b
    (ha : lookup h (root :: left) = some a) (hb : lookup h (root :: right) = some b) :
    resolveHistory (checkedHistory codec signed root left) h =
      resolveHistory (checkedHistory codec signed root right) h := by
  rw [authenticated_lookup codec signed root left hl h a ha,
    authenticated_lookup codec signed root right hr h b hb,
    authenticated_history_unambiguous codec binding signed root left right hl hr hc h a b ha hb]

omit [DecidableEq D] in
/-- A local source of digest consistency: strict weighted quorums intersect at an
honest signer, whose authenticated precommits cannot endorse distinct header digests.
The honest-signature premise concerns a fixed height, including different rounds. -/
theorem quorum_header_digest_agreement (codec : Codec V D) (signed : Authenticator V D)
    (c : EpochConfig V) (a b : BlockHeader D) (s t : Finset (Fin c.n))
    (hf : 3 * (c.atHeight a.height).mass c.byzantine ≤ (c.atHeight a.height).total)
    (hs : (c.atHeight a.height).quorum s) (ht : (c.atHeight a.height).quorum t)
    (has : ∀ i ∈ s, signed (c.toGlobal i) a = true)
    (hbt : ∀ i ∈ t, signed (c.toGlobal i) b = true)
    (honest : ∀ i ∉ c.byzantine, signed (c.toGlobal i) a = true →
      signed (c.toGlobal i) b = true → codec.headerHash a = codec.headerHash b) :
    codec.headerHash a = codec.headerHash b := by
  obtain ⟨i, hi, hn, _⟩ := DistributedTendermintCoreSafety.quorum_honest_intersection
    (c.atHeight a.height) hf hs ht
  exact honest i hn (has i (Finset.mem_inter.mp hi).1) (hbt i (Finset.mem_inter.mp hi).2)

omit [DecidableEq D] in
theorem authenticated_commit_positive (codec : Codec V D) signed a
    (ha : EntryValid codec signed a) : 0 < (a.current.atHeight a.header.height).total := by
  apply DistributedTendermintCoreSafety.quorum_total_positive _ (s := a.signers)
  exact ha.2.1

theorem forged_epoch_config_rejected (codec : Codec V D) signed parent child
    (hm : codec.configHash child.current ≠ parent.header.nextValidatorsHash) :
    ¬ (LinkValid codec parent child ∧ EntryValid codec signed child) := by
  rintro ⟨hl, hv⟩
  exact hm (hv.1.1.symm.trans hl.2.2.2.1)

theorem committed_config_no_substitution (codec : Codec V D) (binding : Binding codec)
    signed parent child
    (hp : RootValid codec parent)
    (hc : LinkValid codec parent child ∧ EntryValid codec signed child) :
    child.current = parent.next := by
  apply binding.config
  exact hc.2.1.1.symm.trans (hc.1.2.2.2.1.trans hp.2.1)

theorem different_committed_config_rejected (codec : Codec V D) (binding : Binding codec)
    signed parent child rest (hp : RootValid codec parent) (hne : child.current ≠ parent.next) :
    verifyFrom codec signed parent (child :: rest) = false := by
  have hn : ¬ (LinkValid codec parent child ∧ EntryValid codec signed child) :=
    fun hc => hne (committed_config_no_substitution codec binding signed parent child hp hc)
  simp [verifyFrom, hn]

theorem broken_parent_rejected (codec : Codec V D) signed parent child rest
    (hm : child.header.parentHeaderHash ≠ codec.headerHash parent.header) :
    verifyFrom codec signed parent (child :: rest) = false := by
  have hn : ¬ (LinkValid codec parent child ∧ EntryValid codec signed child) :=
    fun h => hm h.1.2.2.1
  simp [verifyFrom, hn]

theorem wrong_chain_rejected (codec : Codec V D) signed parent child rest
    (hm : child.header.chainId ≠ parent.header.chainId) :
    verifyFrom codec signed parent (child :: rest) = false := by
  have hn : ¬ (LinkValid codec parent child ∧ EntryValid codec signed child) := fun h => hm h.1.1
  simp [verifyFrom, hn]

/-- Install the CHECKED registry into the actual module-200 pipeline. -/
def bindHistory (C : EpochTransitionMasterContext V) (codec : Codec V D)
    (signed : Authenticator V D) (root : Entry V D) (tail : List (Entry V D)) :
    EpochTransitionMasterContext V :=
  { C with history := checkedHistory codec signed root tail }

theorem authenticated_evidence (C : EpochTransitionMasterContext V)
    (codec : Codec V D) signed root tail
    (hv : verifyChain codec signed root tail = true) a
    (hl : lookup C.context.height (root :: tail) = some a) (ha : a.current = C.context.old)
    (p : Input C) B
    (he : attribute_evidence (C.context.old.atHeight C.context.height)
      p.reference p.evidence = .ok B) :
    AcceptedEvidence (bindHistory C codec signed root tail) p B := by
  refine ⟨?_, he⟩
  change resolveHistory (checkedHistory codec signed root tail) C.context.height = _
  rw [authenticated_lookup codec signed root tail hv _ a hl, ha]
  rfl

variable [DecidableEq V]

theorem authenticated_slashing (C : EpochTransitionMasterContext V)
    (codec : Codec V D) signed root tail
    (hv : verifyChain codec signed root tail = true) a
    (hl : lookup C.context.height (root :: tail) = some a) (ha : a.current = C.context.old)
    (p : Input C) B
    (he : attribute_evidence (C.context.old.atHeight C.context.height)
      p.reference p.evidence = .ok B)
    (hg : Admission C) (hw : WellFormed C.ledger)
    (hf : ∃ i ∈ B, (C.context.height, C.context.old.toGlobal i) ∉ C.ledger.processed ∧
      0 < available C.ledger C.context.height (C.context.old.toGlobal i)) :
    (globalBlame C.context.old B).Nonempty ∧ C.ledger.confiscated <
      (pipeline (bindHistory C codec signed root tail) p).ledger.confiscated :=
  cross_epoch_accountable_slashing_branch (bindHistory C codec signed root tail) p B
    ⟨authenticated_evidence C codec signed root tail hv a hl ha p B he, hg, hw, hf⟩

/-- Authentication failure rejects the debit. Closing the slot can still pay honest withdrawals. -/
theorem rejected_chain_debit_noop (C : EpochTransitionMasterContext V)
    (codec : Codec V D) signed root tail
    (hv : verifyChain codec signed root tail = false) (p : Input C) :
    (debit (bindHistory C codec signed root tail) p).ledger = C.ledger := by
  unfold debit
  rw [rejected_noop]
  · rfl
  · simp [historicalBlame, epoch_transition, initialState, bindHistory,
      checkedHistory, hv, resolveHistory]

variable [Fintype V]

theorem authenticated_pipeline_conservation_and_idempotence
    (C : EpochTransitionMasterContext V) (codec : Codec V D) signed root tail (p : Input C) :
    totalValue (pipeline (bindHistory C codec signed root tail) p).ledger = totalValue C.ledger ∧
    settle C.window (applyHistorical C.window C.context.height ⟨C.context.old.n, p⟩ C.rate
      (debit (bindHistory C codec signed root tail) p)) =
        pipeline (bindHistory C codec signed root tail) p ∧
    applyHistorical C.window C.context.height ⟨C.context.old.n, p⟩ C.rate
      (pipeline (bindHistory C codec signed root tail) p) =
        pipeline (bindHistory C codec signed root tail) p :=
  cross_epoch_master_value_conservation_and_idempotence (bindHistory C codec signed root tail) p

/-- Safety is still conditional on voting discipline. Conservation/replay also hold
for the fail-closed empty registry. The substantive authentication-to-debit bridge
is authenticated_evidence and authenticated_slashing above. -/
theorem header_auth_feeds_master_safety_pipeline (C : EpochTransitionMasterContext V)
    (codec : Codec V D) signed root tail (hs : SafetyConditions C) (p : Input C) :
    Agreement (bindHistory C codec signed root tail) ∧
    totalValue (pipeline (bindHistory C codec signed root tail) p).ledger = totalValue C.ledger ∧
    applyHistorical C.window C.context.height ⟨C.context.old.n, p⟩ C.rate
      (pipeline (bindHistory C codec signed root tail) p) =
        pipeline (bindHistory C codec signed root tail) p := by
  have hs' : SafetyConditions (bindHistory C codec signed root tail) :=
    ⟨hs.accepted, hs.normalized, hs.source, hs.quorum, hs.overlap,
      hs.adoption, hs.prevotes, hs.precommits⟩
  exact ⟨cross_epoch_master_safety_branch _ hs',
    pipeline_conservation (bindHistory C codec signed root tail) p,
    duplicate_after_settlement (bindHistory C codec signed root tail) p⟩

structure DistributedTendermintHeaderChainEpochAuthContractSuite : Prop where
  lookup : ∀ {V D : Type} [DecidableEq D] (codec : Codec V D) signed root tail,
    verifyChain codec signed root tail = true → ∀ h a,
    DistributedTendermintHeaderChainEpochAuthContract.lookup h (root :: tail) = some a →
    resolveHistory (checkedHistory codec signed root tail) h = some a.current
  uniqueness : ∀ {V D : Type} [DecidableEq D] (codec : Codec V D) (_binding : Binding codec)
    signed root left right,
    verifyChain codec signed root left = true → verifyChain codec signed root right = true →
    CommitConsistency codec (root :: left) (root :: right) → ∀ h a b,
    DistributedTendermintHeaderChainEpochAuthContract.lookup h (root :: left) = some a →
    DistributedTendermintHeaderChainEpochAuthContract.lookup h (root :: right) = some b →
    resolveHistory (checkedHistory codec signed root left) h =
      resolveHistory (checkedHistory codec signed root right) h
  substitution : ∀ {V D : Type} [DecidableEq D] (codec : Codec V D) (_binding : Binding codec)
    signed parent child, RootValid codec parent →
    LinkValid codec parent child ∧ EntryValid codec signed child → child.current = parent.next
  rejected_parent : ∀ {V D : Type} [DecidableEq D] (codec : Codec V D) signed parent child rest,
    child.header.parentHeaderHash ≠ codec.headerHash parent.header →
    verifyFrom codec signed parent (child :: rest) = false
  slashing : ∀ {V D : Type} [DecidableEq D] [DecidableEq V]
    (C : EpochTransitionMasterContext V) (codec : Codec V D) signed root tail,
    verifyChain codec signed root tail = true → ∀ a,
    DistributedTendermintHeaderChainEpochAuthContract.lookup C.context.height (root :: tail) =
      some a → a.current = C.context.old → ∀ (p : Input C) B,
    attribute_evidence (C.context.old.atHeight C.context.height)
      p.reference p.evidence = .ok B → Admission C → WellFormed C.ledger →
    (∃ i ∈ B, (C.context.height, C.context.old.toGlobal i) ∉ C.ledger.processed ∧
      0 < available C.ledger C.context.height (C.context.old.toGlobal i)) →
    (globalBlame C.context.old B).Nonempty ∧ C.ledger.confiscated <
      (pipeline (bindHistory C codec signed root tail) p).ledger.confiscated
  conservation_replay : ∀ {V D : Type} [DecidableEq D] [DecidableEq V] [Fintype V]
    (C : EpochTransitionMasterContext V) (codec : Codec V D) signed root tail (p : Input C),
    totalValue (pipeline (bindHistory C codec signed root tail) p).ledger = totalValue C.ledger ∧
    settle C.window (applyHistorical C.window C.context.height ⟨C.context.old.n, p⟩ C.rate
      (debit (bindHistory C codec signed root tail) p)) =
        pipeline (bindHistory C codec signed root tail) p ∧
    applyHistorical C.window C.context.height ⟨C.context.old.n, p⟩ C.rate
      (pipeline (bindHistory C codec signed root tail) p) =
        pipeline (bindHistory C codec signed root tail) p
  safety : ∀ {V D : Type} [DecidableEq D] [DecidableEq V] [Fintype V]
    (C : EpochTransitionMasterContext V) (codec : Codec V D) signed root tail,
    SafetyConditions C → ∀ p : Input C,
    Agreement (bindHistory C codec signed root tail) ∧
    totalValue (pipeline (bindHistory C codec signed root tail) p).ledger = totalValue C.ledger ∧
    applyHistorical C.window C.context.height ⟨C.context.old.n, p⟩ C.rate
      (pipeline (bindHistory C codec signed root tail) p) =
        pipeline (bindHistory C codec signed root tail) p

theorem verification_suite : DistributedTendermintHeaderChainEpochAuthContractSuite :=
  ⟨authenticated_lookup, authenticated_registry_agreement, committed_config_no_substitution,
    broken_parent_rejected, authenticated_slashing,
    authenticated_pipeline_conservation_and_idempotence,
    header_auth_feeds_master_safety_pipeline⟩

end DistributedTendermintHeaderChainEpochAuthContract
