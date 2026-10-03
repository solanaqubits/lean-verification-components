import Verification.MasterSuite

universe u₁ u₂ u₃ u₄ u₅ uFRI uHopf uRaft1 uRaft2 uRaft3

-- The milestone retains independently polymorphic AIR/FRI, Hopf and Raft packages.
example : MasterHundredRegistry.MasterHundredFormalSuite.{u₁, u₂, u₃, u₄, u₅,
    uFRI, uHopf, uRaft1, uRaft2, uRaft3} :=
  MasterHundredRegistry.master_hundred_registry_verified

-- Existing public type and constructor names remain available from MasterSuite.
example : MasterSuite.CryptoFullSuite.{u₁, u₂, u₃, u₄, u₅, uFRI} :=
  MasterSuite.crypto_full_master_suite
example : MasterSuite.DistributedSystemsFullSuite.{uRaft1, uRaft2, uRaft3} :=
  MasterSuite.distributed_systems_full_master_suite
example : MasterSuite.HopfFullSuite.{uHopf} := MasterSuite.hopf_full_master_suite

-- Newly nested access and the original direct projections coexist.
example (r : MasterSuite.VerificationMasterRegistry.{uRaft3, uRaft2, uRaft1,
    u₁, u₂, u₃, u₄, u₅, uHopf, uFRI}) :
    MasterHundredRegistry.MasterHundredFormalSuite.{u₁, u₂, u₃, u₄, u₅,
      uFRI, uHopf, uRaft1, uRaft2, uRaft3} := r.master_hundred_registry
example (r : MasterSuite.VerificationMasterRegistry) :
    MasterSuite.QuantumPhysicsFullSuite := r.quantum_suite
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumBeamSplitterTransform.BeamSplitterFormalSuite := r.beamsplitter_suite
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoTranscriptForkingLemma.ForkingLemmaFormalSuite := r.forking_lemma_suite
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    DistributedMarzulloAlgorithm.MarzulloAlgorithmFormalSuite := r.marzullo_suite
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumStandardQuantumLimit.QuantumSQLFormalSuite := r.sql_suite
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoSchnorrBatchVerification.SchnorrBatchVerificationFormalSuite := r.schnorr_batch_suite

-- Preserve an inherited analytic result, not merely the existence of suite names.
example (r : MasterHundredRegistry.MasterHundredFormalSuite) (c : ℝ) :
    LamzouriMollifier.normFunctional c = 1 / 8 ↔ c = -5 / 2 := r.lamzouri_suite.h_min_unique c
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    AssetSettlement.AssetSettlementFormalSuite := r.finance_risk_full_suite.settlement
