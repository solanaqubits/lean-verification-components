import Verification.MasterSuite

open DeFiLendingUtilizationFeedbackStability

example : DeFiLendingUtilizationFeedbackStabilitySuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).finance_suite.utilization_feedback

example (r : MasterSuite.VerificationMasterRegistry) : DeFiLendingUtilizationFeedbackStabilitySuite :=
  r.finance_suite.utilization_feedback

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    DeFiLendingUtilizationFeedbackStabilitySuite := r.finance_risk_full_suite.utilization_feedback

example : DeFiKinkedInterestRateUtilization.DeFiKinkedInterestRateUtilizationSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).finance_suite.kink_rate
