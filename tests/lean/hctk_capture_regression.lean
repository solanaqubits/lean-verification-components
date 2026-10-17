import Verification.HCTKScalarPartition
open HCTKScalarPartition
noncomputable section

example (s : CaptureState) (d eta : ℝ) :
    captureTotal (capture s d eta) = captureTotal s := capture_total s d eta
example (s : CaptureState) (eta : ℝ) : capture s 0 eta = s := capture_zero s eta
example : capture ⟨10, 0, 0, 7⟩ 10 (3/4) = ⟨0, 15/2, 5/2, 7⟩ := by
  norm_num [capture]
example : capture ⟨10, 0, 0, 7⟩ 10 0 = ⟨0, 0, 10, 7⟩ := by norm_num [capture]
example : capture ⟨10, 0, 0, 7⟩ 10 1 = ⟨0, 10, 0, 7⟩ := by norm_num [capture]
example : (capture ⟨3000, 0, 0, 1⟩ 3000 (197/200)).capturedAmount = 2955 := by
  norm_num [capture]
example : (capture ⟨1, 0, 0, 1⟩ 1 (197/200)).capturedAmount ≠ (197/200 : ℝ)^2 := by
  norm_num [capture]
example : CaptureNonnegative (capture ⟨1, 0, 0, 9⟩ 1 (197/200)) := by
  norm_num [CaptureNonnegative, capture]
example : runCaptures ⟨10, 0, 0, 7⟩ [(4, 1/2), (6, 3/4)] = ⟨0, 13/2, 7/2, 7⟩ := by
  norm_num [runCaptures, capture]
example : AdmissibleCaptures ⟨10, 0, 0, 7⟩ [(4, 1/2), (6, 3/4)] := by
  norm_num [AdmissibleCaptures, capture]
example (s : CaptureState) (xs : List (ℝ × ℝ))
    (hs : CaptureNonnegative s) (ha : AdmissibleCaptures s xs) :
    captureTotal (runCaptures s xs) = captureTotal s ∧
    CaptureNonnegative (runCaptures s xs) ∧ (runCaptures s xs).label = s.label :=
  capture_trace_contract xs s hs ha
example (s : CaptureState) (xs : List (ℝ × ℝ)) :
    collapseCapture (runCaptures s xs) = runTransfers (collapseCapture s) (xs.map Prod.fst) :=
  collapse_runCaptures xs s
-- Conservation alone cannot establish nonnegativity.
example : captureTotal (capture ⟨1, 0, 0, 7⟩ 2 (1/2)) = 1 := by norm_num [captureTotal, capture]
example : ¬ CaptureNonnegative (capture ⟨1, 0, 0, 7⟩ 2 (1/2)) := by
  norm_num [CaptureNonnegative, capture]
example : ¬ AdmissibleCaptures ⟨1, 0, 0, 7⟩ [(2, 1/2)] := by
  norm_num [AdmissibleCaptures]
example : ¬ CaptureNonnegative (capture ⟨1, 0, 0, 7⟩ 1 2) := by
  norm_num [CaptureNonnegative, capture]
example : ¬ CaptureNonnegative (capture ⟨1, 0, 0, 7⟩ 1 (-1)) := by
  norm_num [CaptureNonnegative, capture]
example : ¬ AdmissibleCaptures ⟨1, 0, 0, 7⟩ [(-1, 1/2)] := by
  norm_num [AdmissibleCaptures]
example : ¬ AdmissibleCaptures ⟨1, 0, 0, 7⟩ [(3/4, 1/2), (1/2, 1/2)] := by
  norm_num [AdmissibleCaptures, capture]
-- Same amount does not identify the integer label, much less a complete state.
example : captureTotal ⟨1, 0, 0, 7⟩ = captureTotal ⟨1, 0, 0, 8⟩ ∧ (7:ℤ) ≠ 8 := by
  norm_num [captureTotal]
end
