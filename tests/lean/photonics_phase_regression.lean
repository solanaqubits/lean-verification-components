import Verification.PhotonicsBeamSplitterPhaseShift

open PhotonicsBeamSplitterPhaseShift

example (T φ : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (v : Vec) :
    euclideanNorm ((mzi T φ).mulVec v) = euclideanNorm v :=
  mzi_euclidean_norm T φ hT hT1 v

example (φ : ℝ) : probability 0 φ 0 = 1 ∧ probability 1 φ 1 = 0 :=
  ⟨(mzi_endpoint_probabilities φ).1, (mzi_endpoint_probabilities φ).2.2.2⟩

example : output (1 / 2) Real.pi 0 = 0 := by
  rw [(mzi_output_amplitudes (1 / 2) Real.pi (by norm_num) (by norm_num)).1]
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]

example : probability (1 / 2) Real.pi 1 = 1 := by
  rw [(mzi_balanced_probabilities Real.pi).2]
  simp

example : probability (1 / 4) Real.pi 0 = 1 / 4 ∧
    probability (1 / 4) Real.pi 1 = 3 / 4 := by
  have h := mzi_probabilities_exact (1 / 4) Real.pi (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : MithraicPhaseCollapse.visibility
    (visibilityPattern 1 (1 / 4) (by norm_num) (by norm_num) (by norm_num)) = 3 / 5 := by
  rw [(mzi_visibility_pattern_bridge 1 (1 / 4) (by norm_num) (by norm_num) (by norm_num)).2]
  norm_num

example (offset : ℝ) :
    intensity 1 (1 / 2) (-offset + offset) 0 = 1 ∧
    intensity 1 (1 / 2) ((Real.pi - offset) + offset) 0 = 0 := by
  have h := (mzi_static_phase_extrema 1 (1 / 2) offset
    (by norm_num) (by norm_num) (by norm_num)).2
  norm_num at h ⊢
  exact h

example (φ : ℝ) : intensity 0 (1 / 2) φ 0 = 0 ∧ intensity 0 (1 / 2) φ 1 = 0 := by
  simp [intensity]

example (φ : ℝ) :
    intensity 2 (1 / 2) φ 0 = SolarisMithraCore.constructive_intensity ⟨2, φ⟩ :=
  (mzi_balanced_bridge_to_solaris 2 φ (by norm_num)).1

-- The geometric law is an explicit assumption, including the zero-slope case.
example (ΔL φ₀ : ℝ) :
    intensity 1 (1 / 2) φ₀ 1 = Real.sin (φ₀ / 2) ^ 2 := by
  have h := (mzi_phase_geometric_affine 1 (1 / 2) φ₀ 0 ΔL φ₀
    (by norm_num) (by norm_num) (by ring)).2
  norm_num at h ⊢
  exact h

example : PhotonicsBeamSplitterPhaseShiftSuite := photonics_beam_splitter_phase_shift_master_suite
