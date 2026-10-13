import Verification.DistributedMarzulloIntervalConsensus

open DistributedMarzulloIntervalConsensus

example : DistributedMarzulloIntervalConsensusSuite := verification_suite
example : max_overlap [] = 0 := empty_input.1
example : select_best_peak_component [] = none := empty_input.2.1
example (k : ℕ) : compute_threshold_hull [] k = none := empty_input.2.2 k
example (s : List RationalInterval) (x : ℚ) :
    sweep_overlap_count s x = (overlap_count s x : ℤ) := sweep_overlap_count_correct s x
example (s : List RationalInterval) (k : ℕ) :
    (compute_threshold_hull s k).map embed =
      DistributedMarzulloAlgorithm.thresholdHull (s.map embed) k :=
  algorithmic_hull_matches_marzullo_hull s k
example (s : List RationalInterval) (f : ℕ) (t : ℝ)
    (h : DistributedMarzulloAlgorithm.FaultModel (s.map embed) f t) :
    ∃ I, compute_threshold_hull s (s.length - f) = some I ∧
      DistributedMarzulloAlgorithm.containsTime (embed I) t :=
  algorithmic_hull_contains_true_time s f t h
example (s : List RationalInterval) (x : ℚ) (c : ℤ)
    (h : (x, c) ∈ grouped_observations s) : c = (overlap_count s x : ℤ) :=
  grouped_observation_correct s x c h
example (s : List RationalInterval) (I : RationalInterval) :
    I ∈ peak_components s ↔ IsPeakComponent s I := mem_peak_components_iff s I
example (a b c : ℚ) (hab : a ≤ b) (hbc : b ≤ c) :
    overlap_count [⟨a, b, hab⟩, ⟨b, c, hbc⟩] b = 2 :=
  (closed_interval_boundary_correct a b c hab hbc).1
example (x : ℚ) : overlap_count [⟨x, x, le_rfl⟩] x = 1 :=
  (closed_interval_boundary_correct x x x le_rfl le_rfl).2
example {s t : List RationalInterval} (h : s.Perm t) :
    select_best_peak_component s = select_best_peak_component t := selection_permutation h
example {s t : List RationalInterval} (h : s.Perm t) (k : ℕ) :
    compute_threshold_hull s k = compute_threshold_hull t k := hull_permutation h k
example : max_overlap misleading_sources = 2 :=
  peak_not_necessarily_true_time_counterexample.2.1
example : select_best_peak_component misleading_sources = some misleading_peak :=
  peak_not_necessarily_true_time_counterexample.2.2.1
example : ¬ contains misleading_peak 9 := peak_not_necessarily_true_time_counterexample.2.2.2.1
example : compute_threshold_hull misleading_sources 2 = some misleading_hull :=
  peak_not_necessarily_true_time_counterexample.2.2.2.2.1

private def unit : RationalInterval := ⟨0, 1, by norm_num⟩
private def point : RationalInterval := ⟨1, 1, le_rfl⟩
private def touch : List RationalInterval := [unit, ⟨1, 2, by norm_num⟩]
private def tie : List RationalInterval := [unit, ⟨3, 4, by norm_num⟩]
example : max_overlap [unit, unit] = 2 := by decide
example : max_overlap touch = 2 := by decide
example : compute_threshold_hull touch 2 = some point := by decide
example : compute_threshold_hull [unit] 0 = none := by decide
example : compute_threshold_hull [unit] 2 = none := by decide
example : (peak_components misleading_sources).card = 2 := by decide

-- Execution checks complement kernel proofs; they introduce no theorem or axiom.
#eval show IO Unit from do
  let cases := [
    select_best_peak_component [unit] == some unit,
    select_best_peak_component [unit, unit] == some unit,
    select_best_peak_component touch == some point,
    select_best_peak_component [point] == some point,
    select_best_peak_component tie == some unit,
    select_best_peak_component tie.reverse == some unit,
    select_best_peak_component misleading_sources == some misleading_peak,
    compute_threshold_hull misleading_sources 2 == some misleading_hull,
    grouped_observations touch == [(0, 1), (1, 2), (2, 1)],
    sweep_counters touch == [0, 1, 2, 1, 0]]
  if cases.all id then IO.println "MARZULLO_EXEC_OK: 10 cases"
  else throw (IO.userError "Marzullo executable regression failed")
