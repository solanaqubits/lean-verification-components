import Verification.DistributedRaymondTreeMessageComplexity

open DistributedRaymondTreeMessageComplexity DistributedRaymondTreeMutex

-- The diameter witness includes a reachable inCS state and real send counters.
example : ∃ u owner route s, Routes (lineGraph 5 (by decide)) route owner ∧
    route owner = owner ∧
    (∀ i, route i = i ∨ (lineGraph 5 (by decide)).Adj i (route i)) ∧
    IsolatedExecution u owner route s ∧ s.mode u = .inCS ∧
    s.requestSends + s.privilegeSends = 8 := by
  have h := raymond_diameter_tightness (by decide : 2 ≤ 5)
    (lineShape 5 (by decide)).isTree
  rw [(reg_line_graph (by decide : 1 ≤ 5)).2.1] at h
  exact h

-- Local completion exists without network sends.
example {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.IsTree) (u : Fin n) :
    ∃ route s, Routes G route u ∧ route u = u ∧
      IsolatedExecution u u route s ∧ s.mode u = .inCS ∧
      s.requestSends + s.privilegeSends = 0 := by
  obtain ⟨route, hr, ho, he⟩ := tree_initialization_exists hG u
  obtain ⟨s, hs, hc⟩ := isolated_completion_exists hG u u hr ho he
  refine ⟨route, s, hr, ho, hs, hc, ?_⟩
  simpa using (isolated_request_message_bound hG hr ho he hs hc).2.2

example : Fintype.card (KaryNode 2 3) = 15 ∧
    treeDiameter (karyGraph 2 3) = 6 ∧ maximumMessages (karyGraph 2 3) = 12 ∧
    maximumMessages (karyGraph 2 3) ≠ 8 ∧ AttainedOnFin (karyGraph 2 3) 12 :=
  reg_binary_tree_h3

-- Nonbinary family: the logarithm is of the actual number of vertices.
example : Fintype.card (KaryNode 3 2) = 13 ∧ maximumMessages (karyGraph 3 2) = 8 ∧
    Nat.log 3 (Fintype.card (KaryNode 3 2)) = 2 ∧ AttainedOnFin (karyGraph 3 2) 8 := by
  have hc : Fintype.card (KaryNode 3 2) = 13 := by
    rw [kary_card]; norm_num [karyNodeCount, Finset.sum_range_succ]
  refine ⟨hc, ?_, ?_, kary_operational_attainment (by decide) (by decide)⟩
  · simp [maximumMessages, kary_diameter (by decide : 2 ≤ 3) (by decide : 1 ≤ 2)]
  · rw [hc]; decide

example : treeDiameter (starGraph 7 (by decide)) = 2 ∧
    maximumMessages (starGraph 7 (by decide)) = 4 ∧
    AttainedOnFin (starGraph 7 (by decide)) 4 :=
  ⟨(reg_star_graph (by decide : 3 ≤ 7)).2.2.1,
    (reg_star_graph (by decide : 3 ≤ 7)).2.2.2,
    star_operational_attainment (by decide)⟩

-- The three-node path requires four sends between its endpoints.
example : treeDiameter (lineGraph 3 (by decide)) = 2 ∧
    maximumMessages (lineGraph 3 (by decide)) = 4 :=
  (reg_line_graph (by decide : 1 ≤ 3)).2

example : treeDiameter (lineGraph 1 (by decide)) = 0 ∧
    maximumMessages (lineGraph 1 (by decide)) = 0 :=
  (reg_line_graph (by decide : 1 ≤ 1)).2

example : karyNodeCount 2 0 = 1 ∧ Nat.log 2 (karyNodeCount 2 0) = 0 := by
  simp

example {k : ℕ} (hk : 2 ≤ k) : Asymptotics.IsBigO Filter.atTop
    (fun h : ℕ => (maximumMessages (karyGraph k h) : ℝ))
    (fun h : ℕ => (Nat.log k (Fintype.card (KaryNode k h)) : ℝ)) := kary_cost_isBigO hk

example : DistributedRaymondTreeMessageComplexitySuite :=
  distributed_raymond_tree_message_complexity_master_suite
