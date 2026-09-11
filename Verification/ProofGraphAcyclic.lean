import Verification.ProofGraphDAG

set_option linter.style.header false

namespace ProofGraphAcyclic

open ProofGraphDAG

/-- Indexed certificate instructions; references may share earlier conclusions. -/
inductive DAGStep where
  | baseFact (id : ℕ)
  | axiomTruth
  | modusPonens (premIndex implIndex : ℕ)
  | zkFold (idx1 idx2 : ℕ)
  deriving DecidableEq, Repr

def StepPredecessorsValid (step : DAGStep) (k : ℕ) : Prop :=
  match step with
  | .baseFact _ | .axiomTruth => True
  | .modusPonens p i | .zkFold p i => p < k ∧ i < k

/-- Every reference in the list points to an earlier position. -/
def ValidDAG (dag : List DAGStep) : Prop :=
  ∀ k step, dag[k]? = some step → StepPredecessorsValid step k

/-- Edges point from a dependent node to its prerequisite. -/
def DirectEdge (dag : List DAGStep) (u v : ℕ) : Prop :=
  ∃ step, dag[u]? = some step ∧
    match step with
    | .baseFact _ | .axiomTruth => False
    | .modusPonens p i | .zkFold p i => v = p ∨ v = i

theorem direct_edge_strict_lt (dag : List DAGStep) (h_valid : ValidDAG dag) (u v : ℕ)
    (h_edge : DirectEdge dag u v) : v < u := by
  rcases h_edge with ⟨step, hg, he⟩
  have hv := h_valid u step hg
  cases step <;> simp_all [StepPredecessorsValid] <;> omega

theorem no_self_loop (dag : List DAGStep) (h_valid : ValidDAG dag) (u : ℕ) :
    ¬ DirectEdge dag u u := by
  intro h
  exact Nat.lt_irrefl u (direct_edge_strict_lt dag h_valid u u h)

/-- Dependency paths of positive length. -/
inductive DependencyPath (dag : List DAGStep) : ℕ → ℕ → Prop where
  | edge {u v} : DirectEdge dag u v → DependencyPath dag u v
  | cons {u v w} : DirectEdge dag u v → DependencyPath dag v w → DependencyPath dag u w

theorem dependency_path_strict_lt (dag : List DAGStep) (hv : ValidDAG dag)
    {u v : ℕ} (hp : DependencyPath dag u v) : v < u := by
  induction hp with
  | edge he => exact direct_edge_strict_lt dag hv _ _ he
  | cons he _ ih => exact Nat.lt_trans ih (direct_edge_strict_lt dag hv _ _ he)

/-- No directed dependency cycle of any positive length is possible. -/
theorem no_dependency_cycle (dag : List DAGStep) (hv : ValidDAG dag) (u : ℕ) :
    ¬ DependencyPath dag u u := by
  intro hp
  exact Nat.lt_irrefl u (dependency_path_strict_lt dag hv hp)

/-- Out-of-range references and failed prerequisites yield no formula. -/
def evalStep (baseVal : ℕ → Formula) (step : DAGStep)
    (derived : List (Option Formula)) : Option Formula :=
  match step with
  | .baseFact id => some (baseVal id)
  | .axiomTruth => some .truth
  | .modusPonens p i =>
      match derived[p]?, derived[i]? with
      | some (some fPrem), some (some (.impl f1 f2)) =>
          if fPrem = f1 then some f2 else none
      | _, _ => none
  | .zkFold n1 n2 =>
      match derived[n1]?, derived[n2]? with
      | some (some f1), some (some f2) => some (.conj f1 f2)
      | _, _ => none

def runDAG (baseVal : ℕ → Formula) (dag : List DAGStep) : List (Option Formula) :=
  dag.foldl (fun derived step => derived ++ [evalStep baseVal step derived]) []

def AllDerivedSound (val : ℕ → Prop) (derived : List (Option Formula)) : Prop :=
  ∀ (idx : ℕ) (f : Formula), derived[idx]? = some (some f) → evalFormula val f

theorem mp_eval_sound (val : ℕ → Prop) (fPrem f1 f2 : Formula)
    (hp : evalFormula val fPrem) (hi : evalFormula val (.impl f1 f2))
    (hm : fPrem = f1) : evalFormula val f2 := by
  subst f1
  exact hi hp

theorem fold_eval_sound (val : ℕ → Prop) (f1 f2 : Formula)
    (h1 : evalFormula val f1) (h2 : evalFormula val f2) :
    evalFormula val (.conj f1 f2) := ⟨h1, h2⟩

theorem eval_step_sound (val : ℕ → Prop) (baseVal : ℕ → Formula)
    (h_base : SoundBase val baseVal) (step : DAGStep) (derived : List (Option Formula))
    (hs : AllDerivedSound val derived) (f : Formula)
    (he : evalStep baseVal step derived = some f) : evalFormula val f := by
  cases step with
  | baseFact id =>
      cases he
      exact h_base id
  | axiomTruth =>
      cases he
      trivial
  | modusPonens p i =>
      dsimp [evalStep] at he
      split at he
      · rename_i fp f1 f2 hp hi
        split at he
        · rename_i hm
          cases he
          exact mp_eval_sound val fp f1 f (hs p fp hp) (hs i (.impl f1 f) hi) hm
        · contradiction
      · contradiction
  | zkFold p i =>
      dsimp [evalStep] at he
      split at he
      · rename_i f1 f2 hp hi
        cases he
        exact ⟨hs p f1 hp, hs i f2 hi⟩
      · contradiction

theorem allDerivedSound_iff (val : ℕ → Prop) (derived : List (Option Formula)) :
    AllDerivedSound val derived ↔ ∀ f, some f ∈ derived → evalFormula val f := by
  constructor
  · intro h f hm
    rcases List.mem_iff_getElem?.mp hm with ⟨i, hi⟩
    exact h i f hi
  · intro h i f hi
    exact h f (List.mem_iff_getElem?.mpr ⟨i, hi⟩)

theorem append_step_sound (val : ℕ → Prop) (baseVal : ℕ → Formula)
    (hb : SoundBase val baseVal) (step : DAGStep) (derived : List (Option Formula))
    (hs : AllDerivedSound val derived) :
    AllDerivedSound val (derived ++ [evalStep baseVal step derived]) := by
  rw [allDerivedSound_iff]
  intro f hm
  rcases List.mem_append.mp hm with hm | hm
  · exact (allDerivedSound_iff val derived).mp hs f hm
  · have he : evalStep baseVal step derived = some f := (List.mem_singleton.mp hm).symm
    exact eval_step_sound val baseVal hb step derived hs f he

/-- Successful outputs are sound even for malformed DAGs: failed references return none. -/
theorem runDAG_sound (val : ℕ → Prop) (baseVal : ℕ → Formula)
    (hb : SoundBase val baseVal) (dag : List DAGStep) :
    AllDerivedSound val (runDAG baseVal dag) := by
  have hfold (steps : List DAGStep) (derived : List (Option Formula))
      (hs : AllDerivedSound val derived) :
      AllDerivedSound val
        (steps.foldl (fun acc step => acc ++ [evalStep baseVal step acc]) derived) := by
    induction steps generalizing derived with
    | nil => exact hs
    | cons step rest ih =>
        exact ih _ (append_step_sound val baseVal hb step derived hs)
  exact hfold dag [] (by simp [allDerivedSound_iff])

structure ProofGraphAcyclicSuite : Prop where
  h_strict_lt : ∀ dag, ValidDAG dag → ∀ u v, DirectEdge dag u v → v < u
  h_no_self_loop : ∀ dag, ValidDAG dag → ∀ u, ¬ DirectEdge dag u u
  h_no_cycles : ∀ dag, ValidDAG dag → ∀ u, ¬ DependencyPath dag u u
  h_step_sound : ∀ val baseVal, SoundBase val baseVal →
    ∀ step derived, AllDerivedSound val derived →
    ∀ f, evalStep baseVal step derived = some f → evalFormula val f
  h_run_sound : ∀ val baseVal, SoundBase val baseVal →
    ∀ dag, AllDerivedSound val (runDAG baseVal dag)

theorem proof_graph_acyclic_master_verification_suite : ProofGraphAcyclicSuite := {
  h_strict_lt := direct_edge_strict_lt
  h_no_self_loop := no_self_loop
  h_no_cycles := no_dependency_cycle
  h_step_sound := eval_step_sound
  h_run_sound := runDAG_sound
}

#print axioms proof_graph_acyclic_master_verification_suite

end ProofGraphAcyclic
