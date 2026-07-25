import TPTND.Operational.TraceAdequacy

/-! # Worked `↦` examples

The operational layer `Reduces` (written `↦`) evaluates a *list* of run claims,
appending one claim per step, so a reduction sequence records its own history.
This file exercises it concretely.

* `honest_trace` — a seven-step `↦*` sequence from the empty list: two draws,
  two `sampling` collections, `sumIntro`, `sumElim`.  Every side condition is
  discharged explicitly, so this is a genuine reduction, not a schema.

* `reuse_is_reducible` — the ↦ layer is deliberately **provenance-free**, so it
  happily pools a batch *with itself* (`update` needs only that both batches be
  in the list).  This is the step whose certificate the static layer must
  refuse: `Provenance.disjoint` fails when the two batches are the same runs.
  The reduction is legal; the certificate is not.  That asymmetry is the reason
  `CertTrace` carries labels at all.

* `labelled_certifies` — the same evidence as a *labelled* trace: `CertTrace`
  fixes the provenance bookkeeping, `CertTrace.reduces` erases the labels back
  to a genuine `↦*` sequence, and `CertTrace.certified` produces a
  checker-accepted certificate for every cell. -/

namespace TPTND

private def P (n d : Nat) : Prob := clampProb ((n : ℚ) / d)
private def A : Output := .atom "A"
private def B : Output := .atom "B"
private def x : String := "x"
private def tx : Term := .atom x

/-- A context in which `x` may report `A`, `B`, or the compound event. -/
private def Γx : Context :=
  [⟨x, {x}, A, .unknown⟩, ⟨x, {x}, B, .unknown⟩, ⟨x, {x}, .sum A B, .unknown⟩]

private theorem suppA : supports Γx x A := ⟨⟨x, {x}, A, .unknown⟩, by simp [Γx], rfl, rfl⟩
private theorem suppB : supports Γx x B :=
  ⟨⟨x, {x}, B, .unknown⟩, by simp [Γx], rfl, rfl⟩

-- the run claims the trace produces, named for readability
private def rA : RunClaim := ⟨tx, 1, A, Prob.one⟩
private def rB : RunClaim := ⟨tx, 1, B, Prob.one⟩
private def sA : RunClaim := ⟨tx, 2, A, P 1 2⟩
private def sB : RunClaim := ⟨tx, 2, B, P 1 2⟩
private def sAB : RunClaim := ⟨tx, 2, .sum A B, P 1 1⟩

private theorem disjAB : Output.syntacticallyDisjoint A B = true := by decide

/-- `Γx` is admissible: every entry has a nonempty support and an opaque
    constraint, so no variable commits any mass. -/
private theorem wfΓx : contextWF Γx = true := by
  simp [contextWF, Γx, entryWF, constraintWF, variableNames, variableMass,
        groupMass, exactMass, intervalLower, A, B]

/-- Each `(variable, output)` pair has at most one assumption in `Γx` — the
    uniqueness `experiment`/`obs` demand, and what `CertTrace.certified` needs. -/
private theorem uniqΓx : ∀ u α', (supportEntries Γx (.atom u) α').length ≤ 1 := by
  intro u α'
  simp only [supportEntries, Γx, List.filter_cons, List.filter_nil]
  by_cases hu : x = u
  · rcases eq_or_ne α' A with rfl | h1
    · simp [hu, A, B]
    · rcases eq_or_ne α' B with rfl | h2
      · simp [hu, A, B]
      · rcases eq_or_ne α' (Output.sum A B) with rfl | h3
        · simp [hu, A, B]
        · simp [hu, beq_eq_false_iff_ne.mpr (Ne.symm h1),
                    beq_eq_false_iff_ne.mpr (Ne.symm h2),
                    beq_eq_false_iff_ne.mpr (Ne.symm h3)]
  · simp [hu]

/-- **A seven-step reduction.**  `[] ↦* [A-draw, B-draw, A-rate, B-rate,
    (A+B)-rate, A-rate-again]`: two draws, two collections, a sum introduction
    and a sum elimination. -/
theorem honest_trace :
    ReducesMany Γx [] [rA, rB, sA, sB, sAB, sA] := by
  -- draw A
  refine .step (L' := [rA]) (by simpa using Reduces.event (L := []) suppA) ?_
  -- draw B
  refine .step (L' := [rA, rB]) (by simpa using Reduces.event (L := [rA]) suppB) ?_
  -- collect the two draws at output A: one hit in two runs
  refine .step (L' := [rA, rB, sA]) ?_ ?_
  · have h := Reduces.sampling (Γ := Γx) (L := [rA, rB]) (t := tx) (α := A)
      (runs := [rA, rB]) (f := P 1 2)
      (by intro r hr; simpa using hr)
      (by intro r hr; rcases List.mem_cons.mp hr with h | h <;> simp_all [rA, rB])
      (by intro r hr; rcases List.mem_cons.mp hr with h | h <;> simp_all [rA, rB])
      (by simp) ⟨"A", rfl⟩ suppA
      (by simp [rA, rB, A, B, P, clampProb]; norm_num)
    simpa [sA] using h
  -- collect the same two draws at output B
  refine .step (L' := [rA, rB, sA, sB]) ?_ ?_
  · have h := Reduces.sampling (Γ := Γx) (L := [rA, rB, sA]) (t := tx) (α := B)
      (runs := [rA, rB]) (f := P 1 2)
      (by intro r hr; rcases List.mem_cons.mp hr with h | h <;> simp_all)
      (by intro r hr; rcases List.mem_cons.mp hr with h | h <;> simp_all [rA, rB])
      (by intro r hr; rcases List.mem_cons.mp hr with h | h <;> simp_all [rA, rB])
      (by simp) ⟨"B", rfl⟩ suppB
      (by simp [rA, rB, A, B, P, clampProb]; norm_num)
    simpa [sB] using h
  -- add the two disjoint rates
  refine .step (L' := [rA, rB, sA, sB, sAB]) ?_ ?_
  · have h := Reduces.sumIntro (Γ := Γx) (L := [rA, rB, sA, sB]) (t := tx)
      (n := 2) (α := A) (β := B) (f := P 1 2) (g := P 1 2) (h := P 1 1)
      disjAB (by simp [sA]) (by simp [sB])
      (by simp [P, clampProb]; norm_num)
    simpa [sAB] using h
  -- and strip one back off
  refine .step (L' := [rA, rB, sA, sB, sAB, sA]) ?_ .refl
  have h := Reduces.sumElim (Γ := Γx) (L := [rA, rB, sA, sB, sAB]) (t := tx)
    (n := 2) (α := A) (β := B) (r := P 1 1) (q := P 1 2) (h := P 1 2)
    disjAB (by simp [sAB]) (by simp [sB])
    (by simp [P, clampProb]; norm_num)
  simpa [sA] using h

/-- **The ↦ layer permits evidence reuse.**  `update` requires only that both
    batches appear in the list — so it will pool the batch `sA` *with itself*,
    reporting four samples where only two runs were ever drawn.

    This step is perfectly legal operationally.  Its certificate is not: the
    static `update` demands `Provenance.disjoint σ τ`, and the two batches carry
    the same tokens.  Labelling the trace (`CertTrace`) is exactly what makes
    that refusal possible. -/
theorem reuse_is_reducible :
    Reduces Γx [rA, rB, sA] [rA, rB, sA, ⟨tx, 4, A, P 1 2⟩] := by
  have h := Reduces.update (Γ := Γx) (L := [rA, rB, sA]) (t := tx) (α := A)
    (n := 2) (m := 2) (f := P 1 2) (g := P 1 2) (h := P 1 2)
    (by norm_num) (by norm_num) (by simp [sA]) (by simp [sA])
    (by simp [P, clampProb]; norm_num)
  simpa using h

/-- The same two draws as a **labelled** trace: each draw carries a fresh token
    and the collection unions them. -/
theorem labelled_certifies :
    ∃ T : List (RunClaim × Provenance),
      -- it is a genuine reduction sequence …
      ReducesMany Γx [] (T.map (·.1)) ∧
      -- … and every cell of it has a checker-accepted certificate
      (∀ c ∈ T, ∃ d : Derivation,
        checkDerivation d = Except.ok () ∧
        d.conclusion = ⟨Γx, .term (cellTC c)⟩) := by
  classical
  -- two labelled draws
  have t1 : CertTrace Γx ([] ++ [(rA, ({"ρ0"} : Provenance))]) :=
    .event [] x "A" "ρ0" .nil suppA
  have t2 : CertTrace Γx
      ([(rA, ({"ρ0"} : Provenance))] ++ [(rB, ({"ρ1"} : Provenance))]) :=
    .event _ x "B" "ρ1" (by simpa using t1) suppB
  have t2' : CertTrace Γx [(rA, ({"ρ0"} : Provenance)), (rB, ({"ρ1"} : Provenance))] := by
    simpa using t2
  exact ⟨[(rA, ({"ρ0"} : Provenance)), (rB, ({"ρ1"} : Provenance))],
         t2'.reduces, t2'.certified wfΓx uniqΓx⟩

end TPTND
