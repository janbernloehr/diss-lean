import NLS.ZakharovShabat.SourceDirichletSpectralReachability

/-! # Finite compositions of actual Hilbert spectral flows

A finite list of indexed real-time moves acts by the constructed complete
source flows. Every composition preserves the original norm, discriminant
and periodic data. Endpoint reachability constructs a list placing any
finite set of terminals at their original periodic endpoints, while
retaining every terminal outside that set.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- Apply a finite list of actual indexed spectral moves in list order. -/
def sourceDirichletSpectralFlowSequence (φ : realTypeSourceLocus 2)
    (moves : List (ℤ × ℝ)) : realTypeSourceLocus 2 :=
  moves.foldl (fun ψ move => sourceDirichletSpectralFlow move.1 ψ move.2) φ

@[simp] theorem sourceDirichletSpectralFlowSequence_nil (φ : realTypeSourceLocus 2) :
    sourceDirichletSpectralFlowSequence φ [] = φ := rfl

@[simp] theorem sourceDirichletSpectralFlowSequence_cons (φ : realTypeSourceLocus 2)
    (move : ℤ × ℝ) (moves : List (ℤ × ℝ)) :
    sourceDirichletSpectralFlowSequence φ (move :: moves) =
      sourceDirichletSpectralFlowSequence (sourceDirichletSpectralFlow move.1 φ move.2) moves := rfl

@[simp] theorem sourceDirichletSpectralFlowSequence_append_singleton
    (φ : realTypeSourceLocus 2) (moves : List (ℤ × ℝ)) (k : ℤ) (t : ℝ) :
    sourceDirichletSpectralFlowSequence φ (moves ++ [(k,t)]) =
      sourceDirichletSpectralFlow k (sourceDirichletSpectralFlowSequence φ moves) t := by
  simp [sourceDirichletSpectralFlowSequence,List.foldl_append]

/-- Every finite composition preserves the original Hilbert norm and
all actual discriminant values. -/
theorem sourceDirichletSpectralFlowSequence_conserved
    (φ : realTypeSourceLocus 2) (moves : List (ℤ × ℝ)) :
    ‖(sourceDirichletSpectralFlowSequence φ moves).val‖ = ‖φ.val‖ ∧ ∀ w : ℂ,
      canonicalDiscriminant (by simp) (periodOnePotential (sourceDirichletSpectralFlowSequence φ moves).val) w =
        canonicalDiscriminant (by simp) (periodOnePotential φ.val) w := by
  induction moves generalizing φ with
  | nil => exact ⟨rfl,fun _ => rfl⟩
  | cons move moves ih =>
    rw [sourceDirichletSpectralFlowSequence_cons]
    have hfirst := sourceDirichletSpectralFlow_conserved move.1 φ move.2
    have htail := ih (sourceDirichletSpectralFlow move.1 φ move.2)
    exact ⟨htail.1.trans hfirst.1,fun w => (htail.2 w).trans (hfirst.2 w)⟩

/-- Every finite composition fixes every gap and both original
periodic endpoints, whether open or collapsed. -/
theorem sourceDirichletSpectralFlowSequence_periodicData
    (φ : realTypeSourceLocus 2) (moves : List (ℤ × ℝ)) (j : ℤ) :
    let ψ := sourceDirichletSpectralFlowSequence φ moves;
    canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) j =
      canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) j ∧
    canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) j =
      canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) j ∧
    canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) j =
      canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) j := by
  induction moves generalizing φ with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons move moves ih =>
    dsimp only
    rw [sourceDirichletSpectralFlowSequence_cons]
    have htail := ih (sourceDirichletSpectralFlow move.1 φ move.2)
    have hends := canonicalPeriodicEndpoints_sourceDirichletSpectralGlobalCurve move.1 j φ move.2
    exact ⟨htail.1.trans (canonicalPeriodicGap_sourceDirichletSpectralFlow move.1 j φ move.2),
      htail.2.1.trans hends.1,htail.2.2.trans hends.2⟩

/-- Construct actual indexed moves placing every terminal in a finite
set at one of its original periodic endpoints. Previously placed
terminals remain placed, and every outside terminal remains unchanged. -/
theorem exists_sourceDirichletSpectralFlowSequence_periodicTerminals
    (φ : realTypeSourceLocus 2) (A : Finset ℤ) :
    ∃ moves : List (ℤ × ℝ),
      let ψ := sourceDirichletSpectralFlowSequence φ moves;
      (∀ j ∈ A, sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet j ψ.val = 0 ∧
        (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ.val j =
          canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) j ∨
        canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ.val j =
          canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) j)) ∧
      ∀ j ∉ A, canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ.val j =
        canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val j ∧
        sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet j ψ.val =
          sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet j φ.val := by
  classical
  let μ (ψ : realTypeSourceLocus 2) (j : ℤ) := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ.val j
  let S (ψ : realTypeSourceLocus 2) (j : ℤ) := sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet j ψ.val
  let L (ψ : realTypeSourceLocus 2) (j : ℤ) :=
    canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) j
  let R (ψ : realTypeSourceLocus 2) (j : ℤ) :=
    canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) j
  change ∃ moves, (∀ j ∈ A, S (sourceDirichletSpectralFlowSequence φ moves) j = 0 ∧
    (μ (sourceDirichletSpectralFlowSequence φ moves) j = L φ j ∨
      μ (sourceDirichletSpectralFlowSequence φ moves) j = R φ j)) ∧
    ∀ j ∉ A, μ (sourceDirichletSpectralFlowSequence φ moves) j = μ φ j ∧
      S (sourceDirichletSpectralFlowSequence φ moves) j = S φ j
  induction A using Finset.induction with
  | empty => exact ⟨[],by simp,fun _ _ => ⟨rfl,rfl⟩⟩
  | @insert k A hk ih =>
    obtain ⟨moves,hplaced,houtside⟩ := ih
    let ψ := sourceDirichletSpectralFlowSequence φ moves
    obtain ⟨t,ht,hend⟩ := exists_sourceDirichletSpectralFlow_periodicTerminal k ψ
    have hstep (j : ℤ) (hjk : j ≠ k) :
        μ (sourceDirichletSpectralFlow k ψ t) j = μ ψ j ∧
        S (sourceDirichletSpectralFlow k ψ t) j = S ψ j :=
      other_dirichletTerminals_sourceDirichletSpectralGlobalCurve k j hjk ψ t
    refine ⟨moves ++ [(k,t)],?_,?_⟩
    · intro j hj
      rw [sourceDirichletSpectralFlowSequence_append_singleton]
      rcases Finset.mem_insert.mp hj with rfl | hj
      · refine ⟨ht,?_⟩
        have he := sourceDirichletSpectralFlowSequence_periodicData φ moves j
        rcases hend with heL | heR
        · exact Or.inl (heL.trans he.2.1)
        · exact Or.inr (heR.trans he.2.2)
      · have hjk : j ≠ k := by intro he; exact hk (he ▸ hj)
        have hprevious := hplaced j hj
        refine ⟨(hstep j hjk).2.trans hprevious.1,?_⟩
        rcases hprevious.2 with heL | heR
        · exact Or.inl ((hstep j hjk).1.trans heL)
        · exact Or.inr ((hstep j hjk).1.trans heR)
    · intro j hj
      rw [sourceDirichletSpectralFlowSequence_append_singleton]
      have hjk : j ≠ k := by intro he; subst j; exact hj (Finset.mem_insert_self k A)
      have hjA : j ∉ A := fun h => hj (Finset.mem_insert_of_mem h)
      exact ⟨(hstep j hjk).1.trans (houtside j hjA).1,
        (hstep j hjk).2.trans (houtside j hjA).2⟩

/-- Finitely many nonperiodic terminals can all be made periodic by
a constructed finite list of actual source moves. Every initially
periodic terminal retains its original Dirichlet root. -/
theorem exists_sourceDirichletSpectralFlowSequence_all_terminals_periodic
    (φ : realTypeSourceLocus 2)
    (hfinite : {j : ℤ | sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num)
      .dirichlet j φ.val ≠ 0}.Finite) :
    ∃ moves : List (ℤ × ℝ),
      let ψ := sourceDirichletSpectralFlowSequence φ moves;
      (∀ j : ℤ, sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet j ψ.val = 0) ∧
      ∀ j : ℤ, sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet j φ.val = 0 →
        canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ.val j =
          canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val j := by
  classical
  let A := hfinite.toFinset
  obtain ⟨moves,hplaced,houtside⟩ := exists_sourceDirichletSpectralFlowSequence_periodicTerminals φ A
  refine ⟨moves,?_,?_⟩
  · intro j
    by_cases hj : j ∈ A
    · exact (hplaced j hj).1
    · have hz : sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet j φ.val = 0 := by
        by_contra h
        exact hj (hfinite.mem_toFinset.mpr h)
      exact (houtside j hj).2.trans hz
  · intro j hj
    have hnot : j ∉ A := by
      intro hmem
      exact (hfinite.mem_toFinset.mp hmem) hj
    exact (houtside j hnot).1

end NLS.ZakharovShabat
