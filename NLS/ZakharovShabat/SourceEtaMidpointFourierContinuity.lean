import NLS.ZakharovShabat.SourceEtaMidpointFourierAnalytic

/-! # L2 continuity and compact midpoint Fourier heads

The actual midpoint Fourier coordinates are continuous at real L2 sources; every finite weighted block is bounded on compact real sets.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Every literal midpoint Fourier coordinate is continuous in the original
L2 source norm at each real source. -/
theorem continuousAt_sourceEtaMidpointFourierError_of_real
    (φ : realTypeSourceLocus 2) (n : ℤ) :
    ContinuousAt (fun ψ : CoeffPair 2 => sourceEtaMidpointFourierError
      (by norm_num) (by norm_num) ψ n) φ.val := by
  obtain ⟨U,_,hφU,hμ⟩ := exists_local_source_allBoundaryRoots_analytic
    (p := 2) (by norm_num) (by norm_num) φ.val φ.property
  obtain ⟨V,_,_,hreal,hτ⟩ := exists_global_source_analytic_midpoint_squaredGap
    (p := 2) (by norm_num) (by norm_num)
  have hfst : ContinuousAt (fun ψ : CoeffPair 2 => ψ.fst (-n)) φ.val :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (-n)).continuous.continuousAt.comp
      (CoeffPair.toMax 2).continuous.continuousAt.fst
  have hsnd : ContinuousAt (fun ψ : CoeffPair 2 => ψ.snd n) φ.val :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous.continuousAt.comp
      (CoeffPair.toMax 2).continuous.continuousAt.snd
  have h := (((hμ .dirichlet n φ.val hφU).continuousAt).sub
    ((hτ φ.val (hreal φ.property) n).1.continuousAt)).sub ((hfst.add hsnd).div_const 2)
  simpa only [sourceEtaMidpointFourierError,sourceDirichletMidpointDisplacement_apply,
    sourceStandardRootMidpoint] using! h

/-- Every finite weighted block of the midpoint Fourier error is uniformly
bounded on a compact real L2 source set. -/
theorem exists_sourceEtaMidpointFourierHead_bound_on_compact
    (w : Weight) (S : Finset ℤ) (K : Set (CoeffPair 2))
    (hK : IsCompact K) (hKreal : K ⊆ realTypeSourceLocus 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ φ ∈ K,
      ‖WeightedCoeff.finiteBlock (p := 2) w S
        (fun n => sourceEtaMidpointFourierError (by norm_num) (by norm_num) φ n)‖ ≤ B := by
  let H (φ : CoeffPair 2) := WeightedCoeff.finiteBlock (p := 2) w S
    (fun n => sourceEtaMidpointFourierError (by norm_num) (by norm_num) φ n)
  have hH : ContinuousOn H K := by
    intro φ hφ
    exact (WeightedCoeff.continuousAt_finiteBlock w S _ φ
      (fun n _ => continuousAt_sourceEtaMidpointFourierError_of_real ⟨φ,hKreal hφ⟩ n)).continuousWithinAt
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hH
  exact ⟨max B 0,le_max_right _ _,fun φ hφ => (hB φ hφ).trans (le_max_left _ _)⟩

end NLS.ZakharovShabat
