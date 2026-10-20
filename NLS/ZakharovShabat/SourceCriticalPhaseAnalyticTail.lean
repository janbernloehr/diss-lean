import NLS.ZakharovShabat.SourceCriticalPhaseSmoothTail
import NLS.SequenceSpaces.DenseWeightedCoordinateBound
import NLS.SequenceSpaces.WeightedAnalyticRealization
import NLS.ZakharovShabat.SobolevSourceSmoothDensity
import NLS.ZakharovShabat.SourceSimpleSpectralDomain

/-! # Analytic next-phase tails on the original Sobolev source

Dense Fourier approximation removes smooth representative assumptions and gives analytic tails gaining one derivative.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The actual next-phase offset on a fixed critical tail, realized in
the Sobolev space gaining one derivative. -/
def sourceCriticalNextPhaseTail (s K : ℕ) (ab : SobolevSource s) : ScalarSobolev (s+1) :=
  WeightedCoeff.ofFunctionOrZero (Weight.sobolev ((s+1:ℕ):ℝ)) 2
    (fun n => if K ≤ n.natAbs then sourceCriticalNextPhaseOffset s ab n else 0)

/-- Near every real original Hs source, the actual next-phase offset on
a common critical tail is analytic and uniformly bounded in H^(s+1).
The finite central indices are zeroed to avoid the finite phase's pole;
no smooth representative or extra source derivative is required. -/
theorem exists_local_sourceCriticalNextPhaseTail_analytic
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      AnalyticOnNhd ℂ (sourceCriticalNextPhaseTail s K) U ∧
      ∀ ab ∈ U, ‖sourceCriticalNextPhaseTail s K ab‖ ≤ C ∧
        ∀ n, (sourceCriticalNextPhaseTail s K ab).val n =
          if K ≤ n.natAbs then sourceCriticalNextPhaseOffset s ab n else 0 := by
  classical
  obtain ⟨U₀,hU₀,haU₀,K,hK,C,hC,hbound⟩ :=
    exists_local_source_critical_phase_smooth_tail_bound s hs a₀
  let J := higherSobolevSourceInclusion s
  obtain ⟨V,hV,haV,hroots⟩ := exists_local_source_allCriticalPoints_simple_analytic
    (p := 2) (by norm_num) (by norm_num) (J a₀.val) a₀.property
  let U := U₀ ∩ J ⁻¹' V
  have hU : IsOpen U := hU₀.inter (hV.preimage J.continuous)
  let f (ab : SobolevSource s) (n : ℤ) :=
    if K ≤ n.natAbs then sourceCriticalNextPhaseOffset s ab n else 0
  have hf (n : ℤ) : AnalyticOnNhd ℂ (fun ab => f ab n) U := by
    intro ab hab
    by_cases hn : K ≤ n.natAbs
    · simp only [f,if_pos hn]
      let κ (x : SobolevSource s) := canonicalCriticalPoints (by norm_num) (by norm_num)
        (periodOnePotential (J x)) (periodOnePotential_mem _) n
      have hκ : AnalyticAt ℂ κ ab := (hroots (J ab) hab.2 n).1.comp (J.analyticAt ab)
      have hκ0 : κ ab ≠ 0 := by
        have hnorm := (hbound ab hab.1).1 n hn
        intro hz
        change 1 ≤ ‖κ ab‖ at hnorm
        rw [hz,norm_zero] at hnorm
        norm_num at hnorm
      exact ((analyticAt_sobolevNextHamiltonianPhase_joint s (ab,κ ab) hκ0).comp
        (f := fun x : SobolevSource s => (x,κ x))
        (analyticAt_id.prod hκ)).add analyticAt_const
    · simp only [f,if_neg hn]
      exact analyticAt_const
  have hfull (ab : SobolevSource s) (hab : ab ∈ U) :
      ∃ e : ScalarSobolev (s+1), (∀ n, e.val n = f ab n) ∧ ‖e‖ ≤ C := by
    apply WeightedCoeff.exists_of_dense_bounded_coordinates
      (p := 2) (Weight.sobolev ((s+1:ℕ):ℝ)) (range (sobolevSourceOfFinsupp s)) U
      (denseRange_sobolevSourceOfFinsupp s) hU f
      (fun n => (hf n).continuousOn) C ?_ ab hab
    intro x hx hxfinite
    rcases hxfinite with ⟨c,rfl⟩
    exact (hbound (sobolevSourceOfFinsupp s c) hx.1).2
      (polynomial c.1) (polynomial c.2) (contDiff_source_polynomial _) (contDiff_source_polynomial _)
      (periodic_source_polynomial _) (periodic_source_polynomial _)
      (by intro j; simp [sobolevSourceOfFinsupp]) (by intro j; simp [sobolevSourceOfFinsupp])
  obtain ⟨han,hval⟩ := WeightedCoeff.analytic_realization_of_bound
    (p := 2) (Weight.sobolev ((s+1:ℕ):ℝ)) f hU hf C hfull
  exact ⟨U,hU,⟨haU₀,haV⟩,K,hK,C,hC,han,hval⟩

end NLS.ZakharovShabat
