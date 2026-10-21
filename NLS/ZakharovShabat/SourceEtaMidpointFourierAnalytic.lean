import NLS.ZakharovShabat.SourceEtaMidpointFourierSmoothTail
import NLS.SequenceSpaces.DenseWeightedCoordinateBound
import NLS.SequenceSpaces.WeightedTailCompletion
import NLS.SequenceSpaces.WeightedAnalyticRealization
import NLS.ZakharovShabat.SobolevSourceSmoothDensity
import NLS.ZakharovShabat.SourceBoundaryRootsAnalyticNeighborhood
import NLS.ZakharovShabat.SourceSymmetricContour

/-! # The complete analytic midpoint Fourier remainder

Dense Fourier approximation and finite-head completion produce an analytic one-derivative gain on the original source, including all indices and collapsed gaps.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The complete literal midpoint Fourier error in the target gaining one derivative. -/
def sourceEtaMidpointFourierRemainder (s : ℕ) (ab : SobolevSource s) :
    WeightedCoeff (Weight.sobolev ((s:ℝ)+1)) 2 :=
  WeightedCoeff.ofFunctionOrZero (Weight.sobolev ((s:ℝ)+1)) 2
    (fun n => sourceEtaMidpointFourierError (by simp) (by norm_num)
      (higherSobolevSourceInclusion s ab) n)

/-- The literal midpoint Fourier error gains one derivative analytically
near every real original Hs source, including the finite central block
and collapsed gaps, with no smooth representative assumption. -/
theorem exists_local_sourceEtaMidpointFourierRemainder_analytic
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) :
    ∃ V : Set (SobolevSource s), IsOpen V ∧ a₀.val ∈ V ∧
      ∃ B : ℝ, 0 ≤ B ∧ AnalyticOnNhd ℂ (sourceEtaMidpointFourierRemainder s) V ∧
        ∀ ab ∈ V, ‖sourceEtaMidpointFourierRemainder s ab‖ ≤ B ∧
          ∀ n, (sourceEtaMidpointFourierRemainder s ab).val n =
            sourceEtaMidpointFourierError (by simp) (by norm_num)
              (higherSobolevSourceInclusion s ab) n := by
  classical
  obtain ⟨U₀,hU₀,haU₀,K,_,C,hC,hbound⟩ :=
    exists_local_source_eta_midpoint_smooth_fourier_tail_bound s hs a₀
  let J := higherSobolevSourceInclusion s
  obtain ⟨Vμ,hVμ,haVμ,hμ⟩ := exists_local_source_allBoundaryRoots_analytic
    (p := 2) (by norm_num) (by norm_num) (J a₀.val) a₀.property
  obtain ⟨Vτ,hVτ,_,hrealτ,hτ⟩ := exists_global_source_analytic_midpoint_squaredGap
    (p := 2) (by norm_num) (by norm_num)
  let U := U₀ ∩ (J ⁻¹' Vμ ∩ J ⁻¹' Vτ)
  have hU : IsOpen U := hU₀.inter ((hVμ.preimage J.continuous).inter (hVτ.preimage J.continuous))
  have haU : a₀.val ∈ U := ⟨haU₀,haVμ,hrealτ a₀.property⟩
  let f (ab : SobolevSource s) (n : ℤ) :=
    sourceEtaMidpointFourierError (by simp) (by norm_num) (J ab) n
  have hf (n : ℤ) : AnalyticOnNhd ℂ (fun ab => f ab n) U := by
    intro ab hab
    have hcoeff : AnalyticAt ℂ (fun x : SobolevSource s => (x.1.val (-n)+x.2.val n)/2) ab :=
      ((((WeightedCoeff.evalCLM _ 2 (-n)).analyticAt _).comp analyticAt_fst).add
        (((WeightedCoeff.evalCLM _ 2 n).analyticAt _).comp analyticAt_snd)).div_const
    have h := (((hμ .dirichlet n (J ab) hab.2.1).comp (J.analyticAt ab)).sub
      (((hτ (J ab) hab.2.2 n).1).comp (J.analyticAt ab))).sub hcoeff
    simpa only [f,sourceEtaMidpointFourierError,sourceDirichletMidpointDisplacement_apply,
      sourceStandardRootMidpoint,higherSobolevSourceInclusion_fst,higherSobolevSourceInclusion_snd,J] using! h
  let t (ab : SobolevSource s) (n : ℤ) := if K ≤ n.natAbs then f ab n else 0
  have ht (n : ℤ) : ContinuousOn (fun ab => t ab n) U := by
    by_cases hn : K ≤ n.natAbs
    · simpa only [t,if_pos hn] using (hf n).continuousOn
    · simp only [t,if_neg hn]
      exact continuousOn_const
  have htail (ab : SobolevSource s) (hab : ab ∈ U) :
      ∃ e : ScalarSobolev (s+1), (∀ n, e.val n = t ab n) ∧ ‖e‖ ≤ C := by
    apply WeightedCoeff.exists_of_dense_bounded_coordinates
      (p := 2) (Weight.sobolev ((s+1:ℕ):ℝ)) (range (sobolevSourceOfFinsupp s)) U
      (denseRange_sobolevSourceOfFinsupp s) hU t ht C ?_ ab hab
    intro x hx hxfinite
    rcases hxfinite with ⟨c,rfl⟩
    exact hbound (sobolevSourceOfFinsupp s c) hx.1
      (polynomial c.1) (polynomial c.2) (contDiff_source_polynomial _) (contDiff_source_polynomial _)
      (periodic_source_polynomial _) (periodic_source_polynomial _)
      (by intro j; simp [sobolevSourceOfFinsupp]) (by intro j; simp [sobolevSourceOfFinsupp])
  obtain ⟨V,hV,haV,hVU,B,hB,hfull⟩ := WeightedCoeff.exists_local_full_bound_of_tail
    (p := 2) (Weight.sobolev ((s+1:ℕ):ℝ)) f hU (fun n => (hf n).continuousOn)
    K C hC htail a₀.val haU
  have hfull' (ab : SobolevSource s) (hab : ab ∈ V) :
      ∃ e : WeightedCoeff (Weight.sobolev ((s:ℝ)+1)) 2,
        (∀ n, e.val n = f ab n) ∧ ‖e‖ ≤ B := by
    obtain ⟨e,he,hen⟩ := hfull ab hab
    refine ⟨WeightedCoeff.sobolevInclusion (by norm_num : (s:ℝ)+1 ≤ ((s+1:ℕ):ℝ)) e,?_,
      (WeightedCoeff.norm_sobolevInclusion_le _ e).trans hen⟩
    intro n
    simpa only [WeightedCoeff.sobolevInclusion_apply] using he n
  obtain ⟨han,hval⟩ := WeightedCoeff.analytic_realization_of_bound
    (p := 2) (Weight.sobolev ((s:ℝ)+1)) f hV (fun n ab hab => hf n ab (hVU hab)) B hfull'
  exact ⟨V,hV,haV,B,hB,han,hval⟩

end NLS.ZakharovShabat
