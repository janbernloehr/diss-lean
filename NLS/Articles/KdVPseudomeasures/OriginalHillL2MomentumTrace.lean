import NLS.Articles.KdVPseudomeasures.OriginalHillL2MomentumFunctionals
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapMomentumDifferential
import NLS.Articles.KdVPseudomeasures.OriginalHillL2FiniteGapApproximation
import NLS.SequenceSpaces.PhysicalAnalyticIdentity

/-! The original period-one KdV momentum trace on the genuine physical L2
space. Finite-gap derivative equality extends by density in the TRUE L2
norm; no finite-action identity on an open source neighborhood is used. -/
noncomputable section
open Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem fderiv_hillL2ActionEnergy_eq_momentum_of_finiteGap
    (u : HillRealL2BanachSource)
    (hf : hillL2SourceInclusion u ∈ hillRealFiniteGapLocus) :
    fderiv ℝ hillL2ActionEnergy u=fderiv ℝ hillL2Momentum u := by
  obtain ⟨b,hb,s,hs,hD⟩ := exists_hillL2_finite_action_momentum_differential u hf
  have hs' : ∀ n : ℕ+, n ∉ s → (hillL2NativeMap u).val.val.val (n:ℤ)=0 := by
    intro n hn
    rw [hillL2NativeMap_apply]
    exact hs n hn
  apply ContinuousLinearMap.ext
  intro h
  rw [fderiv_hillL2ActionEnergy_apply,
    WeightedCoeff.fourierRealZeroHilbertPairing_signed_half_finite _ _ s hs',Finset.mul_sum]
  have he : (∑ n ∈ s, (2*Real.pi:ℂ)*((n:ℕ):ℂ)*
      ((hillL2NativeMap u).val.val.val (n:ℤ)*((fderiv ℝ hillL2NativeMap u) h).val.val.val (-(n:ℤ))+
        (hillL2NativeMap u).val.val.val (-(n:ℤ))*((fderiv ℝ hillL2NativeMap u) h).val.val.val (n:ℤ)))=
      ∑ n ∈ s, ((2*Real.pi*(n:ℕ):ℝ):ℂ)*(fderiv ℝ (hillL2CanonicalAction n) u) h := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [fderiv_hillL2CanonicalAction_coordinates]
    push_cast
    ring
  simp_rw [← mul_assoc]
  rw [he]
  simp_rw [fderiv_hillL2CanonicalAction_complex_apply]
  rw [hD (hillL2SourceInclusion h),fderiv_hillL2Momentum_apply,
    WeightedCoeff.sobolevBilinearPairing_apply,
    WeightedCoeff.fourierRealZeroHilbertPairing_signed_zero_apply]
  apply tsum_congr
  intro k
  rw [hb,hillRealMeanZeroInclusion_apply,hillL2SourceInclusion_apply,hillL2SourceInclusion_apply]

theorem hillL2ActionEnergy_zero_eq_momentum : hillL2ActionEnergy 0=hillL2Momentum 0 := by
  rw [hillL2ActionEnergy_eq_pi_norm_sq,hillL2Momentum_eq_half_norm_sq,hillL2NativeMap_zero]
  simp

private theorem mem_hillL2_finiteGap_preimage (u : HillRealL2BanachSource) :
    u ∈ hillL2SourceInclusion ⁻¹' hillRealFiniteGapLocus ↔
      hillL2SourceInclusion u ∈ hillRealFiniteGapLocus :=
  Set.mem_preimage

theorem fderiv_hillL2ActionEnergy_eq_momentum (u : HillRealL2BanachSource) :
    fderiv ℝ hillL2ActionEnergy u=fderiv ℝ hillL2Momentum u := by
  exact WeightedCoeff.fourierRealZero_fderiv_eq_of_analytic_dense_fderiv_eq (Weight.signedSobolev 0)
    hillL2ActionEnergy hillL2Momentum (hillL2SourceInclusion ⁻¹' hillRealFiniteGapLocus)
    analyticAt_hillL2ActionEnergy analyticAt_hillL2Momentum dense_hillL2FiniteGapLocus
    (fun x hx => fderiv_hillL2ActionEnergy_eq_momentum_of_finiteGap x
      ((mem_hillL2_finiteGap_preimage x).mp hx)) u

/-- The actual positive-half action energy equals the original momentum
at EVERY genuine original L2 input, including infinite-gap inputs. -/
theorem hillL2ActionEnergy_eq_momentum : hillL2ActionEnergy=hillL2Momentum := by
  exact @WeightedCoeff.fourierRealZero_eq_of_analytic_dense_fderiv_eq (Weight.signedSobolev 0)
    hillL2ActionEnergy hillL2Momentum Set.univ
    analyticAt_hillL2ActionEnergy analyticAt_hillL2Momentum (by simp)
    (fun x _ => fderiv_hillL2ActionEnergy_eq_momentum x) 0 hillL2ActionEnergy_zero_eq_momentum

/-- Exact original period-one weighted canonical-action momentum trace. -/
theorem hasSum_hillL2CanonicalAction_momentum (u : HillRealL2BanachSource) :
    HasSum (fun n : ℕ+ => ((2*Real.pi*(n:ℕ):ℝ):ℂ)*hillL2CanonicalAction n u)
      (((1/2:ℝ)*‖u‖^2:ℝ):ℂ) := by
  rw [← hillL2Momentum_eq_half_norm_sq,← hillL2ActionEnergy_eq_momentum]
  exact hasSum_hillL2CanonicalAction_energy u

/-- The actual native L2 map preserves the exact KdV quadratic norm,
with the original period-one normalization. -/
theorem norm_sq_hillL2NativeMap (u : HillRealL2BanachSource) :
    ‖u‖^2=2*Real.pi*‖hillL2NativeMap u‖^2 := by
  have he := congrFun hillL2ActionEnergy_eq_momentum u
  rw [hillL2ActionEnergy_eq_pi_norm_sq,hillL2Momentum_eq_half_norm_sq] at he
  have hr := Complex.ofReal_injective he
  linarith

/-- The same identity in literal original unweighted Fourier L2 norm. -/
theorem norm_sq_hillL2SourceCoefficients (u : HillRealL2BanachSource) :
    ‖hillL2SourceCoefficients u‖^2=2*Real.pi*‖hillL2NativeMap u‖^2 := by
  rw [norm_hillL2SourceCoefficients]
  exact norm_sq_hillL2NativeMap u

end NLS.Articles.KdVPseudomeasures
