import NLS.KdV.HillMeanZeroAbelianDerivative
import NLS.SequenceSpaces.MeanZeroSobolevInclusion
import NLS.SequenceSpaces.SobolevHalfWeights

/-! # The same actual Fourier derivative at every native Sobolev order

The literal source and target weights differ by one half. Their ratio
is independent of regularity, so the normalized mean-zero derivative
is the SAME verified bounded Fourier equivalence at every real order.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- Exact native source/target normalization retains the original Fourier
constant, at every signed noncentral coordinate and every real order. -/
theorem fderiv_meanZeroSobolevAbelianMap_eq
    (s : ℝ) (g : WeightedCoeff (Weight.sobolev s) 2 → WeightedCoeff (Weight.sobolev (s+1/2)) 2)
    (hg : DifferentiableAt ℂ g 0)
    (hF : ∀ h : WeightedCoeff (Weight.sobolev s) 2, h.val 0=0 → ∀ j : ℤ,
      ((fderiv ℂ g 0) h).val j=(Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val j) :
    fderiv ℂ (WeightedCoeff.meanZeroWeightedMap (Weight.sobolev (s+1/2))
      (fun u => g ((WeightedCoeff.weightIsometry (Weight.sobolev s) 2).symm u))) 0=
        hillAbelianWeightedFourierEquiv.toContinuousLinearMap := by
  let v := Weight.sobolev s
  let w := Weight.sobolev (s+1/2)
  let J := (WeightedCoeff.weightIsometry v 2).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hgJ : HasFDerivAt g (fderiv ℂ g 0) (J 0) := by simpa only [map_zero] using hg.hasFDerivAt
  have hd := WeightedCoeff.hasFDerivAt_meanZeroWeightedMap w (fun u => g (J u))
    ((fderiv ℂ g 0).comp J) (hgJ.comp 0 J.hasFDerivAt)
  change fderiv ℂ (WeightedCoeff.meanZeroWeightedMap w (fun u => g (J u))) 0=_
  rw [hd.fderiv]
  ext h j
  by_cases hj : j=0
  · subst j
    have hz (a : DeletedCoeff 2 0) : a.val 0=0 := a.property
    exact (hz _).trans (hz _).symm
  · have hmean : (J h.val).val 0=0 := by
      change h.val 0/(v 0 : ℂ)=0
      have h0 : h.val 0=0 := h.property
      rw [h0,zero_div]
    change Coeff.deleteCoordinate 0 (WeightedCoeff.weightEquiv w 2 ((fderiv ℂ g 0) (J h.val))) j=_
    rw [Coeff.deleteCoordinate_apply_other 0 j hj,WeightedCoeff.weightEquiv_apply,hF _ hmean j]
    change (w j : ℂ)*((Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*(J h.val).val j)=
      (hillAbelianWeightedFourierEquiv h).val j
    rw [hillAbelianWeightedFourierEquiv_apply]
    change (w j : ℂ)*((Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*(h.val j/(v j : ℂ)))=_
    calc
      _ = ((w j : ℂ)/(v j : ℂ))*((Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val j) := by ring
      _ = _ := by rw [WeightedCoeff.sobolev_half_ratio,Weight.sobolev_half_apply,
        hillAbelianTargetWeight_one_sqrt]

/-- A genuine native analytic restriction inherits the exact raw Fourier
jet of the GIVEN weak map. Inclusion injectivity is used at the derivative,
with equality on a complex neighborhood, rather than real membership. -/
theorem sobolev_abelian_fourier_derivative_of_restriction
    (s : ℝ) (hs : -1≤s)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZ : DifferentiableAt ℂ Z 0)
    (hF : ∀ h : PeriodOneHminusOne, h.val 0=0 → ∀ j : ℤ,
      ((fderiv ℂ Z 0) h).val j=(Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val j)
    (g : WeightedCoeff (Weight.sobolev s) 2 → WeightedCoeff (Weight.sobolev (s+1/2)) 2)
    (hg : DifferentiableAt ℂ g 0)
    (he : ∀ᶠ p in 𝓝 (0 : WeightedCoeff (Weight.sobolev s) 2),
      WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤s+1/2) (g p)=
        Z (WeightedCoeff.sobolevInclusion hs p)) :
    ∀ h : WeightedCoeff (Weight.sobolev s) 2, h.val 0=0 → ∀ j : ℤ,
      ((fderiv ℂ g 0) h).val j=(Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val j := by
  let L := WeightedCoeff.sobolevInclusion (p := 2) hs
  let T := WeightedCoeff.sobolevInclusion (p := 2) (by linarith : (-1/2 : ℝ)≤s+1/2)
  have hZL : HasFDerivAt Z (fderiv ℂ Z 0) (L 0) := by simpa only [map_zero] using hZ.hasFDerivAt
  have he' : (fun p => T (g p)) =ᶠ[𝓝 (0 : WeightedCoeff (Weight.sobolev s) 2)] (fun p => Z (L p)) := he
  have hd : T.comp (fderiv ℂ g 0)=(fderiv ℂ Z 0).comp L :=
    ((T.hasFDerivAt.comp 0 hg.hasFDerivAt).congr_of_eventuallyEq he'.symm).unique
      (hZL.comp 0 L.hasFDerivAt)
  intro h hh j
  have H := congrArg (fun A => (A h).val j) hd
  simp only [ContinuousLinearMap.comp_apply,T,WeightedCoeff.sobolevInclusion_apply] at H
  exact H.trans (by simpa only [L,WeightedCoeff.sobolevInclusion_apply] using
    (hF (L h) (by simpa only [L,WeightedCoeff.sobolevInclusion_apply] using hh) j))

end NLS.KdV
