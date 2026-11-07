import NLS.Articles.KdVPseudomeasures.OriginalHillH1CanonicalPotential
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapMiura

/-! A genuine selected-action curve in the original H1 potential space.
Its actual native image changes only one coordinate pair, preserves
finite-gap membership, and differentiates the physical energy to the
actual normalized KdV frequency. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff NLS.FunctionalAnalysis
namespace NLS.Articles.KdVPseudomeasures

def hillH1ActionDirection (n : ℕ+) (z : RealSignedHilbert (signedStepOrder (1/2) 1)) :
    RealSignedHilbert (signedStepOrder (1/2) 1) :=
  hillH1ModeCLM n ((2*(starRingEnd ℂ) (z.val.val.val (n:ℤ)))⁻¹)

def hillH1ActionCurve (n : ℕ+) (q : RealSignedHilbert (signedStepOrder 0 1)) (t : ℝ) :
    RealSignedHilbert (signedStepOrder 0 1) :=
  (hillIntegerSobolevEquiv 1).equiv.symm
    ((hillIntegerSobolevEquiv 1).equiv q+t • hillH1ActionDirection n ((hillIntegerSobolevEquiv 1).equiv q))

theorem hillH1ActionCurve_zero (n : ℕ+) (q : RealSignedHilbert (signedStepOrder 0 1)) :
    hillH1ActionCurve n q 0=q := by
  simp only [hillH1ActionCurve,zero_smul,add_zero,Equiv.symm_apply_apply]

theorem analyticAt_hillH1ActionCurve (n : ℕ+) (q : RealSignedHilbert (signedStepOrder 0 1)) (t : ℝ) :
    AnalyticAt ℝ (hillH1ActionCurve n q) t := by
  exact ((hillIntegerSobolevEquiv 1).analytic_symm _).comp
    (analyticAt_const.add (analyticAt_id.smul analyticAt_const))

theorem hillH1ActionCurve_native_image (n : ℕ+) (q : RealSignedHilbert (signedStepOrder 0 1)) (t : ℝ) :
    (hillIntegerSobolevEquiv 1).equiv (hillH1ActionCurve n q t)=
      (hillIntegerSobolevEquiv 1).equiv q+t • hillH1ActionDirection n ((hillIntegerSobolevEquiv 1).equiv q) := by
  exact (hillIntegerSobolevEquiv 1).equiv.apply_symm_apply _

theorem hillIntegerSobolevEquiv_positive_eq_zero_iff_gapSquare
    (q : RealSignedHilbert (signedStepOrder 0 1)) (m : ℕ+) :
    ((hillIntegerSobolevEquiv 1).equiv q).val.val.val (m:ℤ)=0 ↔
      hillHminusCanonicalGapSquare m (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))=0 := by
  have h := hillRealSignedMap_positive_eq_zero_iff_gapSquare (hillIntegerSourceInclusion 1 q) m
  have he := congrArg (fun z : HillRealSignedTarget => z.val.val.val (m:ℤ)) (hillIntegerSobolevEquiv_inclusion 1 q)
  rw [hillIntegerTargetInclusion_apply] at he
  rw [he]
  exact h

theorem hillH1ActionCurve_finiteGap (n : ℕ+) (q : RealSignedHilbert (signedStepOrder 0 1))
    (hf : hillIntegerSourceInclusion 1 q ∈ hillRealFiniteGapLocus) (t : ℝ) :
    hillIntegerSourceInclusion 1 (hillH1ActionCurve n q t) ∈ hillRealFiniteGapLocus := by
  obtain ⟨N,hN⟩ := hf
  refine ⟨max N ((n:ℕ)+1),fun m hm => ?_⟩
  apply (hillIntegerSobolevEquiv_positive_eq_zero_iff_gapSquare _ m).mp
  rw [hillH1ActionCurve_native_image]
  have hmn : m ≠ n := by intro he; subst m; have := (le_max_right N ((n:ℕ)+1)).trans hm; omega
  have hpos : (0:ℤ)<(m:ℤ) := by exact_mod_cast m.pos
  have hnpos : (0:ℤ)<(n:ℤ) := by exact_mod_cast n.pos
  have hmnZ : (m:ℤ) ≠ (n:ℤ) := by
    intro he
    exact hmn (PNat.coe_injective (Int.ofNat_inj.mp he))
  have hbase := (hillIntegerSobolevEquiv_positive_eq_zero_iff_gapSquare q m).mpr
    (hN m ((le_max_left _ _).trans hm))
  change _+(t:ℂ)*(hillH1ActionDirection n ((hillIntegerSobolevEquiv 1).equiv q)).val.val.val (m:ℤ)=0
  rw [hillH1ActionDirection,hillH1ModeCLM_apply,if_neg hmnZ,if_neg (by omega : (m:ℤ)≠-(n:ℤ)),
    zero_add,mul_zero,add_zero,hbase]

theorem hasDerivAt_hillH1ActionCurve_energy (n : ℕ+) (q : RealSignedHilbert (signedStepOrder 0 1))
    (hg : hillHminusCanonicalGapSquare n (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))≠0) :
    HasDerivAt (fun t : ℝ => hillH1KdVHamiltonian (hillH1ActionCurve n q t))
      (hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q)) 0 := by
  let z := (hillIntegerSobolevEquiv 1).equiv q
  have hz : z.val.val.val (n:ℤ)≠0 := by
    intro he
    exact hg ((hillIntegerSobolevEquiv_positive_eq_zero_iff_gapSquare q n).mp he)
  have hstar : (starRingEnd ℂ) (z.val.val.val (n:ℤ))≠0 := by simpa using hz
  have hprod : (starRingEnd ℂ) (z.val.val.val (n:ℤ))*
      (2*(starRingEnd ℂ) (z.val.val.val (n:ℤ)))⁻¹=(1/2:ℂ) := by
    field_simp
  have hgrad : (fderiv ℝ hillH1CanonicalHamiltonian z) (hillH1ActionDirection n z)=hillH1KdVFrequency n z := by
    rw [hillH1ActionDirection,hillH1CanonicalHamiltonian_mode_gradient,hprod]
    norm_num
  have hd := @hasDerivAt_differentiable_real_line
    (RealSignedHilbert (signedStepOrder (1/2) 1)) inferInstance inferInstance
    hillH1CanonicalHamiltonian z (hillH1ActionDirection n z) 0
    (by simpa only [zero_smul,add_zero] using (analyticAt_hillH1CanonicalHamiltonian z).differentiableAt)
  simpa only [zero_smul,add_zero,hgrad] using! hd

end NLS.Articles.KdVPseudomeasures
