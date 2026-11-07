import NLS.Articles.KdVPseudomeasures.OriginalHillH1ActionCurve

/-! Actual strong inverse curves changing one canonical coordinate pair.
They preserve finite-gap membership and open a collapsed selected mode. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

def hillH1ModeCurve (n : ℕ+) (c : ℂ)
    (q : RealSignedHilbert (signedStepOrder 0 1)) (t : ℝ) :
    RealSignedHilbert (signedStepOrder 0 1) :=
  (hillIntegerSobolevEquiv 1).equiv.symm
    ((hillIntegerSobolevEquiv 1).equiv q+t • hillH1ModeCLM n c)

theorem hillH1ModeCurve_zero (n : ℕ+) (c : ℂ)
    (q : RealSignedHilbert (signedStepOrder 0 1)) :
    hillH1ModeCurve n c q 0=q := by
  simp only [hillH1ModeCurve,zero_smul,add_zero,Equiv.symm_apply_apply]

theorem analyticAt_hillH1ModeCurve (n : ℕ+) (c : ℂ)
    (q : RealSignedHilbert (signedStepOrder 0 1)) (t : ℝ) :
    AnalyticAt ℝ (hillH1ModeCurve n c q) t := by
  exact ((hillIntegerSobolevEquiv 1).analytic_symm _).comp
    (analyticAt_const.add (analyticAt_id.smul analyticAt_const))

theorem hillH1ModeCurve_native_image (n : ℕ+) (c : ℂ)
    (q : RealSignedHilbert (signedStepOrder 0 1)) (t : ℝ) :
    (hillIntegerSobolevEquiv 1).equiv (hillH1ModeCurve n c q t)=
      (hillIntegerSobolevEquiv 1).equiv q+t • hillH1ModeCLM n c :=
  (hillIntegerSobolevEquiv 1).equiv.apply_symm_apply _

theorem hillH1ModeCurve_finiteGap (n : ℕ+) (c : ℂ)
    (q : RealSignedHilbert (signedStepOrder 0 1))
    (hf : hillIntegerSourceInclusion 1 q ∈ hillRealFiniteGapLocus) (t : ℝ) :
    hillIntegerSourceInclusion 1 (hillH1ModeCurve n c q t) ∈ hillRealFiniteGapLocus := by
  obtain ⟨N,hN⟩ := hf
  refine ⟨max N ((n:ℕ)+1),fun m hm => ?_⟩
  apply (hillIntegerSobolevEquiv_positive_eq_zero_iff_gapSquare _ m).mp
  rw [hillH1ModeCurve_native_image]
  have hmn : m ≠ n := by intro he; subst m; have := (le_max_right N ((n:ℕ)+1)).trans hm; omega
  have hpos : (0:ℤ)<(m:ℤ) := by exact_mod_cast m.pos
  have hnpos : (0:ℤ)<(n:ℤ) := by exact_mod_cast n.pos
  have hmnZ : (m:ℤ) ≠ (n:ℤ) := by
    intro he
    exact hmn (PNat.coe_injective (Int.ofNat_inj.mp he))
  have hbase := (hillIntegerSobolevEquiv_positive_eq_zero_iff_gapSquare q m).mpr
    (hN m ((le_max_left _ _).trans hm))
  change _+(t:ℂ)*(hillH1ModeCLM n c).val.val.val (m:ℤ)=0
  rw [hillH1ModeCLM_apply,if_neg hmnZ,if_neg (by omega : (m:ℤ)≠-(n:ℤ)),
    zero_add,mul_zero,add_zero,hbase]

theorem hillH1ModeCurve_opens_closed_gap (n : ℕ+)
    (q : RealSignedHilbert (signedStepOrder 0 1))
    (hg : hillHminusCanonicalGapSquare n
      (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))=0)
    {t : ℝ} (ht : t≠0) :
    hillHminusCanonicalGapSquare n
      (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillH1ModeCurve n 1 q t)))≠0 := by
  intro he
  have hz := (hillIntegerSobolevEquiv_positive_eq_zero_iff_gapSquare _ n).mpr he
  have hb := (hillIntegerSobolevEquiv_positive_eq_zero_iff_gapSquare q n).mpr hg
  rw [hillH1ModeCurve_native_image] at hz
  change _+(t:ℂ)*(hillH1ModeCLM n 1).val.val.val (n:ℤ)=0 at hz
  have hnpos : (0:ℤ)<(n:ℤ) := by exact_mod_cast n.pos
  rw [hillH1ModeCLM_apply,if_pos rfl,if_neg (by omega : (n:ℤ)≠-(n:ℤ)),
    add_zero,hb,zero_add,mul_one] at hz
  exact ht (Complex.ofReal_eq_zero.mp hz)

end NLS.Articles.KdVPseudomeasures
