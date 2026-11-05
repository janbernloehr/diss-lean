import NLS.KdV.HillFreeOwnAmplitudeDifference
import NLS.KdV.HillFreeActionGapPrefactorValue

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The ENTIRE original regular correction has an analytic H-minus-one
germ at the free source, with its exact zero base value. -/
theorem exists_hillFree_fullRegularCorrection_hminus_germ (n : ℕ+) :
    ∃ Φ : PeriodOneHminusOne → ℂ, AnalyticAt ℂ Φ 0 ∧ Φ 0 = 0 ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
        Φ (hillOriginalHminusSource p.val) = hillSummedRegularAbelianCorrection p.val p.property.1 p.property.2 n n.pos := by
  let Q : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  have hgap : hillRealGapHalfLength 0 h0q h0r n = 0 := by
    obtain ⟨hl,hu⟩ := hillFreeGapEndpoints h0q h0r n n.pos
    rw [hillRealGapHalfLength,hl,hu,sub_self,zero_div]
  obtain ⟨C,hC,hCM⟩ := exists_hillOriginal_closedGap_regularCorrection_hminus_physical_germ Q n n hgap
  obtain ⟨B,hB,hBM⟩ := exists_hillOriginal_offIndexCorrection_hminus_physical_germ Q n
  let Φ : PeriodOneHminusOne → ℂ := fun p => C p+B p
  have hΦ : AnalyticAt ℂ Φ 0 := by simpa only [Φ,Pi.add_def,Q,map_zero] using hC.add hB
  have hM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 Q,
      Φ (hillOriginalHminusSource p.val) = hillSummedRegularAbelianCorrection p.val p.property.1 p.property.2 n n.pos := by
    filter_upwards [hCM,hBM] with p hpC hpB
    dsimp only [Φ]
    rw [hpC,hpB,hillOriginal_fullCorrection_eq_own_add_offIndex]
  refine ⟨Φ,hΦ,?_,hM⟩
  simpa only [Q,map_zero,hillSummedRegularAbelianCorrection_free h0q h0r n n.pos] using hM.self_of_nhds

/-- Construct BOTH COMPLETE ORIGINAL Cartesian germs at every free closed
gap, retaining all action, own-gap and full regular-phase factors. Their
difference differential is the exact antisymmetric Fourier functional. -/
theorem exists_hillFree_cartesian_pair_difference (n : ℕ+) :
    ∃ Z W : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ Z 0 ∧ AnalyticAt ℂ W 0 ∧ Z 0 = 0 ∧ W 0 = 0 ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
        Z (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos ∧
        W (hillOriginalHminusSource p.val) = conj (hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos)) ∧
      ∀ h : PeriodOneHminusOne,
        (fderiv ℂ Z 0) h-(fderiv ℂ W 0) h =
          hillActionGapPrefactor 0 h0q h0r n*(h.val n-h.val (-(n : ℤ))) := by
  obtain ⟨A,C,hA,hC,hA0,hC0,hM,hD⟩ := exists_hillFree_ownAmplitude_pair_difference h0q h0r n
  obtain ⟨Φ,hΦ,hΦ0,hΦM⟩ := exists_hillFree_fullRegularCorrection_hminus_germ h0q h0r n
  let F : PeriodOneHminusOne → ℂ := fun p => Complex.exp (I*Φ p)
  let G : PeriodOneHminusOne → ℂ := fun p => Complex.exp (-I*Φ p)
  have hF : AnalyticAt ℂ F 0 := (analyticAt_const.mul hΦ).cexp'
  have hG : AnalyticAt ℂ G 0 := (analyticAt_const.mul hΦ).cexp'
  have hF0 : F 0 = 1 := by simp only [F,hΦ0,mul_zero,Complex.exp_zero]
  have hG0 : G 0 = 1 := by simp only [G,hΦ0,mul_zero,Complex.exp_zero]
  let Z : PeriodOneHminusOne → ℂ := fun p => A p*F p
  let W : PeriodOneHminusOne → ℂ := fun p => C p*G p
  refine ⟨Z,W,hA.mul hF,hC.mul hG,?_,?_,?_,?_⟩
  · simp only [Z,hA0,zero_mul]
  · simp only [W,hC0,zero_mul]
  · filter_upwards [hM,hΦM] with p hp hpΦ
    constructor
    · dsimp only [Z,F]
      rw [hp.1,hpΦ,hillSpectralCartesian_eq_ownAmplitude_mul_correction]
    · have hreal : conj (hillSummedRegularAbelianCorrection p.val p.property.1 p.property.2 n n.pos) =
          hillSummedRegularAbelianCorrection p.val p.property.1 p.property.2 n n.pos :=
        Complex.conj_eq_iff_im.mpr (hillSummedRegularAbelianCorrection_im_eq_zero h0q h0r p.val p.property.1 p.property.2 n n.pos)
      dsimp only [W,G]
      rw [hp.2,hpΦ,hillSpectralCartesian_eq_ownAmplitude_mul_correction,map_mul,←Complex.exp_conj,map_mul,Complex.conj_I,hreal]
  · intro h
    have hDZ : fderiv ℂ Z 0 = fderiv ℂ A 0 := fderiv_mul_of_left_zero_right_one A F 0 hA hF hA0 hF0
    have hDW : fderiv ℂ W 0 = fderiv ℂ C 0 := fderiv_mul_of_left_zero_right_one C G 0 hC hG hC0 hG0
    rw [hDZ,hDW]
    exact hD h

/-- Physical matching determines the difference differential of ANY pair
of ORIGINAL full Cartesian/conjugate germs at zero. -/
theorem hillOriginalCartesian_free_difference_fderiv (n : ℕ+)
    (Z W : PeriodOneHminusOne → ℂ) (hZ : AnalyticAt ℂ Z 0) (hW : AnalyticAt ℂ W 0)
    (hZM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
      Z (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos)
    (hWM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
      W (hillOriginalHminusSource p.val) = conj (hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos))
    (h : PeriodOneHminusOne) :
    (fderiv ℂ Z 0) h-(fderiv ℂ W 0) h =
      hillActionGapPrefactor 0 h0q h0r n*(h.val n-h.val (-(n : ℤ))) := by
  obtain ⟨A,C,hA,hC,_,_,hM,hD⟩ := exists_hillFree_cartesian_pair_difference h0q h0r n
  have hEZ := hillHminusPhysicalGerm_fderiv_eq_of_eventuallyEq
    (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) Z A
    (by simpa only [map_zero] using hZ) (by simpa only [map_zero] using hA)
    (by filter_upwards [hZM,hM] with p hp hpr; exact hp.trans hpr.1.symm)
  have hEW := hillHminusPhysicalGerm_fderiv_eq_of_eventuallyEq
    (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) W C
    (by simpa only [map_zero] using hW) (by simpa only [map_zero] using hC)
    (by filter_upwards [hWM,hM] with p hp hpr; exact hp.trans hpr.2.symm)
  have hEZ0 : fderiv ℂ Z 0 = fderiv ℂ A 0 := by simpa only [map_zero] using hEZ
  have hEW0 : fderiv ℂ W 0 = fderiv ℂ C 0 := by simpa only [map_zero] using hEW
  rw [hEZ0,hEW0]
  exact hD h

end NLS.KdV
