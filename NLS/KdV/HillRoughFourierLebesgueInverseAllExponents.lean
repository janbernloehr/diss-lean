import NLS.KdV.HillRoughFourierLebesgueInverseAnalytic
import NLS.Articles.KdVKdV2Frequencies.GlobalRawSobolevDiffeomorphisms

/-! # Native inverse analyticity at EVERY finite Fourier-Lebesgue exponent

The proved Hilbert inverse covers p=2. For p>2 the actual native
derivative is bijective, and its local inverse equals the fixed inverse.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem fourierLebesgueEquiv_symm_two_analytic (D : GlobalRoughAbelianForwardData)
    (s : ℝ) (hs : -1/2≤s) :
    AnalyticOnNhd ℝ (D.fourierLebesgueEquiv s hs 2 (by simp) (by norm_num)).symm univ := by
  obtain ⟨e,_hea,heia,he⟩ := D.exists_global_raw_real_analytic_sobolev_diffeomorphism s (by linarith)
  have hmap : D.fourierLebesgueEquiv s hs 2 (by simp) (by norm_num)=e.toEquiv := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    apply Subtype.ext
    funext j
    change (D.fourierLebesgueForward s hs 2 (by simp) (by norm_num) a).val.val j=(e a).val.val j
    rw [D.fourierLebesgueForward_apply]
    have hsrc : fourierLebesgueSourceInclusion s hs 2 (by simp) (by norm_num) a.val=
        WeightedCoeff.sobolevInclusion (by linarith : -1≤s) a.val := by
      apply Subtype.ext
      funext k
      simp only [fourierLebesgueSourceInclusion_apply,WeightedCoeff.sobolevInclusion_apply]
    rw [hsrc]
    have hj := congrArg (fun z => z.val j) (he a)
    simpa only [WeightedCoeff.sobolevInclusion_apply] using hj.symm
  rw [hmap]
  exact heia

/-- Native real analyticity on the ENTIRE original target for EVERY
finite p>=2 and every s>=-1/2, with the same physical normalization. -/
theorem fourierLebesgueEquiv_symm_analytic (D : GlobalRoughAbelianForwardData)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    AnalyticOnNhd ℝ (D.fourierLebesgueEquiv s hs p hp h2p).symm univ := by
  rcases eq_or_lt_of_le h2p with he | hlt
  · subst p
    exact D.fourierLebesgueEquiv_symm_two_analytic s hs
  · obtain ⟨r,hr,hpr⟩ : ∃ r : ℝ, 0≤r ∧ p=ENNReal.ofReal r :=
      ⟨p.toReal,ENNReal.toReal_nonneg,(ENNReal.ofReal_toReal hp).symm⟩
    subst p
    have hr2 : 2<r := by
      have h := (ENNReal.toReal_lt_toReal (by norm_num) ENNReal.ofReal_ne_top).mpr hlt
      simpa only [ENNReal.toReal_ofNat,ENNReal.toReal_ofReal hr] using h
    exact D.fourierLebesgueEquiv_symm_analytic_of_two_lt s r hs hr2

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
