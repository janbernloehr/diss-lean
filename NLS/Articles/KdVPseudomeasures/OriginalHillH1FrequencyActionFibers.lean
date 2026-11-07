import NLS.Articles.KdVPseudomeasures.OriginalHillH1ModeFrequency
import NLS.SequenceSpaces.FourierRealModeVariation

/-! The actual continuous H1 KdV frequencies are constant on ENTIRE native
action fibers, including collapsed modes. Open modes use genuine radial
energy variations; collapsed modes follow by common mode opening and continuity. -/
noncomputable section
open Complex NLS.KdV NLS.WeightedCoeff NLS.FunctionalAnalysis
namespace NLS.Articles.KdVPseudomeasures

theorem hillH1_normSq_eq_of_products (n : ℕ+)
    (w z : RealSignedHilbert (signedStepOrder (1/2) 1))
    (hprod : ∀ m : ℕ+, w.val.val.val (m:ℤ)*w.val.val.val (-(m:ℤ))=
      z.val.val.val (m:ℤ)*z.val.val.val (-(m:ℤ))) :
    Complex.normSq (w.val.val.val (n:ℤ))=Complex.normSq (z.val.val.val (n:ℤ)) := by
  have h := hprod n
  rw [w.property (n:ℤ),z.property (n:ℤ),Complex.mul_conj,Complex.mul_conj] at h
  exact Complex.ofReal_inj.mp h

theorem hillH1CanonicalHamiltonian_common_radial_lines (n : ℕ+)
    (w z : RealSignedHilbert (signedStepOrder (1/2) 1))
    (hprod : ∀ m : ℕ+, w.val.val.val (m:ℤ)*w.val.val.val (-(m:ℤ))=
      z.val.val.val (m:ℤ)*z.val.val.val (-(m:ℤ))) (t : ℝ) :
    hillH1CanonicalHamiltonian (w+t • hillH1ModeCLM n (w.val.val.val (n:ℤ)))=
      hillH1CanonicalHamiltonian (z+t • hillH1ModeCLM n (z.val.val.val (n:ℤ))) := by
  have hbase : w.val.val.val (n:ℤ)*(starRingEnd ℂ) (w.val.val.val (n:ℤ))=
      z.val.val.val (n:ℤ)*(starRingEnd ℂ) (z.val.val.val (n:ℤ)) := by
    simpa only [w.property (n:ℤ),z.property (n:ℤ)] using hprod n
  apply hillH1CanonicalHamiltonian_eq_of_products
  apply fourierRealModeLine_products _ _ n w z _ _ t hprod
  simp only [map_add,map_mul,Complex.conj_ofReal]
  calc
    _ = (1+(t:ℂ))^2*(w.val.val.val (n:ℤ)*(starRingEnd ℂ) (w.val.val.val (n:ℤ))) := by ring
    _ = (1+(t:ℂ))^2*(z.val.val.val (n:ℤ)*(starRingEnd ℂ) (z.val.val.val (n:ℤ))) := by rw [hbase]
    _ = _ := by ring

theorem hillH1KdVFrequency_eq_of_products_of_mode_ne_zero (n : ℕ+)
    (w z : RealSignedHilbert (signedStepOrder (1/2) 1))
    (hprod : ∀ m : ℕ+, w.val.val.val (m:ℤ)*w.val.val.val (-(m:ℤ))=
      z.val.val.val (m:ℤ)*z.val.val.val (-(m:ℤ))) (hz : z.val.val.val (n:ℤ)≠0) :
    hillH1KdVFrequency n w=hillH1KdVFrequency n z := by
  have hd (a : RealSignedHilbert (signedStepOrder (1/2) 1)) :
      HasDerivAt (fun t : ℝ => hillH1CanonicalHamiltonian (a+t • hillH1ModeCLM n (a.val.val.val (n:ℤ))))
        ((fderiv ℝ hillH1CanonicalHamiltonian a) (hillH1ModeCLM n (a.val.val.val (n:ℤ)))) 0 := by
    simpa only [zero_smul,add_zero] using
      @hasDerivAt_differentiable_real_line (RealSignedHilbert (signedStepOrder (1/2) 1))
        inferInstance inferInstance hillH1CanonicalHamiltonian a (hillH1ModeCLM n (a.val.val.val (n:ℤ))) 0
        (by simpa only [zero_smul,add_zero] using (analyticAt_hillH1CanonicalHamiltonian a).differentiableAt)
  have he : (fun t : ℝ => hillH1CanonicalHamiltonian (w+t • hillH1ModeCLM n (w.val.val.val (n:ℤ))))=
      (fun t : ℝ => hillH1CanonicalHamiltonian (z+t • hillH1ModeCLM n (z.val.val.val (n:ℤ)))) :=
    funext (hillH1CanonicalHamiltonian_common_radial_lines n w z hprod)
  have hw := hd w
  rw [he] at hw
  have hv := hw.unique (hd z)
  rw [hillH1CanonicalHamiltonian_mode_gradient,hillH1CanonicalHamiltonian_mode_gradient,
    ← Complex.normSq_eq_conj_mul_self,← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re,Complex.ofReal_re,hillH1_normSq_eq_of_products n w z hprod] at hv
  exact mul_right_cancel₀ (mul_ne_zero (by norm_num : (2:ℝ)≠0) (ne_of_gt (Complex.normSq_pos.mpr hz))) hv

theorem hillH1KdVFrequency_eq_of_products (n : ℕ+)
    (w z : RealSignedHilbert (signedStepOrder (1/2) 1))
    (hprod : ∀ m : ℕ+, w.val.val.val (m:ℤ)*w.val.val.val (-(m:ℤ))=
      z.val.val.val (m:ℤ)*z.val.val.val (-(m:ℤ))) :
    hillH1KdVFrequency n w=hillH1KdVFrequency n z := by
  by_cases hz : z.val.val.val (n:ℤ)=0
  · have hw : w.val.val.val (n:ℤ)=0 := Complex.normSq_eq_zero.mp (by
      rw [hillH1_normSq_eq_of_products n w z hprod,hz,Complex.normSq_zero])
    let f := fun t : ℝ => hillH1KdVFrequency n (w+t • hillH1ModeCLM n 1)-
      hillH1KdVFrequency n (z+t • hillH1ModeCLM n 1)
    have hc : Continuous f :=
      ((continuous_hillH1KdVFrequency n).comp (by fun_prop)).sub
        ((continuous_hillH1KdVFrequency n).comp (by fun_prop))
    have hmul (t : ℝ) : t*f t=0 := by
      by_cases ht : t=0
      · rw [ht,zero_mul]
      · have hp : ∀ m : ℕ+,
            (w+t • hillH1ModeCLM n 1).val.val.val (m:ℤ)*(w+t • hillH1ModeCLM n 1).val.val.val (-(m:ℤ))=
            (z+t • hillH1ModeCLM n 1).val.val.val (m:ℤ)*(z+t • hillH1ModeCLM n 1).val.val.val (-(m:ℤ)) :=
          fourierRealModeLine_products _ _ n w z 1 1 t hprod (by rw [hw,hz])
        have hne : (z+t • hillH1ModeCLM n 1).val.val.val (n:ℤ)≠0 := by
          have hn : (n:ℤ)≠-(n:ℤ) := by
            have hnpos : (0:ℤ)<n := by exact_mod_cast n.pos
            omega
          change z.val.val.val (n:ℤ)+(t:ℂ)*(hillH1ModeCLM n 1).val.val.val (n:ℤ)≠0
          rw [hillH1ModeCLM_apply]
          simpa [hz,hn] using Complex.ofReal_ne_zero.mpr ht
        dsimp only [f]
        rw [hillH1KdVFrequency_eq_of_products_of_mode_ne_zero n _ _ hp hne,sub_self,mul_zero]
    have hzero := @continuous_eq_zero_of_coordinate_mul ℝ inferInstance inferInstance f
      (ContinuousLinearMap.id ℝ ℝ) 1 (by rfl) hc hmul 0
    simpa only [f,zero_smul,add_zero] using sub_eq_zero.mp hzero
  · exact hillH1KdVFrequency_eq_of_products_of_mode_ne_zero n w z hprod hz

/-- Original full Hill isospectrality makes each actual H1 KdV frequency
equal after the SAME canonical coordinate map. -/
theorem hillH1KdVFrequency_eq_of_original_isospectral (n : ℕ+)
    (p q : RealSignedHilbert (signedStepOrder 0 1))
    (hp : originalHillPotentialOfRealSource (hillIntegerSourceInclusion 1 p) ∈
      originalIsospectralSet (originalHillPotentialOfRealSource (hillIntegerSourceInclusion 1 q))) :
    hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv p)=
      hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q) := by
  have hd := (mem_originalIsospectralSet_iff_discriminant_eq _ _).mp hp
  have hn : hillRealDiscriminantData (hillIntegerSourceInclusion 1 p)=
      hillRealDiscriminantData (hillIntegerSourceInclusion 1 q) := by
    simpa only [← hillRealDiscriminantData_original,originalHillRealMeanZeroSource_ofRealSource] using hd
  have hprod := (hillRealDiscriminantData_eq_iff_native_products _ _).mp hn
  apply hillH1KdVFrequency_eq_of_products
  intro m
  simpa only [← hillIntegerSobolevEquiv_inclusion,hillIntegerTargetInclusion_apply] using hprod m

end NLS.Articles.KdVPseudomeasures
