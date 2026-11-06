import NLS.KdV.HillCubicFrequencyKernel
import NLS.KdV.HillL2RealCutReflection
import NLS.ComplexAnalysis.UpperCircleReflection
import NLS.ComplexAnalysis.UpperArcReflectionIntegrability
import NLS.KdV.HillGlobalDifferentialReality

/-! # Actual cubic kernel on full circles and its genuine integrability -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ContDiff ComplexConjugate Interval
namespace NLS.KdV

theorem exists_hillL2CubicDirichletKernel_circle_error_bound
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0) :
    ∃ C : ℝ, 0<C ∧ ∃ K : ℕ, ∀ n : ℕ, K≤n →
      ∀ E∈sphere (0:ℂ) ((hillFreeBandFrequency n)^2),
        hillFreeBandFrequency n *
          ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) E^3*
            (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) E/
              hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) E)+
                E/2+Q (0 : AddCircle (2:ℝ))/4‖≤C := by
  let q := hillContinuousCoefficients Q
  let f : ℂ → ℂ := fun E => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^3*
    (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E/
      hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E)+E/2+Q (0 : AddCircle (2:ℝ))/4
  obtain ⟨C,hC,K,hbound⟩ := exists_hillL2CubicDirichletKernel_upper_arc_error_bound Q hq hr hf hp hmean
  refine ⟨C,hC,K,?_⟩
  intro n hn
  apply NLS.ComplexAnalysis.weighted_norm_bound_on_circle_of_upper_reflection f _ _ C
  · intro E hE hi
    have hnorm : ‖E‖=(hillFreeBandFrequency n)^2 := by
      simpa only [mem_sphere_iff_norm,sub_zero] using hE
    obtain ⟨t,ht⟩ := NLS.ComplexAnalysis.exists_upper_circleMap_parameter E _ hnorm hi
    have he : hillFreeUpperFrequency n t^2=E := (hillFreeUpperFrequency_sq n t).trans ht
    have h := hbound n hn t
    dsimp only at h
    rw [he] at h
    exact h
  · intro E hE
    dsimp only [f]
    rw [hillL2RealCutPrimitive_conj q hq hr E hE,
      hillL2RealCutRoot_conj q hq hr E hE,
      hillL2DirichletCharacteristic_conj_of_continuous Q hreal E]
    simp only [map_add,map_mul,map_div₀,map_pow,map_ofNat,
      Complex.conj_eq_iff_im.mpr (hreal (0 : AddCircle (2:ℝ)))]
    ring

theorem eventually_hillL2RealCutRoot_circle_ne_zero
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1) :
    ∀ᶠ M : ℕ in atTop, ∀ E∈sphere (0:ℂ) ((hillFreeBandFrequency M)^2),
      hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) E≠0 := by
  let q := hillContinuousCoefficients Q
  obtain ⟨c,C,hc,_hC,K,hbound⟩ := exists_hillL2RealCutRoot_wkb_comparison Q hq hr hf hp 1 le_rfl
  filter_upwards [eventually_ge_atTop K] with M hM E hE
  have hu (w : ℂ) (hw : w∈sphere (0:ℂ) ((hillFreeBandFrequency M)^2)) (hi : 0≤w.im) :
      hillL2RealCutRoot (SpectralWeight.one.toCoeff q) w≠0 := by
    have hnorm : ‖w‖=(hillFreeBandFrequency M)^2 := by
      simpa only [mem_sphere_iff_norm,sub_zero] using hw
    obtain ⟨t,ht⟩ := NLS.ComplexAnalysis.exists_upper_circleMap_parameter w _ hnorm hi
    have he : hillFreeUpperFrequency M t^2=w := (hillFreeUpperFrequency_sq M t).trans ht
    have h := (hbound M hM t).1
    rw [he] at h
    intro hz
    rw [hz,norm_zero,mul_zero] at h
    linarith
  by_cases hi : 0≤E.im
  · exact hu E hE hi
  have hconj : conj E∈sphere (0:ℂ) ((hillFreeBandFrequency M)^2) := by
    simpa only [mem_sphere_iff_norm,sub_zero,norm_conj] using hE
  have hn := hu (conj E) hconj (by simp only [conj_im];linarith)
  rw [hillL2RealCutRoot_conj q hq hr E (by linarith)] at hn
  intro hz
  exact hn (by rw [hz,map_zero,neg_zero])

/-- Genuine integrability of the actual cubic integrand follows from
upper-arc continuity, actual root nonvanishing and off-real reflection. -/
theorem circleIntegrable_hillL2CubicFrequencyIntegrand
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 1≤n) (r : ℝ) (hrp : 0<r)
    (hroot : ∀ E∈sphere (0:ℂ) r, hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E≠0) :
    CircleIntegrable (fun E => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^3*
      hillAbelianSelectedGlobalPsi q hq hr n hn E/hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E) 0 r := by
  apply NLS.ComplexAnalysis.circleIntegrable_of_continuous_upper_arc_reflection _ r hrp
  · have hF : ContinuousOn (fun t : ℝ => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)
        (circleMap 0 r t)) (Icc 0 Real.pi) := by
      apply (continuousOn_hillL2RealCutPrimitive_upper q hq hr).comp (continuous_circleMap 0 r).continuousOn
      intro t ht
      change 0≤(circleMap 0 r t).im
      rw [circleMap_zero_im]
      exact mul_nonneg hrp.le (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2)
    have hψ := (analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn).continuous.comp
      (continuous_circleMap 0 r)
    have hR : ContinuousOn (fun t : ℝ => hillL2RealCutRoot (SpectralWeight.one.toCoeff q)
        (circleMap 0 r t)) (Icc 0 Real.pi) :=
      continuousOn_const.mul (continuous_sinh.comp_continuousOn hF)
    exact ((hF.pow 3).mul hψ.continuousOn).div hR
      (fun t _ht => hroot _ (circleMap_mem_sphere 0 hrp.le t))
  · intro E hE
    have hz : E.im≠0 := ne_of_lt hE
    rw [hillL2RealCutPrimitive_conj q hq hr E hz,
      hillL2RealCutRoot_conj q hq hr E hz,
      hillAbelianSelectedGlobalPsi_conj q hq hr n hn E]
    simp only [map_div₀,map_mul,map_pow,map_neg,conj_conj]
    ring

theorem circleIntegrable_hillDirichletPolynomialIntegrand
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 1≤n) (q₀ : ℂ) (r : ℝ) (hrp : 0<r)
    (hD : ∀ E∈sphere (0:ℂ) r, hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E≠0) :
    CircleIntegrable (fun E => (-E/2-q₀/4)*
      (hillAbelianSelectedGlobalPsi q hq hr n hn E/hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E)) 0 r := by
  apply ContinuousOn.circleIntegrable hrp.le
  intro E hE
  have hP : AnalyticAt ℂ (fun E : ℂ => -E/2-q₀/4) E :=
    (analyticAt_id.neg.div_const).sub analyticAt_const
  exact (hP.mul (((analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn) E (mem_univ _)).div
    ((analyticOnNhd_hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) E (mem_univ _))
    (hD E hE))).continuousAt.continuousWithinAt

end NLS.KdV
