import NLS.KdV.HillCubicFrequencyKernel
import NLS.KdV.HillL2RealCutReflection
import NLS.ComplexAnalysis.UpperCircleReflection

/-! # Actual linear Hill kernel normalization on expanding circles -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ContDiff ComplexConjugate
namespace NLS.KdV

private theorem norm_linear_dirichlet_kernel_error_le (z F G : ℂ) (CF CG : ℝ)
    (hz : 1≤‖z‖) (hCF : 0≤CF)
    (hphase : ‖z‖^3*‖F+I*z‖≤CF) (hlocal : ‖z‖^3*‖G-I/(2*z)‖≤CG) :
    ‖z‖^2*‖F*G-1/2‖≤(1+CF)*CG+CF := by
  let r := ‖z‖
  let L := I/(2*z)
  have hr : 1≤r := hz
  have hrp : 0<r := by linarith
  have hz0 : z≠0 := norm_pos_iff.mp hrp
  have hδ : ‖F+I*z‖≤CF := by
    have hpow : 1≤r^3 := one_le_pow₀ hr
    nlinarith [mul_le_mul_of_nonneg_right hpow (norm_nonneg (F+I*z))]
  have hFnorm : ‖F‖≤(1+CF)*r := by
    have he : F=(-I*z)+(F+I*z) := by ring
    have hn := norm_add_le (-I*z) (F+I*z)
    rw [← he] at hn
    simp only [norm_mul,norm_neg,norm_I,one_mul] at hn
    nlinarith
  have hL : ‖L‖=1/(2*r) := by
    dsimp only [L,r]
    simp only [norm_div,norm_I,norm_mul,norm_ofNat]
  have hmodel : (-I*z)*L=(1/2:ℂ) := by
    dsimp only [L]
    field_simp [hz0]
    ring_nf
    simp [I_sq]
  have he : F*G-1/2=F*(G-L)+(F+I*z)*L := by linear_combination hmodel
  have h1 : r^2*‖F*(G-L)‖≤(1+CF)*CG := by
    rw [norm_mul]
    calc
      _ ≤ r^2*((1+CF)*r*‖G-L‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hFnorm (norm_nonneg _)) (sq_nonneg r)
      _ = (1+CF)*(r^3*‖G-L‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlocal (by positivity)
  have hδr : r*‖F+I*z‖≤CF := by
    have hp : r≤r^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg r)]
    exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans hphase
  have h2 : r^2*‖(F+I*z)*L‖≤CF := by
    rw [norm_mul,hL]
    calc
      _ = (r*‖F+I*z‖)/2 := by field_simp
      _ ≤ CF := by linarith
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (norm_add_le (F*(G-L)) ((F+I*z)*L)) (sq_nonneg r)
  rw [mul_add] at hh
  exact hh.trans (add_le_add h1 h2)

theorem exists_hillL2LinearDirichletKernel_upper_arc_error_bound
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0) :
    ∃ C : ℝ, 0<C ∧ ∃ K : ℕ, ∀ n : ℕ, K≤n → ∀ t : Icc (0:ℝ) Real.pi,
      let z := hillFreeUpperFrequency n t
      (hillFreeBandFrequency n)^2*
        ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)*
          (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)/
            hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2))-1/2‖≤C := by
  obtain ⟨CF,hCF,KF,hphase⟩ := exists_hillL2RealCutPrimitive_upper_arc_cubic_decay Q hq hr hf hp hmean
  obtain ⟨CG,hCG,KG,hlocal⟩ := exists_hillL2Dirichlet_div_root_local_cubic_error_bound Q hq hr hf hp
  obtain ⟨K₁,hK₁⟩ := eventually_atTop.mp (tendsto_hillFreeBandFrequency.eventually_ge_atTop 1)
  let q₀ := Q (0:AddCircle (2:ℝ))
  refine ⟨(1+CF)*(CG+‖q₀‖/4)+CF+1,by positivity,max (max KF KG) K₁,?_⟩
  intro n hn t
  let z := hillFreeUpperFrequency n t
  let r := hillFreeBandFrequency n
  let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  let G := hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)/
    hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  have hz : ‖z‖=r := norm_hillFreeUpperFrequency n t
  have hr1 : 1≤r := hK₁ n ((le_max_right _ _).trans hn)
  have hrp : 0<r := hillFreeBandFrequency_pos n
  have hF := hphase n ((le_max_left _ _).trans ((le_max_left _ _).trans hn)) t
  have hG := hlocal n ((le_max_right _ _).trans ((le_max_left _ _).trans hn)) t
  change r^3*‖F+I*z‖≤CF at hF
  change r^4*‖G-I/(2*z)-I*q₀/(4*z^3)‖≤CG at hG
  have hpow : r^3≤r^4 := by
    calc
      _ ≤ r^3*r := le_mul_of_one_le_right (by positivity) hr1
      _ = _ := by ring
  have hε : r^3*‖G-I/(2*z)-I*q₀/(4*z^3)‖≤CG :=
    (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans hG
  have hterm : r^3*‖I*q₀/(4*z^3)‖=‖q₀‖/4 := by
    rw [norm_div,norm_mul,norm_mul,norm_pow,norm_I,one_mul,norm_ofNat,hz]
    field_simp
  have hg3 : r^3*‖G-I/(2*z)‖≤CG+‖q₀‖/4 := by
    have he : G-I/(2*z)=(G-I/(2*z)-I*q₀/(4*z^3))+I*q₀/(4*z^3) := by ring
    have hh := mul_le_mul_of_nonneg_left
      (norm_add_le (G-I/(2*z)-I*q₀/(4*z^3)) (I*q₀/(4*z^3))) (pow_nonneg hrp.le 3)
    rw [← he,mul_add,hterm] at hh
    linarith
  have hh := norm_linear_dirichlet_kernel_error_le z F G CF (CG+‖q₀‖/4)
    (by rw [hz];exact hr1) hCF.le (by simpa only [hz] using hF) (by simpa only [hz] using hg3)
  rw [hz] at hh
  exact hh.trans (by linarith)

theorem exists_hillL2LinearDirichletKernel_circle_error_bound
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0) :
    ∃ C : ℝ, 0<C ∧ ∃ K : ℕ, ∀ n : ℕ, K≤n →
      ∀ E∈sphere (0:ℂ) ((hillFreeBandFrequency n)^2),
        (hillFreeBandFrequency n)^2*
          ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) E*
            (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) E/
              hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) E)-1/2‖≤C := by
  let q := hillContinuousCoefficients Q
  let f : ℂ → ℂ := fun E => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E*
    (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E/
      hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E)-1/2
  obtain ⟨C,hC,K,hbound⟩ := exists_hillL2LinearDirichletKernel_upper_arc_error_bound Q hq hr hf hp hmean
  refine ⟨C,hC,K,?_⟩
  intro n hn
  apply weighted_norm_bound_on_circle_of_upper_reflection f _ _ C
  · intro E hE hi
    have hnorm : ‖E‖=(hillFreeBandFrequency n)^2 := by simpa only [mem_sphere_iff_norm,sub_zero] using hE
    obtain ⟨t,ht⟩ := exists_upper_circleMap_parameter E _ hnorm hi
    have he : hillFreeUpperFrequency n t^2=E := (hillFreeUpperFrequency_sq n t).trans ht
    have h := hbound n hn t
    dsimp only at h
    rw [he] at h
    exact h
  · intro E hE
    dsimp only [f]
    rw [hillL2RealCutPrimitive_conj q hq hr E hE,hillL2RealCutRoot_conj q hq hr E hE,
      hillL2DirichletCharacteristic_conj_of_continuous Q hreal E]
    simp only [map_sub,map_mul,map_div₀,map_one,map_ofNat]
    ring

end NLS.KdV
