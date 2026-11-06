import NLS.KdV.HillWKBLocalResolventModel
import NLS.KdV.HillWKBRootComparison
import NLS.KdV.HillRiccatiDirichletJet

/-! # Actual local diagonal Hill resolvent on upper energy arcs -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

private theorem norm_scaled_quotient_sub_le (D R T g : ℂ) (W e c A B : ℝ)
    (hW : 0≤W) (he : 0≤e) (hc : 0<c) (hg : ‖g‖≤1)
    (hD : W*e*‖D-g*T‖≤A) (hT : W*e*‖R-T‖≤B) (hR : c≤e*‖R‖) :
    W*‖D/R-g‖≤(A+B)/c := by
  have hRn : R≠0 := by intro h;rw [h,norm_zero,mul_zero] at hR;linarith
  have hid : (D/R-g)*R=(D-g*T)+g*(T-R) := by rw [sub_mul,div_mul_cancel₀ _ hRn];ring
  have hnorm : ‖D/R-g‖*‖R‖≤‖D-g*T‖+‖R-T‖ := by
    calc
      _ = ‖(D/R-g)*R‖ := (norm_mul _ _).symm
      _ ≤ ‖D-g*T‖+‖g‖*‖T-R‖ := by rw [hid];simpa only [norm_mul] using norm_add_le (D-g*T) (g*(T-R))
      _ ≤ _ := by rw [norm_sub_rev T R];exact add_le_add le_rfl ((mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans_eq (one_mul _))
  apply (le_div_iff₀ hc).mpr
  calc
    _ ≤ (W*‖D/R-g‖)*(e*‖R‖) := mul_le_mul_of_nonneg_left hR (by positivity)
    _ = (W*e)*(‖D/R-g‖*‖R‖) := by ring
    _ ≤ (W*e)*(‖D-g*T‖+‖R-T‖) := mul_le_mul_of_nonneg_left hnorm (mul_nonneg hW he)
    _ = W*e*‖D-g*T‖+W*e*‖R-T‖ := by ring
    _ ≤ _ := add_le_add hD hT

theorem exists_hillL2Dirichlet_div_root_wkb_error_bound
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (N : ℕ) (hN : 1≤N) :
    ∃ C : ℝ, 0<C ∧ ∃ K : ℕ, ∀ n : ℕ, K≤n → ∀ t : Icc (0:ℝ) Real.pi,
      let z := hillFreeUpperFrequency n t
      (hillFreeBandFrequency n)^N*
        ‖hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)/
          hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)-
            hillWKBLocalResolvent (fun x : ℝ => Q (x : AddCircle (2:ℝ))) N z‖≤C := by
  let f : ℝ → ℂ := fun x => Q (x : AddCircle (2:ℝ))
  obtain ⟨c,C₁,hc,hC₁,K₁,hroot⟩ := exists_hillL2RealCutRoot_wkb_comparison Q hq hr hf hp N hN
  obtain ⟨R₂,C₂,hR₂,hC₂,hdir⟩ := exists_hillL2Dirichlet_wkb_error_bound Q hf hp N
  obtain ⟨R₃,hR₃,hlocal⟩ := exists_hillWKBLocalResolvent_bound f hf N
  obtain ⟨K₂,hK₂⟩ := Filter.eventually_atTop.mp
    (tendsto_hillFreeBandFrequency.eventually_ge_atTop (max R₂ R₃))
  refine ⟨(C₁+C₂)/c,by positivity,max K₁ K₂,?_⟩
  intro n hn t
  let z := hillFreeUpperFrequency n t
  let r := hillFreeBandFrequency n
  let D := hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  let R := hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  let T := exp (nlsHamiltonianPhase (fun _ => -1) (-f) N z)-
    (exp (nlsHamiltonianPhase (fun _ => -1) (-f) N z))⁻¹
  let g := hillWKBLocalResolvent f N z
  have hz : ‖z‖=r := norm_hillFreeUpperFrequency n t
  have hy : 0≤z.im := hillFreeUpperFrequency_im_nonneg n t t.property
  have hrad := hK₂ n ((le_max_right _ _).trans hn)
  have hrpos : 0<r := hillFreeBandFrequency_pos n
  have hr₂ : R₂≤r := (le_max_left _ _).trans hrad
  have hr₃ : R₃≤r := (le_max_right _ _).trans hrad
  have hg : ‖g‖≤1 := hlocal z (by rw [hz];exact hr₃)
  obtain ⟨hRlower,hRerr⟩ := hroot n ((le_max_left _ _).trans hn) t
  change c≤Real.exp (-z.im)*‖R‖ at hRlower
  change r^N*Real.exp (-z.im)*‖R-T‖≤C₁ at hRerr
  have hDerr := hdir z (by rw [hz];exact hr₂)
  rw [hillWKBDirichletModel_eq_localResolvent_mul,abs_of_nonneg hy,hz] at hDerr
  change ‖D-g*T‖≤C₂/(2*r)^N*Real.exp z.im at hDerr
  have hDscaled : r^N*Real.exp (-z.im)*‖D-g*T‖≤C₂ := by
    have hpow : r^N≤(2*r)^N := pow_le_pow_left₀ hrpos.le (by linarith) N
    have he : Real.exp (-z.im)*Real.exp z.im=1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
    calc
      _ ≤ r^N*Real.exp (-z.im)*(C₂/(2*r)^N*Real.exp z.im) :=
        mul_le_mul_of_nonneg_left hDerr (by positivity)
      _ = (r^N*(C₂/(2*r)^N))*(Real.exp (-z.im)*Real.exp z.im) := by ring
      _ = r^N*C₂/(2*r)^N := by rw [he,mul_one];ring
      _ ≤ C₂ := (div_le_iff₀ (pow_pos (by positivity) N)).mpr (by nlinarith [mul_le_mul_of_nonneg_right hpow hC₂.le])
  have h := norm_scaled_quotient_sub_le D R T g (r^N) (Real.exp (-z.im)) c C₂ C₁
    (by positivity) (by positivity) hc hg hDscaled hRerr hRlower
  change r^N*‖D/R-g‖≤_
  simpa only [add_comm] using h

theorem exists_hillL2Dirichlet_div_root_local_cubic_error_bound
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1) :
    ∃ C : ℝ, 0<C ∧ ∃ K : ℕ, ∀ n : ℕ, K≤n → ∀ t : Icc (0:ℝ) Real.pi,
      let z := hillFreeUpperFrequency n t
      (hillFreeBandFrequency n)^4*
        ‖hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)/
          hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)-
            I/(2*z)-I*Q (0 : AddCircle (2:ℝ))/(4*z^3)‖≤C := by
  let f : ℝ → ℂ := fun x => Q (x : AddCircle (2:ℝ))
  obtain ⟨C₀,hC₀,K₀,hactual⟩ := exists_hillL2Dirichlet_div_root_wkb_error_bound Q hq hr hf hp 4 (by omega)
  obtain ⟨R,C₁,hR,hC₁,hjet⟩ := exists_hillRiccati_four_local_remainder_bound f hf
  obtain ⟨K₁,hK₁⟩ := Filter.eventually_atTop.mp (tendsto_hillFreeBandFrequency.eventually_ge_atTop R)
  refine ⟨C₀+C₁,by positivity,max K₀ K₁,?_⟩
  intro n hn t
  let z := hillFreeUpperFrequency n t
  let r := hillFreeBandFrequency n
  let D := hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  let T := hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  let g := hillWKBLocalResolvent f 4 z
  let w := (2*I*z)⁻¹
  have hz : ‖z‖=r := norm_hillFreeUpperFrequency n t
  have hz0 : z≠0 := norm_pos_iff.mp (by rw [hz];exact hillFreeBandFrequency_pos n)
  have ha := hactual n ((le_max_left _ _).trans hn) t
  change r^4*‖D/T-g‖≤C₀ at ha
  have hj := hjet z (by rw [hz];exact hK₁ n ((le_max_right _ _).trans hn))
  dsimp only at hj
  rw [hz] at hj
  have hew : (2*I*(-z))⁻¹=-w := by dsimp only [w];simp only [mul_neg,inv_neg]
  have hjg : r^4*‖g+w-2*f 0*w^3‖≤C₁ := by
    dsimp only [g,hillWKBLocalResolvent]
    rw [hew]
    exact hj
  have hmodel : -w+2*f 0*w^3=I/(2*z)+I*f 0/(4*z^3) := by
    dsimp only [w]
    field_simp [hz0]
    ring_nf
    simp only [I_sq,I_pow_four]
    ring
  have he : (D/T-g)+(g+w-2*f 0*w^3)=D/T-I/(2*z)-I*f 0/(4*z^3) := by
    linear_combination -hmodel
  change r^4*‖D/T-I/(2*z)-I*f 0/(4*z^3)‖≤_
  rw [← he]
  have hh := mul_le_mul_of_nonneg_left (norm_add_le (D/T-g) (g+w-2*f 0*w^3))
    (pow_nonneg (hillFreeBandFrequency_pos n).le 4)
  rw [mul_add] at hh
  exact hh.trans (add_le_add ha hjg)

end NLS.KdV
