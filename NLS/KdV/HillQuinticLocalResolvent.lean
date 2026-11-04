import NLS.KdV.HillLocalDiagonalResolvent
/-! # Quintic local expansion of the actual Hill diagonal resolvent -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.KdV

private theorem hillRiccati_partner_two (f : ℝ → ℂ) :
    nlsRiccatiDensity f (fun _ => 1) 2=f := by
  rw [nlsRiccatiDensity_two]
  funext x
  simp

theorem hillRiccati_partner_three (f : ℝ → ℂ) :
    nlsRiccatiDensity f (fun _ => 1) 3 = deriv f := by
  rw [show 3=1+2 from rfl,nlsRiccatiDensity_succ_succ]
  rw [hillRiccati_partner_two]
  ext x
  simp [Finset.Nat.antidiagonal_succ]

theorem hillRiccati_partner_four (f : ℝ → ℂ) :
    nlsRiccatiDensity f (fun _ => 1) 4 = deriv (deriv f)-2*f^2 := by
  rw [show 4=2+2 from rfl,nlsRiccatiDensity_succ_succ,hillRiccati_partner_three]
  ext x
  simp [Finset.Nat.antidiagonal_succ]
  ring

theorem hillRiccati_six_initial_polynomials (f : ℝ → ℂ) (w : ℂ) :
    nlsRiccatiApproximation (fun _ => -1) (-f) 6 w 0=
      f 0*w+deriv f 0*w^2+(deriv (deriv f) 0-f 0^2)*w^3+
      nlsRiccatiDensity (fun _ => -1) (-f) 3 0*w^4+
      nlsRiccatiDensity (fun _ => -1) (-f) 4 0*w^5+
      nlsRiccatiDensity (fun _ => -1) (-f) 5 0*w^6 ∧
    nlsRiccatiApproximation f (fun _ => 1) 6 (-w) 0=
      w-f 0*w^3+deriv f 0*w^4+(2*f 0^2-deriv (deriv f) 0)*w^5+
      nlsRiccatiDensity f (fun _ => 1) 5 0*w^6 := by
  have hneg : deriv (-f)=-deriv f := by funext x;exact deriv.neg
  have hone : deriv (fun _ : ℝ => (1:ℂ))=0 := by funext x;exact deriv_const x 1
  simp only [nlsRiccatiApproximation,Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,
    zero_add,Nat.reduceAdd,pow_one,nlsRiccatiDensity_zero,Pi.neg_apply,neg_neg,
    nlsRiccatiDensity_one,nlsRiccatiDensity_two,hillRiccati_partner_three,
    hillRiccati_partner_four,neg_zero,zero_mul,add_zero,
    Pi.add_apply,Pi.mul_apply,Pi.pow_apply,Pi.sub_apply,Pi.ofNat_apply,hneg,hone,deriv.neg,deriv_zero]
  constructor <;> ring

private def riccatiSixRemainder (A B C D E w : ℂ) : ℂ :=
  (-2*A*B)*w^0+
    (7*A^3 - 6*A*C + B^2)*w^1+
    (B*(5*A^2 - 2*C))*w^2+
    (-6*A^4 + 11*A^2*C - 2*A*B^2 - 3*C^2)*w^3+
    (-2*A^3*B)*w^4+
    (2*(2*A^5 - 6*A^3*C + 2*A^2*B^2 + 3*A*C^2 - B^2*C))*w^5+
    (2*A^2*B*(2*A^2 - C))*w^6+
    (2*C*(A^2 - C)*(2*A^2 - C))*w^7 +
    (1-2*A*w^2-(2*C-4*A^2)*w^4)*D*(1-A*w^2+B*w^3+(A^2-C)*w^4) +
    (w-2*A*w^3-(2*C-4*A^2)*w^5)*(A*w+B*w^2+C*w^3+w^4*D)*E-E

private theorem riccati_six_local_remainder (A B C D E w : ℂ)
    (hd : 1+(A*w+B*w^2+C*w^3+w^4*D)*
      (w-A*w^3+B*w^4+(A^2-C)*w^5+w^6*E)≠0) :
    -(w-A*w^3+B*w^4+(A^2-C)*w^5+w^6*E)/
      (1+(A*w+B*w^2+C*w^3+w^4*D)*(w-A*w^3+B*w^4+(A^2-C)*w^5+w^6*E))
      +w-2*A*w^3-(2*C-4*A^2)*w^5 =
    w^6*riccatiSixRemainder A B C D E w/
      (1+(A*w+B*w^2+C*w^3+w^4*D)*(w-A*w^3+B*w^4+(A^2-C)*w^5+w^6*E)) := by
  apply (eq_div_iff hd).mpr
  rw [sub_mul,sub_mul,add_mul,div_mul_cancel₀ _ hd]
  dsimp only [riccatiSixRemainder]
  ring

theorem exists_hillRiccati_six_local_remainder_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) :
    ∃ R C : ℝ, 1≤R ∧ 0<C ∧ ∀ z : ℂ, R≤‖z‖ →
      let w := (2*I*z)⁻¹
      let r := nlsRiccatiApproximation (fun _ => -1) (-f) 6 w 0
      let s := nlsRiccatiApproximation f (fun _ => 1) 6 (-w) 0
      ‖z‖^6*‖-s/(1+r*s)+w-2*f 0*w^3-(2*deriv (deriv f) 0-6*f 0^2)*w^5‖≤C := by
  obtain ⟨R,hR,hbasis⟩ := exists_nlsWKB_initial_basis_small (fun _ => -1) (-f) contDiff_const hf.neg 6
  let A := f 0
  let B := deriv f 0
  let C := deriv (deriv f) 0-f 0^2
  let D : ℂ → ℂ := fun w => nlsRiccatiDensity (fun _ => -1) (-f) 3 0+
    nlsRiccatiDensity (fun _ => -1) (-f) 4 0*w+
    nlsRiccatiDensity (fun _ => -1) (-f) 5 0*w^2
  let E := nlsRiccatiDensity f (fun _ => 1) 5 0
  have hcont : Continuous (fun w => riccatiSixRemainder A B C (D w) E w) := by
    unfold riccatiSixRemainder D
    fun_prop
  obtain ⟨M,hM,hbound⟩ := ((isCompact_closedBall (0:ℂ) 1).image hcont).isBounded.exists_pos_norm_le
  refine ⟨R,2*M,hR,by positivity,?_⟩
  intro z hz
  let w := (2*I*z)⁻¹
  let r := nlsRiccatiApproximation (fun _ => -1) (-f) 6 w 0
  let s := nlsRiccatiApproximation f (fun _ => 1) 6 (-w) 0
  obtain ⟨_hℓ,_hu,hd,hi⟩ := hbasis z hz
  have he : (2*I*(-z))⁻¹=-w := by dsimp only [w];simp only [mul_neg,inv_neg]
  have hfun : -(-(fun x : ℝ => f x))=f := by simp
  have hone : (-(fun _ : ℝ => (-1:ℂ)))=(fun _ => (1:ℂ)) := by funext x;norm_num
  rw [he,hfun,hone] at hd hi
  change 1-(-I*r)*(-I*s)≠0 at hd
  change ‖(1-(-I*r)*(-I*s))⁻¹‖≤2 at hi
  have hden : 1-(-I*r)*(-I*s)=1+r*s := by ring_nf;simp only [I_sq];ring
  rw [hden] at hd hi
  have hpoly := hillRiccati_six_initial_polynomials f w
  have hRp : r=A*w+B*w^2+C*w^3+w^4*D w := by
    dsimp only [r]
    rw [hpoly.1]
    dsimp only [A,B,C,D]
    ring
  have hS : s=w-A*w^3+B*w^4+(A^2-C)*w^5+w^6*E := by
    dsimp only [s]
    rw [hpoly.2]
    dsimp only [A,B,C,E]
    ring
  have hrem : -s/(1+r*s)+w-2*f 0*w^3-(2*deriv (deriv f) 0-6*f 0^2)*w^5=
      w^6*riccatiSixRemainder A B C (D w) E w/(1+r*s) := by
    rw [hRp,hS]
    convert riccati_six_local_remainder A B C (D w) E w
      (by simpa only [←hRp,←hS] using hd) using 1
    dsimp only [A,C]
    ring
  have hz1 : 1≤‖z‖ := hR.trans hz
  have hzpos : 0<‖z‖ := by linarith
  have hwnorm : ‖w‖=(2*‖z‖)⁻¹ := by dsimp only [w];simp
  have hw1 : ‖w‖≤1 := by rw [hwnorm];exact inv_le_one_of_one_le₀ (by linarith)
  have hH : ‖riccatiSixRemainder A B C (D w) E w‖≤M :=
    hbound _ ⟨w,by simpa only [mem_closedBall,dist_zero_right] using hw1,rfl⟩
  change ‖z‖^6*‖-s/(1+r*s)+w-2*f 0*w^3-(2*deriv (deriv f) 0-6*f 0^2)*w^5‖≤2*M
  rw [hrem,div_eq_mul_inv,norm_mul,norm_mul,norm_pow]
  have hwscale : ‖z‖^6*‖w‖^6≤1 := by rw [hwnorm];field_simp;nlinarith [pow_nonneg (norm_nonneg z) 6]
  calc
    _ = (‖z‖^6*‖w‖^6)*(‖riccatiSixRemainder A B C (D w) E w‖*‖(1+r*s)⁻¹‖) := by ring
    _ ≤ 1*(M*2) := mul_le_mul hwscale (mul_le_mul hH hi (norm_nonneg _) hM.le)
      (by positivity) (by norm_num)
    _ = _ := by ring

theorem exists_hillL2Dirichlet_div_root_local_quintic_error_bound
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1) :
    ∃ C : ℝ, 0<C ∧ ∃ K : ℕ, ∀ n : ℕ, K≤n → ∀ t : Icc (0:ℝ) Real.pi,
      let z := hillFreeUpperFrequency n t
      (hillFreeBandFrequency n)^6*
        ‖hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)/
          hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)-
            I/(2*z)-I*Q (0 : AddCircle (2:ℝ))/(4*z^3)-
            I*(3*Q (0 : AddCircle (2:ℝ))^2-deriv (deriv (fun x : ℝ => Q (x : AddCircle (2:ℝ)) )) 0)/(16*z^5)‖≤C := by
  let f : ℝ → ℂ := fun x => Q (x : AddCircle (2:ℝ))
  obtain ⟨C₀,hC₀,K₀,hactual⟩ := exists_hillL2Dirichlet_div_root_wkb_error_bound Q hq hr hf hp 6 (by omega)
  obtain ⟨R,C₁,hR,hC₁,hjet⟩ := exists_hillRiccati_six_local_remainder_bound f hf
  obtain ⟨K₁,hK₁⟩ := Filter.eventually_atTop.mp (tendsto_hillFreeBandFrequency.eventually_ge_atTop R)
  refine ⟨C₀+C₁,by positivity,max K₀ K₁,?_⟩
  intro n hn t
  let z := hillFreeUpperFrequency n t
  let r := hillFreeBandFrequency n
  let D := hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  let T := hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  let g := hillWKBLocalResolvent f 6 z
  let w := (2*I*z)⁻¹
  have hz : ‖z‖=r := norm_hillFreeUpperFrequency n t
  have hz0 : z≠0 := norm_pos_iff.mp (by rw [hz];exact hillFreeBandFrequency_pos n)
  have ha := hactual n ((le_max_left _ _).trans hn) t
  change r^6*‖D/T-g‖≤C₀ at ha
  have hj := hjet z (by rw [hz];exact hK₁ n ((le_max_right _ _).trans hn))
  dsimp only at hj
  rw [hz] at hj
  have hew : (2*I*(-z))⁻¹=-w := by dsimp only [w];simp only [mul_neg,inv_neg]
  have hjg : r^6*‖g+w-2*f 0*w^3-(2*deriv (deriv f) 0-6*f 0^2)*w^5‖≤C₁ := by
    dsimp only [g,hillWKBLocalResolvent]
    rw [hew]
    exact hj
  have hmodel : -w+2*f 0*w^3+(2*deriv (deriv f) 0-6*f 0^2)*w^5=
      I/(2*z)+I*f 0/(4*z^3)+I*(3*f 0^2-deriv (deriv f) 0)/(16*z^5) := by
    dsimp only [w]
    field_simp [hz0]
    ring_nf
    simp only [show I^6=(-1:ℂ) by rw [show 6=2*3 from rfl,pow_mul,I_sq];norm_num,I_sq,I_pow_four]
    ring
  have he : (D/T-g)+(g+w-2*f 0*w^3-(2*deriv (deriv f) 0-6*f 0^2)*w^5)=D/T-I/(2*z)-I*f 0/(4*z^3)-I*(3*f 0^2-deriv (deriv f) 0)/(16*z^5) := by
    linear_combination -hmodel
  change r^6*‖D/T-I/(2*z)-I*f 0/(4*z^3)-I*(3*f 0^2-deriv (deriv f) 0)/(16*z^5)‖≤_
  rw [← he]
  have hh := mul_le_mul_of_nonneg_left (norm_add_le (D/T-g) (g+w-2*f 0*w^3-(2*deriv (deriv f) 0-6*f 0^2)*w^5))
    (pow_nonneg (hillFreeBandFrequency_pos n).le 6)
  rw [mul_add] at hh
  exact hh.trans (add_le_add ha hjg)

end NLS.KdV
