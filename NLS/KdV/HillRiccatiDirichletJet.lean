import NLS.KdV.HillWKBDirichletComparison

/-! # Actual local Riccati jet of the Hill diagonal resolvent approximation -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.KdV

private theorem nlsRiccatiDensity_constant_lower_two (f : ℝ → ℂ) :
    nlsRiccatiDensity f (fun _ => 1) 2=f := by
  rw [show 2=0+2 from rfl,nlsRiccatiDensity_succ_succ]
  funext x
  simp [nlsRiccatiDensity_one,nlsRiccatiDensity_zero]

theorem hillRiccati_four_initial_polynomials (f : ℝ → ℂ) (w : ℂ) :
    nlsRiccatiApproximation (fun _ => -1) (-f) 4 w 0=
      f 0*w+nlsRiccatiDensity (fun _ => -1) (-f) 1 0*w^2+
        nlsRiccatiDensity (fun _ => -1) (-f) 2 0*w^3+
        nlsRiccatiDensity (fun _ => -1) (-f) 3 0*w^4 ∧
    nlsRiccatiApproximation f (fun _ => 1) 4 (-w) 0=
      w-f 0*w^3+nlsRiccatiDensity f (fun _ => 1) 3 0*w^4 := by
  simp only [nlsRiccatiApproximation,Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,
    zero_add,Nat.reduceAdd,pow_one,nlsRiccatiDensity_zero,Pi.neg_apply,neg_neg,
    nlsRiccatiDensity_one,nlsRiccatiDensity_constant_lower_two,deriv_const,neg_zero,zero_mul,add_zero]
  constructor
  · trivial
  · ring

private def riccatiLocalJetRemainder (A B C D E w : ℂ) : ℂ :=
  (B-E)+(C-3*A^2)*w+(D-3*A*B+A*E)*w^2+
    (B*E-3*A*C+2*A^3)*w^3+(C*E-3*A*D+2*A^2*B-2*A^2*E)*w^4+
    (D*E-2*A*B*E+2*A^2*C)*w^5+(-2*A*C*E+2*A^2*D)*w^6-2*A*D*E*w^7

private theorem riccati_local_jet_remainder (A B C D E w : ℂ)
    (hd : 1+(A*w+B*w^2+C*w^3+D*w^4)*(w-A*w^3+E*w^4)≠0) :
    -(w-A*w^3+E*w^4)/(1+(A*w+B*w^2+C*w^3+D*w^4)*(w-A*w^3+E*w^4))+w-2*A*w^3=
      w^4*riccatiLocalJetRemainder A B C D E w/
        (1+(A*w+B*w^2+C*w^3+D*w^4)*(w-A*w^3+E*w^4)) := by
  apply (eq_div_iff hd).mpr
  rw [sub_mul,add_mul,div_mul_cancel₀ _ hd]
  dsimp only [riccatiLocalJetRemainder]
  ring

theorem exists_hillRiccati_four_local_remainder_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) :
    ∃ R C : ℝ, 1≤R ∧ 0<C ∧ ∀ z : ℂ, R≤‖z‖ →
      let w := (2*I*z)⁻¹
      let r := nlsRiccatiApproximation (fun _ => -1) (-f) 4 w 0
      let s := nlsRiccatiApproximation f (fun _ => 1) 4 (-w) 0
      ‖z‖^4*‖-s/(1+r*s)+w-2*f 0*w^3‖≤C := by
  obtain ⟨R,hR,hbasis⟩ := exists_nlsWKB_initial_basis_small (fun _ => -1) (-f) contDiff_const hf.neg 4
  let A := f 0
  let B := nlsRiccatiDensity (fun _ => -1) (-f) 1 0
  let C := nlsRiccatiDensity (fun _ => -1) (-f) 2 0
  let D := nlsRiccatiDensity (fun _ => -1) (-f) 3 0
  let E := nlsRiccatiDensity f (fun _ => 1) 3 0
  have hcont : Continuous (riccatiLocalJetRemainder A B C D E) := by
    unfold riccatiLocalJetRemainder
    fun_prop
  obtain ⟨M,hM,hbound⟩ := ((isCompact_closedBall (0:ℂ) 1).image hcont).isBounded.exists_pos_norm_le
  refine ⟨R,2*M,hR,by positivity,?_⟩
  intro z hz
  let w := (2*I*z)⁻¹
  let r := nlsRiccatiApproximation (fun _ => -1) (-f) 4 w 0
  let s := nlsRiccatiApproximation f (fun _ => 1) 4 (-w) 0
  obtain ⟨_hℓ,_hu,hd,hi⟩ := hbasis z hz
  have he : (2*I*(-z))⁻¹=-w := by dsimp only [w];simp only [mul_neg,inv_neg]
  have hfun : -(-(fun x : ℝ => f x))=f := by simp
  have hone : (-(fun _ : ℝ => (-1:ℂ)))=(fun _ => (1:ℂ)) := by funext x;norm_num
  rw [he,hfun,hone] at hd hi
  change 1-(-I*r)*(-I*s)≠0 at hd
  change ‖(1-(-I*r)*(-I*s))⁻¹‖≤2 at hi
  have hden : 1-(-I*r)*(-I*s)=1+r*s := by ring_nf;simp only [I_sq];ring
  rw [hden] at hd hi
  have hpoly := hillRiccati_four_initial_polynomials f w
  have hrem : -s/(1+r*s)+w-2*f 0*w^3=w^4*riccatiLocalJetRemainder A B C D E w/(1+r*s) := by
    dsimp only [r,s]
    rw [hpoly.1,hpoly.2]
    exact riccati_local_jet_remainder A B C D E w (by simpa only [r,s,hpoly.1,hpoly.2] using hd)
  have hz1 : 1≤‖z‖ := hR.trans hz
  have hzpos : 0<‖z‖ := by linarith
  have hwnorm : ‖w‖=(2*‖z‖)⁻¹ := by dsimp only [w];simp
  have hw1 : ‖w‖≤1 := by rw [hwnorm];exact inv_le_one_of_one_le₀ (by linarith)
  have hH : ‖riccatiLocalJetRemainder A B C D E w‖≤M :=
    hbound _ ⟨w,by simpa only [mem_closedBall,dist_zero_right] using hw1,rfl⟩
  change ‖z‖^4*‖-s/(1+r*s)+w-2*f 0*w^3‖≤2*M
  rw [hrem,div_eq_mul_inv,norm_mul,norm_mul,norm_pow]
  have hwscale : ‖z‖^4*‖w‖^4≤1 := by rw [hwnorm];field_simp;nlinarith [pow_nonneg (norm_nonneg z) 4]
  calc
    _ = (‖z‖^4*‖w‖^4)*(‖riccatiLocalJetRemainder A B C D E w‖*‖(1+r*s)⁻¹‖) := by ring
    _ ≤ 1*(M*2) := mul_le_mul hwscale (mul_le_mul hH hi (norm_nonneg _) hM.le)
      (by positivity) (by norm_num)
    _ = _ := by ring

end NLS.KdV
