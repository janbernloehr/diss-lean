import NLS.KdV.HillWKBDirichletComparison
import NLS.KdV.HillL2UpperArcAsymptotics
import NLS.KdV.HillL2RealCutDifferential
import NLS.ComplexAnalysis.WeightedCoshInverse
import NLS.ComplexAnalysis.LaurentSquareRemainder

/-! # Actual Hill root separation and all-order WKB root comparison -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

theorem norm_sinh_increment_weighted_abs_le (a w : ℂ) (hw : ‖w‖≤1) :
    Real.exp (-|a.re|)*‖sinh (a+w)-sinh a‖≤2*‖w‖ := by
  by_cases ha : 0≤a.re
  · simpa only [abs_of_nonneg ha] using norm_sinh_increment_weighted_le a w ha hw
  · have h := norm_sinh_increment_weighted_le (-a) (-w) (by simpa using (not_le.mp ha).le)
      (by simpa only [norm_neg] using hw)
    have he : sinh (-a + -w)-sinh (-a)=-(sinh (a+w)-sinh a) := by
      rw [show -a + -w=-(a+w) by ring,sinh_neg,sinh_neg]
      ring
    rw [he,norm_neg] at h
    simpa only [neg_re,abs_of_neg (not_le.mp ha),neg_neg,norm_neg] using h

theorem norm_sinh_increment_le_exp_bound (a w : ℂ) (Y : ℝ)
    (ha : |a.re|≤Y) (hw : ‖w‖≤1) :
    ‖sinh (a+w)-sinh a‖≤2*Real.exp Y*‖w‖ := by
  have h := norm_sinh_increment_weighted_abs_le a w hw
  have he : Real.exp (-Y)≤Real.exp (-|a.re|) := Real.exp_le_exp.mpr (by linarith)
  have hb : Real.exp (-Y)*‖sinh (a+w)-sinh a‖≤2*‖w‖ :=
    (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans h
  have hh := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg Y)
  rw [← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul] at hh
  exact hh.trans_eq (by ring)

theorem exists_nlsHamiltonianPhase_weighted_correction_bound (a b : ℝ → ℂ) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ z : ℂ, 1≤‖z‖ →
      ‖z‖*‖nlsHamiltonianPhase a b N z+I*z‖≤C := by
  let C : ℝ := 1+∑ k ∈ Finset.range N, ‖classicalNLSHamiltonian a b (k+1)‖
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  intro z hz
  have he : nlsHamiltonianPhase a b N z+I*z=
      ∑ k ∈ Finset.range N, I*classicalNLSHamiltonian a b (k+1)/(2*z)^(k+1) := by
    unfold nlsHamiltonianPhase
    ring
  rw [he]
  calc
    _ ≤ ‖z‖*∑ k ∈ Finset.range N, ‖I*classicalNLSHamiltonian a b (k+1)/(2*z)^(k+1)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg z)
    _ = ∑ k ∈ Finset.range N, ‖z‖*‖I*classicalNLSHamiltonian a b (k+1)/(2*z)^(k+1)‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ k ∈ Finset.range N, ‖classicalNLSHamiltonian a b (k+1)‖ := by
      apply Finset.sum_le_sum
      intro k _hk
      have h2z : ‖(2:ℂ)*z‖=2*‖z‖ := by simp
      have h := norm_weighted_laurent_term_le (2*z) (I*classicalNLSHamiltonian a b (k+1))
        (by rw [h2z];linarith) 1 (k+1) (by omega)
      simp only [pow_one,h2z,norm_mul,norm_I,one_mul] at h
      nlinarith [norm_nonneg (I*classicalNLSHamiltonian a b (k+1)/(2*z)^(k+1))]
    _ ≤ C := by dsimp only [C];linarith

theorem exists_hillL2RealCutRoot_wkb_comparison
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (N : ℕ) (hN : 1≤N) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∃ K : ℕ, ∀ n : ℕ, K≤n → ∀ t : Icc (0:ℝ) Real.pi,
      let z := hillFreeUpperFrequency n t
      let S := nlsHamiltonianPhase (fun _ => -1) (fun x : ℝ => -Q (x : AddCircle (2:ℝ))) N z
      c≤Real.exp (-z.im)*‖hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)‖ ∧
      (hillFreeBandFrequency n)^N*Real.exp (-z.im)*
        ‖hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)-
          (exp S-(exp S)⁻¹)‖≤C := by
  obtain ⟨c,hc,hfree⟩ := exists_hillFreeUpperFrequency_sinh_lower_bound
  obtain ⟨D,hD,K₁,herror⟩ := exists_hillL2RealCutPrimitive_upper_arc_error_bound Q hq hr hf hp N hN
  obtain ⟨P,hP,hphase⟩ := exists_nlsHamiltonianPhase_weighted_correction_bound
    (fun _ => -1) (fun x : ℝ => -Q (x : AddCircle (2:ℝ))) N
  let ε := min 1 (c/4)
  have hε : 0<ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε≤1 := min_le_left _ _
  have hεc : ε≤c/4 := min_le_right _ _
  obtain ⟨K₂,hK₂⟩ := Filter.eventually_atTop.mp
    (tendsto_hillFreeBandFrequency.eventually_ge_atTop (max 1 ((D+P+1)/ε)))
  refine ⟨c,4*Real.exp 1*D,hc,by positivity,max K₁ K₂,?_⟩
  intro n hn t
  let z := hillFreeUpperFrequency n t
  let r := hillFreeBandFrequency n
  let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  let S := nlsHamiltonianPhase (fun _ => -1) (fun x : ℝ => -Q (x : AddCircle (2:ℝ))) N z
  have hz : ‖z‖=r := norm_hillFreeUpperFrequency n t
  have hy : 0≤z.im := hillFreeUpperFrequency_im_nonneg n t t.property
  have hrT := hK₂ n ((le_max_right _ _).trans hn)
  have hr1 : 1≤r := (le_max_left _ _).trans hrT
  have hrpos : 0<r := by linarith
  have hthreshold : D+P+1≤r*ε := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hrT)
  have hδ : ‖F-S‖≤D/(2*r)^N := herror n ((le_max_left _ _).trans hn) t
  have hδcross : ‖F-S‖*(2*r)^N≤D := (le_div_iff₀ (pow_pos (by positivity) N)).mp hδ
  have hrpow : r≤(2*r)^N := by
    calc
      r≤2*r := by linarith
      _ = (2*r)^1 := by rw [pow_one]
      _ ≤ (2*r)^N := pow_le_pow_right₀ (by linarith) hN
  have hδ1 : r*‖F-S‖≤D := by nlinarith [mul_le_mul_of_nonneg_left hrpow (norm_nonneg (F-S))]
  have hδN : r^N*‖F-S‖≤D := by
    have hh := pow_le_pow_left₀ (by positivity : 0≤r) (by linarith : r≤2*r) N
    nlinarith [mul_le_mul_of_nonneg_left hh (norm_nonneg (F-S))]
  have hS : r*‖S+I*z‖≤P := by simpa only [hz] using hphase z (by rw [hz];exact hr1)
  have hδsmall : ‖F-S‖≤ε := by nlinarith
  have hSsmall : ‖S+I*z‖≤ε := by nlinarith
  have hFsmall : ‖F+I*z‖≤ε := by
    have he : F+I*z=(F-S)+(S+I*z) := by ring
    have hh := mul_le_mul_of_nonneg_left (norm_add_le (F-S) (S+I*z)) hrpos.le
    rw [← he,mul_add] at hh
    nlinarith
  have hsin := norm_sinh_increment_weighted_le (-I*z) (F+I*z)
    (by simpa [mul_re] using hy) (hFsmall.trans hε1)
  rw [show -I*z+(F+I*z)=F by ring] at hsin
  have hreal : (-I*z).re=z.im := by simp [mul_re]
  rw [hreal] at hsin
  have hfreelower := hfree n t t.property
  rw [hreal] at hfreelower
  have hRlower : c≤Real.exp (-z.im)*‖(2:ℂ)*sinh F‖ := by
    have hh := mul_le_mul_of_nonneg_left (norm_le_norm_sub_add (sinh (-I*z)) (sinh F)) (Real.exp_nonneg (-z.im))
    rw [norm_sub_rev,mul_add] at hh
    rw [norm_mul,norm_ofNat]
    nlinarith
  have hSre : |S.re|≤z.im+1 := by
    have he : S.re=z.im+(S+I*z).re := by simp [mul_re]
    rw [he]
    calc
      _ ≤ |z.im|+|(S+I*z).re| := abs_add_le _ _
      _ ≤ z.im+‖S+I*z‖ := by rw [abs_of_nonneg hy];exact add_le_add le_rfl (Complex.abs_re_le_norm _)
      _ ≤ _ := by linarith
  have hdiff := norm_sinh_increment_le_exp_bound S (F-S) (z.im+1) hSre (hδsmall.trans hε1)
  rw [show S+(F-S)=F by ring] at hdiff
  have hRdiff : ‖(2:ℂ)*sinh F-(exp S-(exp S)⁻¹)‖≤4*Real.exp (z.im+1)*‖F-S‖ := by
    rw [show exp S-(exp S)⁻¹=2*sinh S by rw [two_sinh,exp_neg],← mul_sub,norm_mul,norm_ofNat]
    nlinarith
  have hecancel : Real.exp (-z.im)*Real.exp (z.im+1)=Real.exp 1 := by rw [← Real.exp_add];congr 1;ring
  change c≤Real.exp (-z.im)*‖(2:ℂ)*sinh F‖ ∧ r^N*Real.exp (-z.im)*‖(2:ℂ)*sinh F-(exp S-(exp S)⁻¹)‖≤_
  refine ⟨hRlower,?_⟩
  calc
    _ ≤ r^N*Real.exp (-z.im)*(4*Real.exp (z.im+1)*‖F-S‖) :=
      mul_le_mul_of_nonneg_left hRdiff (by positivity)
    _ = 4*(Real.exp (-z.im)*Real.exp (z.im+1))*(r^N*‖F-S‖) := by ring
    _ = 4*Real.exp 1*(r^N*‖F-S‖) := by rw [hecancel]
    _ ≤ _ := mul_le_mul_of_nonneg_left hδN (by positivity)

end NLS.KdV
