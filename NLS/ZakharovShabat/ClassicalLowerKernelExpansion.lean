import NLS.ZakharovShabat.SobolevClassicalDiagonalExpansion
import NLS.ZakharovShabat.ClassicalScalarForcingLowerKernel

/-! # The first mass correction to the lower propagator

The actual lower propagator has its explicit primitive-difference correction with a quadratic inverse-frequency error on original Sobolev balls.
-/

noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

private theorem norm_lowerKernel_expansion_algebra
    (a b c d u v P Q w : ℂ) (B C D K E : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hw : ‖w‖ ≤ 1) (hb : ‖b‖ ≤ B) (hu : ‖u‖ ≤ E) (hv : ‖v‖ ≤ E)
    (hP : ‖P‖ ≤ K) (hQ : ‖Q‖ ≤ K)
    (ha : ‖a-u*(1-w*P)‖ ≤ C*‖w‖^2)
    (hb' : ‖b-v*(1+w*Q)‖ ≤ C*‖w‖^2)
    (hc : ‖c‖ ≤ D*‖w‖) (hd : ‖d‖ ≤ D*‖w‖) :
    ‖a*b-c*d-u*v*(1+w*(Q-P))‖ ≤
      (C*B+E*(1+K)*C+E^2*K^2+D^2)*‖w‖^2 := by
  have hp : ‖1-w*P‖ ≤ 1+K := by
    apply (norm_sub_le _ _).trans
    rw [norm_one,norm_mul]
    have h := mul_le_mul hw hP (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    linarith
  have ha0 : ‖u*(1-w*P)‖ ≤ E*(1+K) := by
    rw [norm_mul]
    exact mul_le_mul hu hp (norm_nonneg _) hE
  have h₁ : ‖(a-u*(1-w*P))*b‖ ≤ C*B*‖w‖^2 := by
    rw [norm_mul]
    exact (mul_le_mul ha hb (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have h₂ : ‖u*(1-w*P)*(b-v*(1+w*Q))‖ ≤ E*(1+K)*C*‖w‖^2 := by
    rw [norm_mul]
    exact (mul_le_mul ha0 hb' (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have h₃ : ‖u*v*w^2*P*Q‖ ≤ E^2*K^2*‖w‖^2 := by
    simp only [norm_mul,norm_pow]
    calc
      _ ≤ E*E*‖w‖^2*K*K := by gcongr
      _ = _ := by ring
  have h₄ : ‖c*d‖ ≤ D^2*‖w‖^2 := by
    rw [norm_mul]
    exact (mul_le_mul hc hd (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have he : a*b-c*d-u*v*(1+w*(Q-P)) =
      (a-u*(1-w*P))*b+u*(1-w*P)*(b-v*(1+w*Q))-u*v*w^2*P*Q-c*d := by ring
  rw [he]
  have ht (x y r s : ℂ) : ‖x+y-r-s‖ ≤ ‖x‖+‖y‖+‖r‖+‖s‖ := by
    linarith [norm_sub_le (x+y-r) s,norm_sub_le (x+y) r,norm_add_le x y]
  exact (ht _ _ _ _).trans ((add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄).trans_eq (by ring))

/-- The actual lower propagator has the explicit mass-primitive difference
as its first inverse-frequency correction. The quadratic error is uniform
on original complex Hs balls, strips, and both physical endpoints. -/
theorem exists_uniform_classical_lowerKernel_first_order_expansion
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H → ∀ t x : Icc (0:ℝ) 1,
        ‖classicalScalarForcingLowerKernel (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z t x-
          exp (I*z*(t.val-x.val))*(1+(2*I*z)⁻¹*(nlsWKBMassPrimitive a b t-nlsWKBMassPrimitive a b x))‖ ≤
          C*‖(2*I*z)⁻¹‖^2 := by
  obtain ⟨C,hC,hdiag⟩ := exists_uniform_classical_diagonal_first_order_expansion s hs R hR H
  obtain ⟨A,hA,hpot⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  let D := 2*classicalSobolevErrorConstant (2*R) H
  let E := Real.exp H
  let K := A^2
  let B := E+D
  have hD : 0 ≤ D := mul_nonneg (by norm_num) (classicalSobolevErrorConstant_nonneg _ _ (by positivity))
  have hE : 0 ≤ E := (Real.exp_pos H).le
  have hK : 0 ≤ K := sq_nonneg A
  have hB : 0 ≤ B := add_nonneg hE hD
  refine ⟨C*B+E*(1+K)*C+E^2*K^2+D^2,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH t x
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  let w := (2*I*z)⁻¹
  have hw : ‖w‖ ≤ 1 := by
    simp only [w,norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    apply inv_le_one_of_one_le₀
    linarith
  have hfree (v : ℂ × ℂ) (y : Icc (0:ℝ) 1) :
      ‖classicalSolution Φ z v y-classicalFreeVector z v y‖ ≤ D*‖v‖*‖w‖ :=
    norm_classicalSolution_sub_free_higherSobolev_le s hs R H ab hab a b ha.continuous hb.continuous
      hpa hpb hca hcb z (norm_pos_iff.mp (by linarith)) hzH v y
  have hu : ‖exp (-I*z*x.val)‖ ≤ E := norm_exp_neg_I_mul_strip_le z H hzH x x.property
  have hv : ‖exp (I*z*t.val)‖ ≤ E := by
    have hh := norm_exp_neg_I_mul_strip_le (-z) H (by simpa using hzH) t t.property
    simpa only [mul_neg,neg_mul,neg_neg] using hh
  have hP (y : Icc (0:ℝ) 1) : ‖nlsWKBMassPrimitive a b y‖ ≤ K :=
    norm_nlsWKBMassPrimitive_le a b A hA
      (hpot ab hab a b ha hb hpa hpb hca hcb)
      (hpot (ab.2,ab.1) (by simpa only [Prod.norm_def,max_comm] using hab)
        b a hb ha hpb hpa hcb hca) y y.property
  have hc : ‖(classicalSolution Φ z (0,1) x).1‖ ≤ D*‖w‖ := by
    have hh := (norm_fst_le _).trans (hfree (0,1) x)
    simpa only [Prod.fst_sub,classicalFreeVector,mul_zero,sub_zero,Prod.norm_def,norm_one,norm_zero,
      max_eq_right zero_le_one,mul_one] using hh
  have hd : ‖(classicalSolution Φ z (1,0) t).2‖ ≤ D*‖w‖ := by
    have hh := (norm_snd_le _).trans (hfree (1,0) t)
    simpa only [Prod.snd_sub,classicalFreeVector,mul_zero,sub_zero,Prod.norm_def,norm_one,norm_zero,
      max_eq_left zero_le_one,mul_one] using hh
  have hbfree : ‖(classicalSolution Φ z (0,1) t).2-exp (I*z*t.val)‖ ≤ D*‖w‖ := by
    have hh := (norm_snd_le _).trans (hfree (0,1) t)
    simpa only [Prod.snd_sub,classicalFreeVector,mul_one,Prod.norm_def,norm_one,norm_zero,
      max_eq_right zero_le_one] using hh
  have hbn : ‖(classicalSolution Φ z (0,1) t).2‖ ≤ B := by
    have hh := norm_le_norm_sub_add (classicalSolution Φ z (0,1) t).2 (exp (I*z*t.val))
    have hwD := mul_le_of_le_one_right hD hw
    dsimp only [B]
    linarith
  have hax := (hdiag ab hab a b ha hb hpa hpb hca hcb z hz hzH x).1
  have hbt := (hdiag ab hab a b ha hb hpa hpb hca hcb z hz hzH t).2
  have hh := norm_lowerKernel_expansion_algebra
    (classicalSolution Φ z (1,0) x).1 (classicalSolution Φ z (0,1) t).2
    (classicalSolution Φ z (0,1) x).1 (classicalSolution Φ z (1,0) t).2
    (exp (-I*z*x.val)) (exp (I*z*t.val))
    (nlsWKBMassPrimitive a b x) (nlsWKBMassPrimitive a b t) w B C D K E
    hC hD hK hE hw hbn hu hv (hP x) (hP t) hax hbt hc hd
  have he : exp (-I*z*x.val)*exp (I*z*t.val) = exp (I*z*(t.val-x.val)) := by
    rw [← exp_add]
    congr 1
    ring
  simpa only [classicalScalarForcingLowerKernel,Φ,w,he] using hh

end NLS.ZakharovShabat
