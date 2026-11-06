import NLS.KdV.HillHminusOneJointGapRoots
import NLS.KdV.SquaredCoshCriticalDisc
import NLS.KdV.FrequencyPrimitiveContinuation

/-! # Uniform normalized deflated roots for the actual rough high gaps

The root has the original free sign before a possible constant sign
normalization. Its square factors the actual radicand. Compactness of the
unit squared-primitive disc gives a common bound for its inverse.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_squaredCosh_deriv_inverse_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, ‖w‖ ≤ 1 →
      deriv squaredCosh w ≠ 0 ∧ ‖(deriv squaredCosh w)⁻¹‖ ≤ C := by
  have hn (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) 1) : deriv squaredCosh w ≠ 0 := by
    apply deriv_squaredCosh_ne_zero_of_norm_lt_pi_sq
    have hh : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
    nlinarith [Real.pi_gt_three]
  have hc : ContinuousOn (fun w : ℂ => (deriv squaredCosh w)⁻¹) (closedBall (0 : ℂ) 1) := by
    intro w hw
    exact (((analyticOnNhd_squaredCosh w (mem_univ _)).deriv).continuousAt.inv₀ (hn w hw)).continuousWithinAt
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hc
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro w hw
  have hb : w ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hw
  exact ⟨hn w hb,(hC w hb).trans (le_max_left _ _)⟩

def hillHminusHighNormalizedDeflatedRoot
    (n : ℕ+) (r : ℝ) (K : ℂ × PeriodOneHminusOne → ℂ)
    (t : ℂ × PeriodOneHminusOne) : ℂ :=
  (2*I*(-1 : ℂ)^(n : ℕ)/(Real.pi : ℂ))*
    hillHminusJointNormalizedGapRoot n r K t*deriv squaredCosh (K t)

theorem hillHminusHighNormalizedDeflatedRoot_factor
    (n : ℕ+) (r : ℝ) (K : ℂ × PeriodOneHminusOne → ℂ)
    (t : ℂ × PeriodOneHminusOne)
    (htrace : squaredCosh (K t)=(-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant t.2 t.1/2)
    (hfactor : K t= -hillHminusGapPolynomial n r t*hillHminusJointNormalizedGapRoot n r K t^2 /
      (4*((Real.pi : ℂ)*(n : ℕ))^2)) :
    hillHminusRadicand t.2 t.1=hillHminusGapPolynomial n r t*
      (hillHminusHighNormalizedDeflatedRoot n r K t/(n : ℂ))^2 := by
  have hs : ((-1 : ℂ)^(n : ℕ))^2=1 := by
    rw [← pow_mul,Nat.mul_comm (n : ℕ) 2,pow_mul]
    norm_num
  have hrad : hillHminusRadicand t.2 t.1=16*K t*(deriv squaredCosh (K t))^2 := by
    have hh := squaredCosh_radicand_factorization (K t)
    rw [htrace] at hh
    unfold hillHminusRadicand
    linear_combination hh - (hillHminusDiscriminant t.2 t.1)^2*hs
  rw [hrad]
  nth_rw 1 [hfactor]
  simp only [hillHminusHighNormalizedDeflatedRoot,div_pow,mul_pow,I_sq,hs]
  have hp : (Real.pi : ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn : (n : ℂ)≠0 := by exact_mod_cast n.ne_zero
  field_simp [hp,hn]
  ring

theorem hillHminusHighNormalizedDeflatedRoot_inverse_bound
    (C : ℝ) (hC : 0 ≤ C) (n : ℕ+) (r : ℝ)
    (K : ℂ × PeriodOneHminusOne → ℂ) (t : ℂ × PeriodOneHminusOne)
    (hJ : hillHminusJointNormalizedGapRoot n r K t ≠ 0)
    (hJb : ‖hillHminusJointNormalizedGapRoot n r K t-1‖ ≤ 1/2)
    (hD : deriv squaredCosh (K t) ≠ 0) (hDb : ‖(deriv squaredCosh (K t))⁻¹‖ ≤ C) :
    hillHminusHighNormalizedDeflatedRoot n r K t ≠ 0 ∧
      ‖(hillHminusHighNormalizedDeflatedRoot n r K t)⁻¹‖ ≤ Real.pi*C := by
  let J := hillHminusJointNormalizedGapRoot n r K t
  have hJlower : 1/2 ≤ ‖J‖ := by
    have hh := norm_le_norm_sub_add (1 : ℂ) J
    rw [norm_one,norm_sub_rev] at hh
    linarith
  have hJi : ‖J⁻¹‖ ≤ 2 := by
    rw [norm_inv,← one_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hJ)).mpr
    linarith
  have hp : (Real.pi : ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : (-1 : ℂ)^(n : ℕ)≠0 := pow_ne_zero _ (by norm_num)
  have ha : (2*I*(-1 : ℂ)^(n : ℕ)/(Real.pi : ℂ))≠0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hs) hp
  have hnorm : ‖(2*I*(-1 : ℂ)^(n : ℕ)/(Real.pi : ℂ))⁻¹‖=Real.pi/2 := by
    rw [norm_inv,norm_div,norm_mul,norm_mul,norm_ofNat,norm_I,norm_pow,
      norm_neg,norm_one,one_pow,norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    field_simp
  refine ⟨mul_ne_zero (mul_ne_zero ha hJ) hD,?_⟩
  change ‖(((2*I*(-1 : ℂ)^(n : ℕ)/(Real.pi : ℂ))*J*deriv squaredCosh (K t))⁻¹)‖ ≤ _
  rw [mul_inv_rev,mul_inv_rev,norm_mul,norm_mul,hnorm]
  rw [← mul_assoc]
  have hh := mul_le_mul hDb hJi (norm_nonneg _) hC
  calc
    _ ≤ (C*2)*(Real.pi/2) := mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by ring

theorem exists_hillHminus_high_deflated_roots (q : PeriodOneHminusOne) :
    ∃ r C : ℝ, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < C ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ U : ℂ × PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ U
          (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V) ∧
        (∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u) ∧
        ∀ t ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V,
          U t ≠ 0 ∧ ‖(U t)⁻¹‖ ≤ C ∧
          hillHminusRadicand t.2 t.1=hillHminusGapPolynomial n r t*(U t/(n : ℂ))^2 := by
  obtain ⟨B,hB,hD⟩ := exists_squaredCosh_deriv_inverse_bound
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_hillHminus_normalized_gap_squares q
  obtain ⟨N,V,hN,hV,hq,hfamily⟩ := hfamily (1/2) (by norm_num)
  refine ⟨r,Real.pi*B,N,V,hr,hrpi,mul_pos Real.pi_pos hB,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨K,hK,hKb,htrace,_hz,_hmatch,hpairs⟩ := hfamily n hn
  have hdata : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
      (∀ z : ℂ, K (z,a)=(z-l)*(z-u)*twoRootDeflation (fun w => K (w,a)) l u z) ∧
      ∀ z ∈ hillHminusGapSquareDisc n r, ‖hillHminusNormalizedGapSquare n K a l u z-1‖ ≤ 1/2 := by
    intro a ha
    obtain ⟨l,u,hpair,_hQ,hfac,hb⟩ := hpairs a ha
    exact ⟨l,u,hpair,hfac,hb⟩
  obtain ⟨hJ,hprops⟩ := hillHminusJointNormalizedGapRoot_properties n r (1/2) hr
    (by norm_num) V hV K hK hdata
  let U := hillHminusHighNormalizedDeflatedRoot n r K
  have hKa : AnalyticOnNhd ℂ K
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V) :=
    hK.mono (fun t ht => ⟨ball_subset_closedBall ht.1,ht.2⟩)
  refine ⟨U,?_,?_,?_⟩
  · intro t ht
    have hd := ((analyticOnNhd_squaredCosh (K t) (mem_univ _)).deriv).comp (hKa t ht)
    exact ((analyticAt_const.mul (hJ t ht)).mul hd)
  · intro a ha
    obtain ⟨l,u,hpair,_⟩ := hdata a ha
    exact ⟨l,u,hpair⟩
  · intro t ht
    obtain ⟨hDn,hDb⟩ := hD (K t) (hKb t ⟨ball_subset_closedBall ht.1,ht.2⟩).le
    obtain ⟨hu,hb⟩ := hillHminusHighNormalizedDeflatedRoot_inverse_bound B hB.le n r K t
      (hprops t ht).1 (hprops t ht).2.1 hDn hDb
    exact ⟨hu,hb,hillHminusHighNormalizedDeflatedRoot_factor n r K t
      (htrace t ⟨ball_subset_closedBall ht.1,ht.2⟩) (hprops t ht).2.2⟩

end NLS.KdV
