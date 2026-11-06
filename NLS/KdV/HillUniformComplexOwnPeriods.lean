import NLS.KdV.HillComplexPeriodErrorBounds
import NLS.KdV.HillComplexPeriodLocalRootGerm
import NLS.ComplexAnalysis.BanachAnalyticZeroBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The free own-gap quotient has a uniform bound after multiplication
by the actual contour radius. -/
theorem norm_hillFreeOwnAbelianQuotient_on_contour (n : ℕ) (hn : 1≤n) (E : ℂ)
    (hE : E∈sphere (hillRealGapCenter 0 h0q h0r n : ℂ)
      (hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n)) :
    ‖hillAbelianPsiCandidate hillFreeGapRoot n E/hillEnergyCanonicalRootProduct 0 h0q h0r E‖ ≤
      2/(hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n) := by
  let R := hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r n hn).1
    (hillRealGapContour_geometry 0 h0q h0r n hn).2.1
  have hnorm : ‖(freeHillValue n : ℂ)-E‖=R := by
    rw [norm_sub_rev]
    simpa only [mem_sphere,dist_eq_norm,hillFreeGapCenter h0q h0r n hn] using hE
  have hg := (hillFreeGapContour_frequency_bounds h0q h0r n hn E hE).2.2.2
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  rw [hillFreeAbelianQuotient h0q h0r n hn E (hillRealGapContour_sphere_subset 0 h0q h0r n hn hE),
    norm_div,norm_mul,norm_mul,norm_I,one_mul,norm_natCast,norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,norm_mul,hnorm]
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity : 0<((n:ℝ)*Real.pi/2)*R)
    (mul_le_mul_of_nonneg_right hg hR.le)).trans_eq
  change (n:ℝ)*Real.pi/(((n:ℝ)*Real.pi/2)*R)=2/R
  field_simp

/-- A common bound for the original diagonal complex periods on a common
complex potential ball; unlike the scaled off-diagonal control this
estimate includes the own normalization period. -/
theorem exists_hillAbelianComplexOwnPeriod_common_bound :
    ∃ ε M : ℝ, 0<ε ∧ 0<M ∧ ∀ n : ℕ, 1≤n → ∀ a p : Coeff 2, ‖p‖≤ε →
      ‖hillAbelianComplexPeriod 0 h0q h0r n n (a,p)‖ ≤ M*Real.exp ((8/Real.pi^2)*‖a‖) := by
  obtain ⟨ε,C,hε,hC,hbound⟩ := exists_hillFreeGapContour_inverse_root_bound h0q h0r
  refine ⟨ε,2*(1+C*ε),hε,by positivity,?_⟩
  intro n hn a p hp
  let R := hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r n hn).1
    (hillRealGapContour_geometry 0 h0q h0r n hn).2.1
  have hi (E : ℂ) (hE : E∈sphere (hillRealGapCenter 0 h0q h0r n : ℂ) R) :
      ‖hillAbelianHilbertPsi n (E,a)/hillAbelianComplexRoot 0 h0q h0r (E,p)‖ ≤
        (2/R)*Real.exp ((8/Real.pi^2)*‖a‖)*(1+C*ε) := by
    obtain ⟨hd,hb⟩ := hbound p hp n hn E hE
    have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
    have hr : ‖hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)‖≤1+C*ε := by
      have hh := norm_add_le (hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)-1) (1:ℂ)
      rw [sub_add_cancel,norm_one] at hh
      have hh' : C*‖p‖/(n:ℝ)≤C*ε :=
        (div_le_self (by positivity) hn1).trans (mul_le_mul_of_nonneg_left hp hC.le)
      linarith
    have he : hillAbelianHilbertPsi n (E,a)/hillAbelianComplexRoot 0 h0q h0r (E,p) =
        (hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 h0q h0r E)*
          (hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)) := by
      have hd0 := hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain 0 h0q h0r E hd.1.1
      field_simp
    rw [he,norm_mul,hillAbelianHilbertPsi_contour_separation h0q h0r n n hn E hE a,mul_div_right_comm,norm_mul]
    exact mul_le_mul (mul_le_mul (norm_hillFreeOwnAbelianQuotient_on_contour h0q h0r n hn E hE)
      (norm_hilbertWeightedProduct_hillFreeContour_le h0q h0r n n hn E hE a) (norm_nonneg _) (by positivity))
      hr (norm_nonneg _) (by positivity)
  have hh := norm_normalized_circleIntegral_difference_le
    (fun E => hillAbelianHilbertPsi n (E,a)/hillAbelianComplexRoot 0 h0q h0r (E,p))
    (fun _ => 0) (hillRealGapCenter 0 h0q h0r n : ℂ) 1 R
    ((2/R)*Real.exp ((8/Real.pi^2)*‖a‖)*(1+C*ε)) hR.le
    (hillAbelianComplexIntegrand_circleIntegrable h0q h0r n n hn a p (fun E hE => (hbound p hp n hn E hE).1))
    (by fun_prop) (by simpa only [sub_zero,one_mul] using hi)
  have hz : (∮ E in C((hillRealGapCenter 0 h0q h0r n : ℂ),R), (0:ℂ))=0 := by
    simp [circleIntegral]
  simp only [hz,mul_zero,sub_zero,one_mul] at hh
  change ‖hillAbelianComplexPeriod 0 h0q h0r n n (a,p)‖≤_ at hh
  apply hh.trans_eq
  field_simp

/-- The original own periods approach one uniformly in the index on a
common joint Hilbert neighborhood of zero roots and zero potential. -/
theorem exists_hillAbelianComplexOwnPeriod_common_linear_deviation :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ n : ℕ, 1≤n → ∀ t∈ball (0 : Coeff 2 × Coeff 2) r,
      ‖hillAbelianComplexPeriod 0 h0q h0r n n t-1‖≤L*‖t‖ := by
  obtain ⟨ε,M,hε,hM,hbound⟩ := exists_hillAbelianComplexOwnPeriod_common_bound h0q h0r
  obtain ⟨εc,D,hεc,_,hc⟩ := exists_hillComplexPeriodControl h0q h0r
  let R := min 1 (min ε εc)
  have hR : 0<R := by dsimp only [R];positivity
  have hR1 : R≤1 := min_le_left _ _
  have hRε : R≤ε := (min_le_right _ _).trans (min_le_left _ _)
  have hRεc : R≤εc := (min_le_right _ _).trans (min_le_right _ _)
  let B := M*Real.exp (8/Real.pi^2)+1
  refine ⟨R/4,8*B/R,by positivity,by dsimp only [B];positivity,?_⟩
  intro n hn
  let f : Coeff 2 × Coeff 2 → ℂ := fun t => hillAbelianComplexPeriod 0 h0q h0r n n t-1
  have hA := analyticOnNhd_hillAbelianComplexPeriod_of_domain 0 h0q h0r n n hn
    (ball 0 εc) isOpen_ball
    (fun p hp E hE => (hc p (show ‖p‖≤εc from
      (show ‖p‖<εc by simpa only [mem_ball,dist_zero_right] using hp).le)).1 n hn E hE)
  have hf : AnalyticOnNhd ℂ f (ball 0 R) := by
    intro t ht
    have ht' : ‖t‖<R := by simpa only [mem_ball,dist_zero_right] using ht
    have hp : t.2∈ball 0 εc := by
      rw [mem_ball,dist_zero_right]
      exact (norm_snd_le t).trans_lt (ht'.trans_le hRεc)
    exact (hA t ⟨mem_univ _,hp⟩).sub analyticAt_const
  have hf0 : f 0=0 := by
    change hillAbelianComplexPeriod 0 h0q h0r n n (0,0)-1=0
    rw [hillAbelianComplexPeriod_zero_diagonal h0q h0r n hn,sub_self]
  have hb (t : Coeff 2 × Coeff 2) (ht : t∈ball 0 R) : ‖f t‖≤B := by
    have ht' : ‖t‖<R := by simpa only [mem_ball,dist_zero_right] using ht
    have hp : ‖t.2‖≤ε := (norm_snd_le t).trans (ht'.le.trans hRε)
    have ha : ‖t.1‖≤1 := (norm_fst_le t).trans (ht'.le.trans hR1)
    apply (norm_sub_le (hillAbelianComplexPeriod 0 h0q h0r n n t) 1).trans
    rw [norm_one]
    change ‖hillAbelianComplexPeriod 0 h0q h0r n n t‖+1≤M*Real.exp (8/Real.pi^2)+1
    apply add_le_add ((hbound n hn t.1 t.2 hp).trans _) le_rfl
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      have hK : 0≤8/Real.pi^2 := by positivity
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ha hK)) hM.le
  exact norm_le_mul_norm_of_analytic_zero_ball_bound f R B hR hf hf0 hb

end NLS.KdV
