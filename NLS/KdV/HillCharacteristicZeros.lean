import NLS.KdV.HillWeightIndependence
import NLS.KdV.HillZeroCount
import NLS.KdV.ClassicalFreePrimitive
import NLS.ComplexAnalysis.ZeroCountHomotopy
import NLS.ComplexAnalysis.IsolatedOrderStability
import NLS.ComplexAnalysis.TwoZeroOrderComparison

/-! # Multiplicity counts for the actual rough Hill characteristic function

The physical characteristic function is the actual monodromy trace squared
minus four. A potential homotopy transfers its free multiplicity count to
every checked high-frequency disc, at the same linear L2 cutoff as the
Fourier reduction. This counts analytic characteristic orders.
-/

noncomputable section
open Set Metric Filter Topology
namespace NLS.KdV

/-- The actual periodic/antiperiodic characteristic function in energy. -/
def hillL2Radicand (q : Coeff 2) (lambda : ℂ) : ℂ := hillL2Discriminant q lambda ^ 2 - 4

theorem analyticOnNhd_hillL2Radicand_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillL2Radicand p.2 p.1) univ :=
  (analyticOnNhd_hillL2Discriminant_joint.pow 2).sub analyticOnNhd_const

theorem analyticOnNhd_hillL2Radicand (q : Coeff 2) :
    AnalyticOnNhd ℂ (hillL2Radicand q) univ :=
  (analyticOnNhd_hillL2Discriminant q).pow 2 |>.sub analyticOnNhd_const

@[simp] theorem hillL2Discriminant_zero (lambda : ℂ) :
    hillL2Discriminant 0 lambda = 2*Complex.cos (Complex.sqrt lambda) := by
  have hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients 0) = 0 := by
    ext k
    simp [hillContinuousCoefficients_apply, fourierCoeff]
  have hc : hillUnitPotentialCurve 0 = 0 := by ext t; rfl
  rw [← hq, hillL2Discriminant_eq_classical, hc, classicalHillDiscriminant_zero]

theorem hillL2Radicand_zero (lambda : ℂ) :
    hillL2Radicand 0 lambda = -4*Complex.sin (Complex.sqrt lambda)^2 := by
  rw [hillL2Radicand, hillL2Discriminant_zero]
  linear_combination 4*Complex.sin_sq_add_cos_sq (Complex.sqrt lambda)

/-- Every nonzero free Hill energy is a double characteristic zero. -/
theorem hillL2Radicand_free_order (n : ℕ) (hn : 1 ≤ n) :
    analyticOrderNatAt (hillL2Radicand 0) (freeHillValue n : ℂ) = 2 := by
  let c : ℂ := freeHillValue n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpos : 0 < (freeHillValue n) := by dsimp [freeHillValue]; positivity
  have hslit : c ∈ Complex.slitPlane := by
    exact Or.inl (by simpa [c] using hpos)
  have hs : AnalyticAt ℂ Complex.sqrt c :=
    Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hslit)
  have hsquare : Complex.sqrt c ^ 2 = ((n : ℂ)*(Real.pi : ℂ))^2 := by
    rw [ComplexAnalysis.complex_sqrt_sq]
    simp only [c, freeHillValue, Int.cast_natCast, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_natCast]
    ring
  have hsin : Complex.sin (Complex.sqrt c) = 0 := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsquare with h | h
    · rw [h, Complex.sin_nat_mul_pi]
    · rw [h, Complex.sin_neg, Complex.sin_nat_mul_pi, neg_zero]
  have hcos : Complex.cos (Complex.sqrt c) ≠ 0 := by
    intro hc
    have h := Complex.sin_sq_add_cos_sq (Complex.sqrt c)
    simp only [hsin, hc, zero_pow (by omega : 2 ≠ 0), add_zero] at h
    exact zero_ne_one h
  have hsder : deriv Complex.sqrt c ≠ 0 := by
    intro hd
    have h := (hs.differentiableAt.hasDerivAt.pow 2).deriv
    change deriv (fun z : ℂ => Complex.sqrt z ^ 2) c = _ at h
    have he : (fun z : ℂ => Complex.sqrt z ^ 2) = id :=
      funext ComplexAnalysis.complex_sqrt_sq
    rw [he, deriv_id, hd] at h
    norm_num at h
  have ha : AnalyticAt ℂ (fun z : ℂ => Complex.sin (Complex.sqrt z)) c :=
    Complex.analyticAt_sin.comp hs
  have hd : deriv (fun z : ℂ => Complex.sin (Complex.sqrt z)) c ≠ 0 := by
    have h := ((Complex.hasDerivAt_sin _).comp c hs.differentiableAt.hasDerivAt).deriv
    exact h.trans_ne (mul_ne_zero hcos hsder)
  have ho := ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hsin hd
  have he : hillL2Radicand 0 = fun z : ℂ => (-4 : ℂ)*Complex.sin (Complex.sqrt z)^2 :=
    funext hillL2Radicand_zero
  have horder : analyticOrderAt (hillL2Radicand 0) c = 2 := by
    rw [he]
    change analyticOrderAt ((fun _ : ℂ => (-4 : ℂ)) *
      (fun z : ℂ => Complex.sin (Complex.sqrt z))^2) c = 2
    rw [analyticOrderAt_mul analyticAt_const (ha.pow 2), analyticOrderAt_pow ha, ho]
    have hc : analyticOrderAt (fun _ : ℂ => (-4 : ℂ)) c = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (by norm_num))
    simp [hc]
  change (analyticOrderAt (hillL2Radicand 0) c).toNat = 2
  rw [horder]
  rfl

theorem hillL2Radicand_free_two_zeros (n : ℕ) (hn : 1 ≤ n) :
    ComplexAnalysis.analyticZeroCount (hillL2Radicand 0)
      (closedBall (freeHillValue n : ℂ) (n : ℝ)) = 2 := by
  rw [ComplexAnalysis.analyticZeroCount_eq_order_of_isolated _ _ _ (by positivity),
    hillL2Radicand_free_order n hn]
  intro z hz hzero
  have hz' := openHillStrip_subset n (hillClosedBall_subset_openStrip n hn hz)
  have heven : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈
      Coeff.paritySubspace 0 := by simp
  have hroot := (hillReduced_zero_iff_l2Discriminant 0 heven n hn z hz' (by simp)).mpr
    (show hillL2Discriminant (SpectralWeight.one.toCoeff 0) z ^ 2 = 4 by
      simpa only [map_zero] using sub_eq_zero.mp hzero)
  have hloc := hillReducedDeterminant_zero_localization 0 n hn z hz' (by simp) hroot
  simpa only [norm_zero, mul_zero, norm_le_zero_iff, sub_eq_zero] using hloc

/-- Physical characteristic roots satisfy the same quantitative localization
as the reduced Fourier determinant. -/
theorem hillL2Radicand_zero_localization
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ))
    (hd : hillL2Radicand (SpectralWeight.one.toCoeff q) z = 0) :
    ‖z-(freeHillValue n : ℂ)‖ ≤ 4*‖q‖ :=
  hillReducedDeterminant_zero_localization q n hn z hz hcut
    ((hillReduced_zero_iff_l2Discriminant q hq n hn z hz hcut).mpr (sub_eq_zero.mp hd))

/-- Exactly two physical characteristic zeros, with analytic multiplicity,
in each high-energy disc at the linear L2 cutoff. -/
theorem hillL2Radicand_two_zeros
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    ComplexAnalysis.analyticZeroCount (hillL2Radicand (SpectralWeight.one.toCoeff q))
      (closedBall (freeHillValue n : ℂ) (n : ℝ)) = 2 := by
  let F : Icc (0 : ℝ) 1 → ℂ → ℂ := fun t z =>
    hillL2Radicand ((t.val : ℂ) • SpectralWeight.one.toCoeff q) z
  have hcont : Continuous F.uncurry := by
    dsimp only [F, Function.uncurry]
    have hc : Continuous (fun p : ℂ × Coeff 2 => hillL2Radicand p.2 p.1) :=
      continuous_iff_continuousAt.mpr
        (fun p => (analyticOnNhd_hillL2Radicand_joint p (mem_univ _)).continuousAt)
    have hm : Continuous (fun p : Icc (0 : ℝ) 1 × ℂ =>
        (p.2, (p.1.val : ℂ) • SpectralWeight.one.toCoeff q)) := by
      have ht : Continuous (fun p : Icc (0 : ℝ) 1 × ℂ => (p.1.val : ℂ)) :=
        Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
      have hq' : Continuous (fun _ : Icc (0 : ℝ) 1 × ℂ => SpectralWeight.one.toCoeff q) :=
        continuous_const
      exact continuous_snd.prodMk (ht.smul hq')
    convert! hc.comp hm using 1
  have hnorm (t : Icc (0 : ℝ) 1) : ‖(t.val : ℂ) • q‖ ≤ ‖q‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t.property.1]
    exact mul_le_of_le_one_left (norm_nonneg q) t.property.2
  have hz (t : Icc (0 : ℝ) 1) (z : ℂ) (hzc : z ∈ sphere (freeHillValue n : ℂ) (n : ℝ)) :
      F t z ≠ 0 := by
    intro hd
    have hpar : SpectralWeight.one.toCoeff ((t.val : ℂ) • q) ∈ Coeff.paritySubspace 0 := by
      rw [map_smul]
      exact (Coeff.paritySubspace 0).smul_mem _ hq
    have hd' : hillL2Radicand (SpectralWeight.one.toCoeff ((t.val : ℂ) • q)) z = 0 := by
      simpa only [map_smul] using hd
    have hloc := hillL2Radicand_zero_localization _ hpar n hn z
      (openHillStrip_subset n (hillClosedBall_subset_openStrip n hn (sphere_subset_closedBall hzc)))
      (show 8*‖(t.val : ℂ) • q‖ ≤ (n : ℝ) by linarith [hnorm t, norm_nonneg q]) hd'
    have he : ‖z-(freeHillValue n : ℂ)‖ = (n : ℝ) := by
      simpa only [mem_sphere, dist_eq_norm] using hzc
    rw [he] at hloc
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    linarith [hnorm t, norm_nonneg q]
  have he := ComplexAnalysis.analyticZeroCount_eq_of_homotopy F (freeHillValue n : ℂ) (n : ℝ)
    (by exact_mod_cast (show 0 < n by omega)) hcont.continuousOn
    (fun t => (analyticOnNhd_hillL2Radicand _).mono (subset_univ _)) hz
    (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1) (⟨0,by norm_num⟩ : Icc (0 : ℝ) 1)
  simpa only [F, Complex.ofReal_one, one_smul, Complex.ofReal_zero, zero_smul,
    hillL2Radicand_free_two_zeros n hn] using he

theorem hillL2Radicand_ne_zero_on_sphere
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (z : ℂ) (hz : z ∈ sphere (freeHillValue n : ℂ) (n : ℝ)) :
    hillL2Radicand (SpectralWeight.one.toCoeff q) z ≠ 0 := by
  intro hd
  have hcut' : 8*‖q‖ ≤ (n : ℝ) := by linarith [norm_nonneg q]
  have hloc := hillL2Radicand_zero_localization q hq n hn z
    (openHillStrip_subset n (hillClosedBall_subset_openStrip n hn (sphere_subset_closedBall hz)))
    hcut' hd
  have hr : ‖z-(freeHillValue n : ℂ)‖ = (n : ℝ) := by
    simpa only [mem_sphere, dist_eq_norm] using hz
  rw [hr] at hloc
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  linarith [norm_nonneg q]

/-- The physical characteristic count exhausts the entire checked strip. -/
theorem hillL2Radicand_strip_two_zeros
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    ComplexAnalysis.analyticZeroCount (hillL2Radicand (SpectralWeight.one.toCoeff q))
      (reducedHillStrip n) = 2 := by
  have he : ComplexAnalysis.analyticZeroCount (hillL2Radicand (SpectralWeight.one.toCoeff q))
      (reducedHillStrip n) =
      ComplexAnalysis.analyticZeroCount (hillL2Radicand (SpectralWeight.one.toCoeff q))
        (closedBall (freeHillValue n : ℂ) (n : ℝ)) := by
    apply ComplexAnalysis.analyticZeroCount_congr_set
    intro z hd
    constructor
    · intro hz
      have hloc := hillL2Radicand_zero_localization q hq n hn z hz
        (show 8*‖q‖ ≤ (n : ℝ) by linarith [norm_nonneg q]) hd
      change dist z (freeHillValue n : ℂ) ≤ (n : ℝ)
      rw [dist_eq_norm]
      linarith [norm_nonneg q]
    · exact fun hz => openHillStrip_subset n (hillClosedBall_subset_openStrip n hn hz)
  rw [he, hillL2Radicand_two_zeros q hq n hn hcut]

/-- Exact order matching between the finite Fourier determinant and the
actual monodromy characteristic, including a double root. This is a
characteristic multiplicity statement, not an unproved operator-multiplicity identification. -/
theorem hillReduced_order_eq_l2Radicand
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ))
    (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    analyticOrderNatAt (fun y => hillReducedDeterminant SpectralWeight.one n (q,y)) z =
      analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) z := by
  classical
  have hcut' : 8*‖q‖ ≤ (n : ℝ) := by linarith [norm_nonneg q]
  have heq (y : ℂ) (hy : y ∈ reducedHillStrip n) :
      hillReducedDeterminant SpectralWeight.one n (q,y) = 0 ↔
        hillL2Radicand (SpectralWeight.one.toCoeff q) y = 0 := by
    rw [hillL2Radicand, sub_eq_zero]
    exact hillReduced_zero_iff_l2Discriminant q hq n hn y hy hcut'
  by_cases hd : hillReducedDeterminant SpectralWeight.one n (q,z) = 0
  · have hloc := hillReducedDeterminant_zero_localization q n hn z hz hcut' hd
    have hzk : z ∈ closedBall (freeHillValue n : ℂ) (n : ℝ) := by
      change dist z (freeHillValue n : ℂ) ≤ (n : ℝ)
      rw [dist_eq_norm]
      linarith [norm_nonneg q]
    obtain ⟨b,hb⟩ := (NormedSpace.sphere_nonempty (E := ℂ)
      (x := (freeHillValue n : ℂ))).mpr (show 0 ≤ (n : ℝ) by positivity)
    have hbD := hillL2Radicand_ne_zero_on_sphere q hq n hn hcut' b hb
    have hbf : hillReducedDeterminant SpectralWeight.one n (q,b) ≠ 0 :=
      fun hb0 => hbD ((heq b (openHillStrip_subset n
        (hillClosedBall_subset_openStrip n hn (sphere_subset_closedBall hb)))).mp hb0)
    exact ComplexAnalysis.analyticOrderNatAt_eq_of_two_zero_counts
      (isCompact_closedBall _ _) (isConnected_closedBall (by positivity))
      ((analyticOnNhd_hillReducedDeterminant_spectral SpectralWeight.one q n hn hcut').mono
        (hillClosedBall_subset_openStrip n hn))
      ((analyticOnNhd_hillL2Radicand _).mono (subset_univ _))
      (sphere_subset_closedBall hb) hbf hbD (hillReducedDeterminant_two_zeros q n hn hcut)
      (hillL2Radicand_two_zeros q hq n hn hcut')
      (fun y hy => heq y (openHillStrip_subset n (hillClosedBall_subset_openStrip n hn hy))) hzk
  · have hD : hillL2Radicand (SpectralWeight.one.toCoeff q) z ≠ 0 :=
      fun hD => hd ((heq z hz).mpr hD)
    have hf0 : analyticOrderNatAt (fun y => hillReducedDeterminant SpectralWeight.one n (q,y)) z = 0 := by
      by_contra hf0
      exact hd (apply_eq_zero_of_analyticOrderNatAt_ne_zero
        (f := fun y : ℂ => hillReducedDeterminant SpectralWeight.one n (q,y)) hf0)
    have hg0 : analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) z = 0 := by
      by_contra hg0
      exact hD (apply_eq_zero_of_analyticOrderNatAt_ne_zero hg0)
    rw [hf0,hg0]

end NLS.KdV
