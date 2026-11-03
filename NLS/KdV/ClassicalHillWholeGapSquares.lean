import NLS.KdV.ClassicalCoshStripControl
import NLS.KdV.ClassicalHillSmallDiscTrace
import NLS.KdV.ClassicalHillSmallGapCoverage
import NLS.KdV.ClassicalHillSquaredPrimitiveMatching

/-! # One actual analytic squared primitive on complete high-gap discs

A common small normalized-trace neighborhood is pulled through one
squared-cosh inverse. Uniform strip control identifies the resulting
joint analytic functions with actual F_n^2 everywhere admissible on the
whole disc, including through every branch point. These are energy discs,
so straight complex gap segments can be enclosed without endpoint charts.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

/-- A literal energy disc of radius n*pi*r around the free energy. -/
def classicalHillGapSquareDisc (n : ℕ+) (r : ℝ) : Set ℂ :=
  closedBall (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)

private theorem sqrt_square (z : ℂ) : (Complex.sqrt z)^2 = z := by
  have h := Complex.cpow_nat_inv_pow z (Nat.succ_ne_zero 1)
  norm_num at h
  simpa only [Complex.sqrt,one_div] using h

/-- An entire energy disc is covered by the principal frequency disc.
The root's nonnegative real part controls the exact factored denominator. -/
theorem sqrt_mem_closedBall_of_energy_disc (c r : ℝ) (hc : 0 < c) (z : ℂ)
    (hz : z ∈ closedBall ((c : ℂ)^2) (c*r)) :
    Complex.sqrt z ∈ closedBall (c : ℂ) r := by
  have hre : 0 ≤ (Complex.sqrt z).re := by rw [Complex.sqrt,cpow_inv_two_re]; positivity
  have hsum : c ≤ ‖Complex.sqrt z+(c : ℂ)‖ := by
    have h := re_le_norm (Complex.sqrt z+(c : ℂ))
    simp only [add_re,ofReal_re] at h
    linarith
  have he : (Complex.sqrt z-(c : ℂ))*(Complex.sqrt z+(c : ℂ)) = z-(c : ℂ)^2 := by
    linear_combination sqrt_square z
  have hn := congrArg norm he
  rw [norm_mul] at hn
  have hb : ‖z-(c : ℂ)^2‖ ≤ c*r := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have hprod := mul_le_mul_of_nonneg_left hsum (norm_nonneg (Complex.sqrt z-(c : ℂ)))
  have hnorm : ‖Complex.sqrt z-(c : ℂ)‖ ≤ r := by nlinarith
  simpa only [mem_closedBall,dist_eq_norm] using hnorm

theorem sqrt_mem_ball_of_energy_disc (c r : ℝ) (hc : 0 < c) (z : ℂ)
    (hz : z ∈ ball ((c : ℂ)^2) (c*r)) :
    Complex.sqrt z ∈ ball (c : ℂ) r := by
  have hre : 0 ≤ (Complex.sqrt z).re := by rw [Complex.sqrt,cpow_inv_two_re]; positivity
  have hsum : c ≤ ‖Complex.sqrt z+(c : ℂ)‖ := by
    have h := re_le_norm (Complex.sqrt z+(c : ℂ))
    simp only [add_re,ofReal_re] at h
    linarith
  have he : (Complex.sqrt z-(c : ℂ))*(Complex.sqrt z+(c : ℂ)) = z-(c : ℂ)^2 := by
    linear_combination sqrt_square z
  have hn := congrArg norm he
  rw [norm_mul] at hn
  have hb : ‖z-(c : ℂ)^2‖ < c*r := by simpa only [mem_ball,dist_eq_norm] using hz
  have hprod := mul_le_mul_of_nonneg_left hsum (norm_nonneg (Complex.sqrt z-(c : ℂ)))
  have hnorm : ‖Complex.sqrt z-(c : ℂ)‖ < r := by nlinarith
  simpa only [mem_ball,dist_eq_norm] using hnorm

/-- A smaller frequency disc maps strictly into the energy disc. This
strict inclusion leaves room for the entire complex straight gap segment. -/
theorem square_mem_energy_ball_of_small_frequency
    (c r : ℝ) (hc : 0 < c) (hr : 0 < r) (hrc : r ≤ c) (z : ℂ)
    (hz : z ∈ ball (c : ℂ) (r/4)) :
    z^2 ∈ ball ((c : ℂ)^2) (c*r) := by
  have hdist : ‖z-(c : ℂ)‖ < r/4 := by simpa only [mem_ball,dist_eq_norm] using hz
  have htwo : ‖(2 : ℂ)*(c : ℂ)‖ = 2*c := by simp [abs_of_pos hc]
  have hsum : ‖z+(c : ℂ)‖ ≤ 3*c := by
    have h : ‖z+(c : ℂ)‖ ≤ ‖z-(c : ℂ)‖+2*c := by
      calc
        _ = ‖(z-(c : ℂ))+(2 : ℂ)*(c : ℂ)‖ := by congr 1; ring
        _ ≤ _ := by simpa only [htwo] using norm_add_le (z-(c : ℂ)) ((2 : ℂ)*(c : ℂ))
    linarith
  have he : z^2-(c : ℂ)^2 = (z-(c : ℂ))*(z+(c : ℂ)) := by ring
  rw [mem_ball,dist_eq_norm,he,norm_mul]
  calc
    _ ≤ ‖z-(c : ℂ)‖*(3*c) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ < (r/4)*(3*c) := mul_lt_mul_of_pos_right hdist (by positivity)
    _ < c*r := by nlinarith

/-- A single inverse and a common complex potential neighborhood give
one analytic square on every complete high energy disc. The actual
shifted primitive agrees wherever its source continuation is admissible. -/
theorem exists_classicalHill_whole_disc_small_squares (q : Curve ℂ) (B : ℝ) (hB : 0 < B) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (Curve ℂ),
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × Curve ℂ → ℂ,
        AnalyticOnNhd ℂ K (classicalHillGapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V, ‖K t‖ < B) ∧
        (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V,
          squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*classicalHillDiscriminant t.2 t.1/2) ∧
        (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V,
          K t = 0 ↔ classicalHillRadicand t = 0) ∧
        ∀ t ∈ (classicalHillGapSquareDisc n r ×ˢ V) ∩ classicalHillContinuationDomain,
          K t = (classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2 := by
  obtain ⟨U,W,hU,hW,h0,h1,G,hG,hG1,hleft,hright⟩ := exists_squaredCosh_inverse
  have hpre : IsOpen ((fun z : ℂ => z^2) ⁻¹' U) := hU.preimage (continuous_id.pow 2)
  have h0pre : (0 : ℂ) ∈ (fun z : ℂ => z^2) ⁻¹' U := by simpa using h0
  obtain ⟨epsilon,hepsilon,hsmallU⟩ := Metric.mem_nhds_iff.mp (hpre.mem_nhds h0pre)
  obtain ⟨d,hd,hcontrol⟩ := exists_delta_cosh_strip_control epsilon hepsilon
  obtain ⟨eta,heta,hsmallW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h1)
  obtain ⟨etaG,hetaG,hsmallG⟩ := Metric.continuousAt_iff.mp
    ((hG 1 h1).continuousAt : ContinuousAt G (1 : ℂ)) B hB
  let delta : ℝ := min 1 (min d (min eta etaG))
  have hdelta : 0 < delta := lt_min (by norm_num) (lt_min hd (lt_min heta hetaG))
  have hdelta1 : delta ≤ 1 := min_le_left _ _
  have hdeltad : delta ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaeta : delta ≤ eta :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaG : delta ≤ etaG :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨r,Nt,Vt,hr,hrpi,hNt,hVt,hqt,htrace⟩ :=
    exists_classicalHill_small_disc_normalized_trace q delta hdelta
  obtain ⟨Ns,Vs,_,hVs,hqs,hstrip⟩ := exists_classicalHill_high_primitive_strip q
  refine ⟨r,max Nt Ns,Vt ∩ Vs,hr,hrpi,hNt.trans_le (le_max_left _ _),
    hVt.inter hVs,⟨hqt,hqs⟩,?_⟩
  intro n hn
  let D : ℂ × Curve ℂ → ℂ := fun t => (-1 : ℂ)^(n : ℕ)*classicalHillDiscriminant t.2 t.1/2
  let K : ℂ × Curve ℂ → ℂ := G ∘ D
  have hD : AnalyticOnNhd ℂ D univ :=
    (analyticOnNhd_const.mul analyticOnNhd_classicalHillDiscriminant_joint).div_const
  have hfreq (t : ℂ × Curve ℂ) (ht : t ∈ classicalHillGapSquareDisc n r ×ˢ (Vt ∩ Vs)) :
      Complex.sqrt t.1 ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) r := by
    have hc : (0 : ℝ) < Real.pi*(n : ℕ) := by positivity
    have h := sqrt_mem_closedBall_of_energy_disc (Real.pi*(n : ℕ)) r hc t.1
      (by simpa only [classicalHillGapSquareDisc,ofReal_mul,ofReal_natCast] using ht.1)
    simpa only [ofReal_mul,ofReal_natCast] using h
  have hnorm (t : ℂ × Curve ℂ) (ht : t ∈ classicalHillGapSquareDisc n r ×ˢ (Vt ∩ Vs)) :
      ‖D t-1‖ < delta := by
    have h := htrace t.2 ht.2.1 1 (by constructor <;> norm_num) n
      ((le_max_left Nt Ns).trans hn) (Complex.sqrt t.1) (hfreq t ht)
    simpa only [D,ofReal_one,one_smul,sqrt_square] using h
  have hDW (t : ℂ × Curve ℂ) (ht : t ∈ classicalHillGapSquareDisc n r ×ˢ (Vt ∩ Vs)) : D t ∈ W := by
    apply hsmallW
    simpa only [mem_ball,dist_eq_norm] using (hnorm t ht).trans_le hdeltaeta
  refine ⟨K,?_,?_,?_,?_,?_⟩
  · intro t ht
    exact (hG (D t) (hDW t ht)).comp (hD t (mem_univ _))
  · intro t ht
    have h := hsmallG (by simpa only [dist_eq_norm] using (hnorm t ht).trans_le hdeltaG)
    simpa only [K,Function.comp_def,hG1,dist_zero_right] using h
  · intro t ht
    exact (hright (D t) (hDW t ht)).2
  · intro t ht
    have hsign : ((-1 : ℂ)^(n : ℕ))^2 = 1 := by rw [pow_two,← mul_pow]; simp
    constructor
    · intro hz
      have hrel : squaredCosh (K t) = D t := (hright (D t) (hDW t ht)).2
      rw [hz,squaredCosh_zero] at hrel
      change (1 : ℂ) = (-1 : ℂ)^(n : ℕ)*classicalHillDiscriminant t.2 t.1/2 at hrel
      have hvalue : classicalHillDiscriminant t.2 t.1 = 2*(-1 : ℂ)^(n : ℕ) := by
        linear_combination -2*(-1 : ℂ)^(n : ℕ)*hrel-classicalHillDiscriminant t.2 t.1*hsign
      change classicalHillDiscriminant t.2 t.1^2-4 = 0
      rw [hvalue,mul_pow,hsign]
      norm_num
    · intro hz
      have hroot : D t^2 = (1 : ℂ)^2 := by
        have hzero : classicalHillDiscriminant t.2 t.1^2 = 4 := sub_eq_zero.mp hz
        dsimp only [D]
        rw [div_pow,mul_pow,hsign,hzero]
        norm_num
      rcases eq_or_eq_neg_of_sq_eq_sq _ _ hroot with he | he
      · change G (D t) = 0
        rw [he,hG1]
      · have h := hnorm t ht
        rw [he] at h
        norm_num at h
        linarith
  · intro t ht
    have hF : |(classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi).im| < Real.pi/2 := by
      have hz : Complex.sqrt t.1 ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) :=
        closedBall_subset_closedBall hrpi (hfreq t ht.1)
      have h := hstrip t.2 ht.1.2.2 n ((le_max_right Nt Ns).trans hn) (Complex.sqrt t.1) hz
        (by simpa only [sqrt_square] using ht.2)
      simpa only [sqrt_square] using h
    have hcosh : cosh (classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi) = D t := by
      rw [cosh_add_hill_index]
      have h := (classicalHillContinuedPrimitive_trace t ht.2).1
      dsimp only [D]
      linear_combination (-1 : ℂ)^(n : ℕ)*h/2
    have hnormF := hcontrol _ hF (by rw [hcosh]; exact (hnorm t ht.1).trans_le hdeltad)
    have hFU : (classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2 ∈ U := by
      exact hsmallU (by simpa only [mem_ball,dist_zero_right] using hnormF)
    change G (D t) = _
    rw [← hcosh,← squaredCosh_sq]
    exact hleft _ hFU

/-- Unit-bounded version of the arbitrarily small whole-disc square
construction, retained for the endpoint deflation and contour bounds. -/
theorem exists_classicalHill_whole_disc_squares (q : Curve ℂ) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (Curve ℂ),
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × Curve ℂ → ℂ,
        AnalyticOnNhd ℂ K (classicalHillGapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V, ‖K t‖ < 1) ∧
        (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V,
          squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*classicalHillDiscriminant t.2 t.1/2) ∧
        (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V,
          K t = 0 ↔ classicalHillRadicand t = 0) ∧
        ∀ t ∈ (classicalHillGapSquareDisc n r ×ˢ V) ∩ classicalHillContinuationDomain,
          K t = (classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2 :=
  exists_classicalHill_whole_disc_small_squares q 1 (by norm_num)

/-- The analytic energy discs contain the whole actual high gaps, with
one complex neighborhood and cutoff chosen before every pair. One square
per index covers both endpoints and the complete straight complex gap
segment, including a collapsed pair. No endpoint gluing is assumed. -/
theorem exists_classicalHill_whole_gap_squares (q : Curve ℂ) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (Curve ℂ),
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × Curve ℂ → ℂ,
        AnalyticOnNhd ℂ K (classicalHillGapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V, ‖K t‖ < 1) ∧
        (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V,
          squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*classicalHillDiscriminant t.2 t.1/2) ∧
        (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V,
          K t = 0 ↔ classicalHillRadicand t = 0) ∧
        (∀ t ∈ (classicalHillGapSquareDisc n r ×ˢ V) ∩ classicalHillContinuationDomain,
          K t = (classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
        ∀ a ∈ V, ∃ l u : ℂ, ClassicalHillHighGapPair a n l u ∧
          segment ℝ l u ⊆ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) := by
  obtain ⟨r,Nk,Vk,hr,hrpi,hNk,hVk,hqk,hfamily⟩ := exists_classicalHill_whole_disc_squares q
  obtain ⟨Nr,Vr,_,hVr,hqr,hcover⟩ := exists_classicalHill_small_gap_coverage q (r/4)
    (by positivity) (by linarith)
  obtain ⟨Nc,Vc,_,hVc,hqc,hcount⟩ := exists_classicalHillCounting_near_compact {q} isCompact_singleton
  let N := max Nk (max Nr (Nc+1))
  let V := Vk ∩ (Vr ∩ Vc)
  have hqV : q ∈ V := ⟨hqk,hqr,hqc (mem_singleton q)⟩
  refine ⟨r,N,V,hr,hrpi,hNk.trans_le (le_max_left _ _),hVk.inter (hVr.inter hVc),hqV,?_⟩
  intro n hn
  have hnk : Nk ≤ (n : ℕ) := (le_max_left Nk _).trans hn
  have hnr : Nr ≤ (n : ℕ) := (le_max_left Nr _).trans ((le_max_right Nk _).trans hn)
  have hnc : Nc < (n : ℕ) := by dsimp only [N] at hn; omega
  obtain ⟨K,hK,hbound,hrel,hzero,hmatch⟩ := hfamily n hnk
  have hsub : classicalHillGapSquareDisc n r ×ˢ V ⊆ classicalHillGapSquareDisc n r ×ˢ Vk :=
    fun _ ht => ⟨ht.1,ht.2.1⟩
  refine ⟨K,hK.mono hsub,fun t ht => hbound t (hsub ht),fun t ht => hrel t (hsub ht),
    fun t ht => hzero t (hsub ht),fun t ht => hmatch t ⟨hsub ht.1,ht.2⟩,?_⟩
  intro a ha
  obtain ⟨l,u,hpair⟩ := exists_classicalHillHighGapPair_of_counting a Nc
    (hcount a ha.2.2 Nc le_rfl) n hnc
  have hrc : r ≤ Real.pi*(n : ℕ) := by
    have hnreal : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
    nlinarith [Real.pi_pos]
  have endpoint_mem (lambda : ℂ) (hlambda : lambda ∈ classicalHillHighEnergyRegion n)
      (hz : classicalHillRadicand (lambda,a) = 0) :
      lambda ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) := by
    obtain ⟨z,hzball,hzsq⟩ := hlambda
    change z^2 = lambda at hzsq
    have hsmall := hcover a ha.2.1 (n : ℕ) (by simpa only [Int.natAbs_natCast] using hnr) z
      (by simpa only [Int.cast_natCast] using ball_subset_closedBall hzball)
      (by simpa only [hzsq] using hz)
    have h := square_mem_energy_ball_of_small_frequency (Real.pi*(n : ℕ)) r (by positivity) hr hrc z
      (by simpa only [ofReal_mul,ofReal_natCast,Int.cast_natCast] using hsmall)
    simpa only [hzsq,ofReal_mul,ofReal_natCast] using h
  refine ⟨l,u,hpair,?_⟩
  exact (convex_ball _ _).segment_subset
    (endpoint_mem l hpair.left_mem hpair.left_zero) (endpoint_mem u hpair.right_mem hpair.right_zero)

end NLS.KdV
