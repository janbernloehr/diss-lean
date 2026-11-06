import NLS.KdV.HillL2GapBoundaryValues
import NLS.ComplexAnalysis.RealCutCircleIntegral
import NLS.ComplexAnalysis.AnalyticCutContour

/-! # Actual high Hill contours collapsed onto their real gaps

The filled shifted-primitive square supplies a uniform bound near the
whole cut. The circle deformation and dominated-convergence theorem
therefore apply to the actual source-normalized primitive, with the
clockwise/upper-minus-lower signs and the factor two kept explicit.
-/

noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillL2NormalizedCutPrimitive.circleIntegral_shifted_eq_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8 * ‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hgap : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F) (m : ℕ) :
    (∮ z in C((freeHillValue n : ℂ), 3 * (n : ℝ) / 4),
      z ^ m * (F z + I * (n : ℂ) * Real.pi)) =
      -2 * ∫ x in p.left..p.right,
        (x : ℂ) ^ m * (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let c := (p.left + p.right) / 2
  let d := (p.right - p.left) / 2
  let r := d + (n : ℝ) / 8
  let s := d + (n : ℝ) / 4
  let Ω := ball (freeHillValue n : ℂ) (7 * (n : ℝ) / 8)
  let K := segment ℝ (p.left : ℂ) p.right
  let f : ℂ → ℂ := fun z => z ^ m * (F z + I * (n : ℂ) * Real.pi)
  let φ : ℝ → ℂ := fun x =>
    (x : ℂ) ^ m * (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ)
  have hd : 0 < d := by dsimp [d]; linarith [lt_of_le_of_ne p.ordered hgap]
  have hl : c - d = p.left := by dsimp [c, d]; ring
  have hu : c + d = p.right := by dsimp [c, d]; ring
  have hloc := p.localization q hq n (by omega) hcut
  have hcenter : |c - freeHillValue n| + d ≤ 4 * ‖q‖ := by
    have he : |c - freeHillValue n| ≤ 4 * ‖q‖ - d := by
      rw [abs_le]
      constructor <;> dsimp [c, d] <;>
        linarith [(abs_le.mp hloc.1).1, (abs_le.mp hloc.2).2]
    linarith
  have hcdist : dist (c : ℂ) (freeHillValue n : ℂ) = |c - freeHillValue n| := by
    simp only [dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
  have hΩ : closedBall (c : ℂ) s ⊆ Ω := by
    intro z hz
    have ht := dist_triangle z (c : ℂ) (freeHillValue n : ℂ)
    rw [hcdist] at ht
    have hz' := mem_closedBall.mp hz
    dsimp [Ω]
    rw [mem_ball]
    dsimp [s] at hz'
    linarith
  have hrs : r < s := by dsimp [r, s]; linarith
  have hsmall : closedBall (c : ℂ) r ⊆ Ω :=
    (closedBall_subset_closedBall hrs.le).trans hΩ
  have hmid : ball (c : ℂ) s \ K ⊆ Ω \ K :=
    fun z hz => ⟨hΩ (ball_subset_closedBall hz.1), hz.2⟩
  have hf : AnalyticOnNhd ℂ f (Ω \ K) :=
    (analyticOnNhd_id.pow m).mul (h.analytic.add analyticOnNhd_const)
  obtain ⟨hX, hXeq, _, _⟩ := h.square_extension q hq hreal n hn hcut p hgap R F
  let X := hillL2CutPrimitiveSquare n p.left p.right F
  obtain ⟨M, hM, hbound⟩ := exists_norm_bound_of_continuous_square_on_compact f
    (fun z => (z ^ m) ^ 2 * X z) (closedBall (c : ℂ) r) K (isCompact_closedBall _ _)
    (((analyticOnNhd_id.pow m).pow 2).mul (hX.mono hsmall)).continuousOn
    (by
      intro z hz
      change (z ^ m * (F z + I * (n : ℂ) * Real.pi)) ^ 2 = (z ^ m) ^ 2 * X z
      rw [mul_pow]
      exact congrArg ((z ^ m) ^ 2 * ·) (hXeq ⟨hsmall hz.1, hz.2⟩).symm)
  obtain ⟨p', hlabelL, hlabelR⟩ := hillRealLabels_high_pair q hq hreal n hn hcut
  have hp := p.endpoints_unique _ n (by omega) p'
  have hlabelsL : hillRealLabels q hq hreal (2 * n - 1) = p.left :=
    hlabelL.trans hp.1.symm
  have hlabelsR : hillRealLabels q hq hreal (2 * n) = p.right :=
    hlabelR.trans hp.2.symm
  have hprofile := continuousOn_hillRealGapProfile q hq hreal n (by omega)
  rw [hlabelsL, hlabelsR] at hprofile
  have hφ : ContinuousOn φ (Icc p.left p.right) :=
    (Complex.continuous_ofReal.pow m).continuousOn.mul
      (Complex.continuous_ofReal.comp_continuousOn hprofile)
  have hK : segment ℝ ((c - d : ℝ) : ℂ) ((c + d : ℝ) : ℂ) = K := by rw [hl, hu]
  have hmidIntegral : (∮ z in C((c : ℂ), r), f z) =
      -(∫ x in p.left..p.right, φ x - -φ x) := by
    have he := circleIntegral_eq_neg_real_cut_jump f (fun x => -φ x) φ c d r s M
      hd (by dsimp [r]; linarith) hrs hM
      (by rw [hK]; exact hf.mono hmid)
      (by rw [hK]; exact hbound)
      (by rw [hl, hu]; exact hφ.neg) (by rw [hl, hu]; exact hφ)
      (by
        intro x hx
        rw [hl, hu] at hx
        have hb := (h.gap_boundary_values q hq hreal n hn hcut p hgap R F x hx).2
        have hpow := (continuousAt_id.pow m).tendsto.mono_left
          (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}) (a := (x : ℂ)))
        simpa only [f, φ, mul_neg, Pi.pow_apply, id_eq] using hpow.mul hb)
      (by
        intro x hx
        rw [hl, hu] at hx
        exact ((continuousAt_id.pow m).tendsto.mono_left nhdsWithin_le_nhds).mul
          (h.gap_boundary_values q hq hreal n hn hcut p hgap R F x hx).1)
    simpa only [hl, hu] using he
  have hnest : closedBall (c : ℂ) r ⊆
      closedBall (freeHillValue n : ℂ) (3 * (n : ℝ) / 4) := by
    intro z hz
    have ht := dist_triangle z (c : ℂ) (freeHillValue n : ℂ)
    rw [hcdist] at ht
    have hz' := mem_closedBall.mp hz
    rw [mem_closedBall]
    dsimp [r] at hz'
    linarith
  have hKmid : K ⊆ ball (c : ℂ) r := by
    apply (convex_ball _ _).segment_subset
    · rw [← hl]
      simp only [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
      rw [show c - d - c = -d by ring, abs_neg, abs_of_pos hd]
      dsimp [r]
      linarith
    · rw [← hu]
      simp only [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
      rw [show c + d - c = d by ring, abs_of_pos hd]
      dsimp [r]
      linarith
  have hKouter : K ⊆ ball (freeHillValue n : ℂ) (3 * (n : ℝ) / 4) := by
    apply (convex_ball _ _).segment_subset
    · rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
      linarith [hloc.1]
    · rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
      linarith [hloc.2]
  have hcircles := circleIntegral_eq_of_analytic_cut_nestedCircles f Ω K hf
    (c : ℂ) (freeHillValue n : ℂ) r (3 * (n : ℝ) / 4)
    (by dsimp [r]; positivity) (by positivity) hKmid hKouter hnest
    (closedBall_subset_ball (by linarith : 3 * (n : ℝ) / 4 < 7 * (n : ℝ) / 8))
  calc
    _ = ∮ z in C((c : ℂ), r), f z := hcircles.symm
    _ = -(∫ x in p.left..p.right, φ x - -φ x) := hmidIntegral
    _ = -2 * ∫ x in p.left..p.right, φ x := by
      simp_rw [show ∀ x, φ x - -φ x = (2 : ℂ) * φ x by intro x; ring]
      rw [intervalIntegral.integral_const_mul]
      ring

/-- The index shift contributes a polynomial, whose circle integral is zero. -/
theorem HillL2NormalizedCutPrimitive.circleIntegral_shifted_eq
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8 * ‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F) (m : ℕ) :
    (∮ z in C((freeHillValue n : ℂ), 3 * (n : ℝ) / 4),
      z ^ m * (F z + I * (n : ℂ) * Real.pi)) =
      ∮ z in C((freeHillValue n : ℂ), 3 * (n : ℝ) / 4), z ^ m * F z := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hloc := p.localization q hq n hn hcut
  have hK : segment ℝ (p.left : ℂ) p.right ⊆
      ball (freeHillValue n : ℂ) (3 * (n : ℝ) / 4) := by
    apply (convex_ball _ _).segment_subset
    · rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
      linarith [hloc.1]
    · rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
      linarith [hloc.2]
  have hcircle : sphere (freeHillValue n : ℂ) (3 * (n : ℝ) / 4) ⊆
      ball (freeHillValue n : ℂ) (7 * (n : ℝ) / 8) \ segment ℝ (p.left : ℂ) p.right := by
    intro z hz
    exact ⟨by rw [mem_ball]; linarith [mem_sphere.mp hz],
      fun hk => sphere_disjoint_ball.le_bot ⟨hz, hK hk⟩⟩
  have hiF : CircleIntegrable (fun z => z ^ m * F z)
      (freeHillValue n : ℂ) (3 * (n : ℝ) / 4) :=
    ((analyticOnNhd_id.pow m).mul (h.analytic.mono hcircle)).continuousOn.circleIntegrable
      (by positivity)
  let g : ℂ → ℂ := fun z => z ^ m * (I * (n : ℂ) * Real.pi)
  have hg : AnalyticOnNhd ℂ g univ := (analyticOnNhd_id.pow m).mul analyticOnNhd_const
  have hzero : (∮ z in C((freeHillValue n : ℂ), 3 * (n : ℝ) / 4), g z) = 0 :=
    (DiffContOnCl.mk_ball (hg.differentiableOn.mono (subset_univ _))
      hg.continuous.continuousOn).circleIntegral_eq_zero (by positivity)
  simp_rw [mul_add]
  rw [circleIntegral.integral_add hiF
    (hg.continuous.continuousOn.circleIntegrable (by positivity)), hzero, add_zero]

end NLS.KdV
