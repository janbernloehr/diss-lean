import NLS.KdV.HillRealGapUnitBound
import NLS.KdV.HillL2GapQuotientAsymptotics

/-! # Eventual quadratic bounds for the actual real Hill actions

The shared complex L2 charts agree with the actual real normalized
squares. Their uniform free-unit estimate gives a quadratic gap bound
for every sufficiently high real action. The cutoff depends on the
potential; this is not the explicit norm estimate in Theorem 3.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillRealGapIntegral_quadratic_tail_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (n : ℝ) * hillRealGapIntegral q hq hr n 0 ≤
        (hillRealLabels q hq hr (2 * n) - hillRealLabels q hq hr (2 * n - 1)) ^ 2 := by
  obtain ⟨r, hrpos, hrpi, hfamily⟩ := exists_hillL2_near_free_gap_units (SpectralWeight.one.toCoeff q)
  obtain ⟨N, V, _, _, hqV, hcharts⟩ := hfamily (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨A, hA⟩ := exists_nat_ge (8 * ‖q‖)
  refine ⟨max 2 (max N A), le_max_left _ _, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnN : N ≤ n := (le_max_left N A).trans ((le_max_right 2 _).trans hn)
  have hnA : A ≤ n := (le_max_right N A).trans ((le_max_right 2 _).trans hn)
  have hcut : 8 * ‖q‖ ≤ (n : ℝ) := hA.trans (by exact_mod_cast hnA)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let ν : ℕ+ := ⟨n, by omega⟩
  obtain ⟨p, hlabelL, hlabelR⟩ := hillRealLabels_high_pair q hq hr n hn2 hcut
  by_cases hclosed : p.left = p.right
  · have hc : hillRealLabels q hq hr (2 * n - 1) = hillRealLabels q hq hr (2 * n) :=
      hlabelL.trans (hclosed.trans hlabelR.symm)
    rw [hillRealGapIntegral_closed q hq hr n 0 hc, hc, sub_self]
    simp
  obtain ⟨K, hK, htrace, _, hpairs⟩ := hcharts ν hnN
  obtain ⟨l, u, H, hpair, hl, hu, hH, hunit⟩ := hpairs _ hqV
  have horder := hpair.eq_or_swap_real p hclosed
  let E : ℂ := ((Real.pi : ℂ) * (n : ℂ)) ^ 2
  let ρ : ℝ := Real.pi * (n : ℝ) * r
  let Ω := ball (freeHillValue n : ℂ) (7 * (n : ℝ) / 8)
  let U := ball E ρ ∩ Ω
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  change l ∈ ball E ((1 / 2 : ℝ) / 64 * ρ) at hl
  change u ∈ ball E ((1 / 2 : ℝ) / 64 * ρ) at hu
  have hscale : (1 / 2 : ℝ) / 64 * ρ = ρ / 128 := by ring
  rw [hscale] at hl hu
  have hL : (p.left : ℂ) ∈ ball E (ρ / 128) := by
    rcases horder with ⟨hl', _⟩ | ⟨_, hu'⟩
    · simpa only [hl'] using hl
    · simpa only [hu'] using hu
  have hR : (p.right : ℂ) ∈ ball E (ρ / 128) := by
    rcases horder with ⟨_, hu'⟩ | ⟨hl', _⟩
    · simpa only [hu'] using hu
    · simpa only [hl'] using hl
  have hdisc (z : ℂ) (hz : z ∈ closedBall E ρ) : z ∈ hillL2GapSquareDisc ν r := by
    change z ∈ closedBall E ρ
    exact hz
  have hKe : AnalyticOnNhd ℂ (fun z => K (z, SpectralWeight.one.toCoeff q)) (closedBall E ρ) := by
    intro z hz
    exact (hK (z, SpectralWeight.one.toCoeff q) ⟨hdisc z hz, hqV⟩).comp
      (f := fun z : ℂ => (z, SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  have hfactor (z : ℂ) (hz : z ∈ closedBall E ρ) :
      K (z, SpectralWeight.one.toCoeff q) =
        (z - p.left) * (z - p.right) * H z ^ 2 := by
    have he := (hunit z (hdisc z hz)).2.2.1
    rcases horder with ⟨hl', hu'⟩ | ⟨hl', hu'⟩
    · simpa only [hl', hu'] using he
    · rw [hl', hu'] at he
      rw [he]
      ring
  have hloc := p.localization q hq n (by omega) hcut
  have hLΩ : (p.left : ℂ) ∈ Ω := by
    rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    linarith [hloc.1]
  have hRΩ : (p.right : ℂ) ∈ Ω := by
    rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    linarith [hloc.2]
  have hLU : (p.left : ℂ) ∈ U := ⟨ball_subset_ball (by linarith) hL, hLΩ⟩
  have hRU : (p.right : ℂ) ∈ U := ⟨ball_subset_ball (by linarith) hR, hRΩ⟩
  have hUopen : IsOpen U := isOpen_ball.inter isOpen_ball
  have hUconv : Convex ℝ U := (convex_ball _ _).inter (convex_ball _ _)
  obtain ⟨R, F, h⟩ := p.exists_normalized_source_cut_primitive q hq n (by omega) hcut
  have hmatch := h.square_eq_on_of_trace_and_zero q hq hr n hn2 hcut p hclosed R F
    (fun z => K (z, SpectralWeight.one.toCoeff q)) U hUopen hUconv.isPreconnected
    (fun _ hz => hz.2) hLU (hKe.mono (fun _ hz => ball_subset_closedBall hz.1))
    (by rw [hfactor _ (ball_subset_closedBall hLU.1)]; simp)
    (fun z hz => htrace (z, SpectralWeight.one.toCoeff q) ⟨hdisc z (ball_subset_closedBall hz.1), hqV⟩)
  have hrealU (x : ℝ) (hx : x ∈ Icc p.left p.right) : (x : ℂ) ∈ U := by
    apply hUconv.segment_subset hLU hRU
    have hxseg : x ∈ segment ℝ p.left p.right := by
      simpa only [segment_eq_Icc p.ordered] using hx
    have himg := mem_image_of_mem Complex.ofRealCLM.toLinearMap.toAffineMap hxseg
    simpa only [image_segment] using! himg
  have hHbound (z : ℂ) (hz : z ∈ closedBall E ρ) : ‖H z‖ ≤ 1 / (n : ℝ) := by
    have hb := (hunit z (hdisc z hz)).2.2.2
    have hnorm : ‖I / (2 * ((Real.pi : ℂ) * (n : ℂ)))‖ = 1 / (2 * Real.pi * (n : ℝ)) := by
      simp [abs_of_pos Real.pi_pos, mul_assoc]
    calc
      _ ≤ ‖H z - I / (2 * ((Real.pi : ℂ) * (n : ℂ)))‖ +
          ‖I / (2 * ((Real.pi : ℂ) * (n : ℂ)))‖ := norm_le_norm_sub_add _ _
      _ ≤ (1 / 2) / (2 * Real.pi * (n : ℝ)) + 1 / (2 * Real.pi * (n : ℝ)) := by
        rw [hnorm]
        exact add_le_add hb le_rfl
      _ ≤ 1 / (n : ℝ) := by
        field_simp
        nlinarith [Real.pi_gt_three]
  have hi := h.gapIntegral_le_of_unit_bound q hq hr n hn2 hcut p hclosed R F H
    (fun x hx => (hmatch (hrealU x ⟨hx.1.le, hx.2.le⟩)).symm.trans
      (hfactor x (ball_subset_closedBall (hrealU x ⟨hx.1.le, hx.2.le⟩).1)))
    (fun x hx => hHbound x (ball_subset_closedBall (hrealU x ⟨hx.1.le, hx.2.le⟩).1))
  simpa only [hlabelL, hlabelR] using hi

end NLS.KdV
