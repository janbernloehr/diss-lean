import NLS.ZakharovShabat.AppendixDExteriorAsymptotic
import NLS.ZakharovShabat.CentralCircleThresholds
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! # The circle-decay hypothesis and vanishing Cauchy error in E.1 -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal supremum in the hypothesis of E.1. -/
def appendixESineCircleSup (f : ℂ → ℂ) (N : ℕ) : ℝ :=
  sSup ((fun z => ‖f z/sin z‖) '' sphere (0:ℂ) (centralCircleRadius N))

/-- Sine is nonzero on every source interpolation circle. -/
theorem sin_ne_zero_on_centralCircle (N : ℕ) (z : ℂ)
    (hz : z ∈ sphere (0:ℂ) (centralCircleRadius N)) : sin z ≠ 0 := by
  apply sin_ne_zero_of_notMem_freeLattice
  apply notMem_freeLattice_of_separated (by positivity : 0 < Real.pi/4)
  intro m
  have h := centralCircle_lattice_gap N hz m
  linarith [Real.pi_pos]

/-- The literal supremum bounds every circle value; finiteness is derived from analyticity. -/
theorem norm_sineQuotient_le_appendixESineCircleSup (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (N : ℕ) (z : ℂ)
    (hz : z ∈ sphere (0:ℂ) (centralCircleRadius N)) :
    ‖f z/sin z‖ ≤ appendixESineCircleSup f N := by
  have hc : ContinuousOn (fun z => ‖f z/sin z‖) (sphere (0:ℂ) (centralCircleRadius N)) := by
    apply ContinuousOn.norm
    apply ContinuousOn.div (hf.continuousOn.mono (subset_univ _)) continuous_sin.continuousOn
    exact sin_ne_zero_on_centralCircle N
  exact le_csSup ((isCompact_sphere (0:ℂ) (centralCircleRadius N)).bddAbove_image hc)
    (mem_image_of_mem _ hz)

/-- The printed supremum limit supplies the uniform epsilon formulation. -/
theorem eventually_sineQuotient_small_of_sup_tendsto (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hdecay : Tendsto (appendixESineCircleSup f) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ z ∈ sphere (0:ℂ) (centralCircleRadius N), ‖f z/sin z‖ ≤ ε := by
  filter_upwards [Metric.tendsto_nhds.mp hdecay ε hε] with N hN z hz
  have hb : |appendixESineCircleSup f N| < ε := by simpa only [Real.dist_eq,sub_zero] using hN
  exact ((norm_sineQuotient_le_appendixESineCircleSup f hf N z hz).trans
    (le_abs_self _)).trans hb.le

/-- The uniform-epsilon formulation also implies the printed literal supremum limit. -/
theorem tendsto_appendixESineCircleSup_of_circle_decay (f : ℂ → ℂ)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius N), ‖f z/sin z‖ ≤ ε) :
    Tendsto (appendixESineCircleSup f) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hdecay (ε/2) (half_pos hε)] with N hN
  let S := (fun z => ‖f z/sin z‖) '' sphere (0:ℂ) (centralCircleRadius N)
  have hne : S.Nonempty :=
    (NormedSpace.sphere_nonempty.mpr (centralCircleRadius_pos N).le).image _
  have hbound : ∀ v ∈ S, v ≤ ε/2 := by
    rintro v ⟨z,hz,rfl⟩
    exact hN z hz
  have hnonneg : 0 ≤ sSup S := by
    obtain ⟨v,z,hz,rfl⟩ := hne
    exact (norm_nonneg _).trans (le_csSup ⟨ε/2,hbound⟩ (mem_image_of_mem _ hz))
  change dist (sSup S) 0 < ε
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnonneg]
  exact (csSup_le hne hbound).trans_lt (half_lt_self hε)

/-- D.5 makes the full product uniformly nonzero relative to sine on large circles. -/
theorem eventually_appendixDProduct_circle_lower (hp : p ≠ ⊤) (a : Coeff p) :
    ∀ᶠ N : ℕ in atTop, ∀ z ∈ sphere (0:ℂ) (centralCircleRadius N),
      appendixDProduct (z,a) ≠ 0 ∧ (1/2:ℝ) ≤ ‖appendixDProduct (z,a)/sin z‖ := by
  obtain ⟨η,hη,R,_,hR⟩ := exists_local_appendixDProduct_div_sin_bound hp a (by norm_num : 0 < (1/2:ℝ))
  apply eventually_centralCircle_of_separated_threshold
  refine ⟨R,fun z hz hsep => ?_⟩
  have hb := hR a (by simpa using hη) z hsep hz
  have htri := norm_sub_norm_le (1:ℂ) (appendixDProduct (z,a)/sin z)
  rw [norm_one,norm_sub_rev] at htri
  have hlower : (1/2:ℝ) ≤ ‖appendixDProduct (z,a)/sin z‖ := by linarith
  refine ⟨?_,hlower⟩
  intro he
  simp only [he,zero_div,norm_zero] at hlower
  norm_num at hlower

/-- The source hypothesis transfers to decay of the quotient by the displaced product. -/
theorem eventually_appendixEQuotient_small (hp : p ≠ ⊤) (a : Coeff p)
    (f : ℂ → ℂ)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius N), ‖f z/sin z‖ ≤ ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ z ∈ sphere (0:ℂ) (centralCircleRadius N),
      ‖f z/appendixDProduct (z,a)‖ ≤ ε := by
  filter_upwards [eventually_appendixDProduct_circle_lower hp a,hdecay (ε/2) (half_pos hε)]
    with N hN hsmall z hz
  have hlow := (hN z hz).2
  have hs := sin_ne_zero_on_centralCircle N z hz
  have he : f z/appendixDProduct (z,a) = (f z/sin z)/(appendixDProduct (z,a)/sin z) := by
    field_simp
  rw [he,norm_div]
  calc
    _ ≤ (ε/2)/(1/2) := (div_le_div_of_nonneg_right (hsmall z hz) (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left (by positivity) (by norm_num) hlow)
    _ = ε := by ring

/-- The outer Cauchy integrals vanish uniformly on bounded evaluation sets.
Only uniform quotient decay is needed, with no rate of decay assumed. -/
theorem eventually_appendixE_outerCauchy_small (hp : p ≠ ⊤) (a : Coeff p)
    (f : ℂ → ℂ)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius N), ‖f z/sin z‖ ≤ ε)
    (L : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ w : ℂ, ‖w‖ ≤ L →
      ‖∮ z in C(0,centralCircleRadius N), f z/appendixDProduct (z,a)/(z-w)‖ < ε := by
  let δ := ε/(8*Real.pi)
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [eventually_appendixEQuotient_small hp a f hdecay hδ,
    tendsto_centralCircleRadius_atTop.eventually (eventually_gt_atTop (2*L))] with N hN hlarge w hw
  let R := centralCircleRadius N
  have hR : 0 < R := centralCircleRadius_pos N
  have hb (z : ℂ) (hz : z ∈ sphere (0:ℂ) R) :
      ‖f z/appendixDProduct (z,a)/(z-w)‖ ≤ δ/(R/2) := by
    have hzNorm : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
    have htri := norm_add_le (z-w) w
    rw [sub_add_cancel,hzNorm] at htri
    have hdist : R/2 ≤ ‖z-w‖ := by change 2*L < R at hlarge; linarith
    rw [norm_div]
    exact (div_le_div_of_nonneg_right (hN z hz) (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left hδ.le (half_pos hR) hdist)
  have hi := circleIntegral.norm_integral_le_of_norm_le_const hR.le hb
  have he : 2*Real.pi*R*(δ/(R/2)) = ε/2 := by
    dsimp only [δ]
    field_simp
    ring
  rw [he] at hi
  exact hi.trans_lt (half_lt_self hε)

end NLS.ZakharovShabat
