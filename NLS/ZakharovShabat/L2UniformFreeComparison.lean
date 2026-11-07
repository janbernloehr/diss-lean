import NLS.ZakharovShabat.L2StripStability
import NLS.ZakharovShabat.PhysicalH1Density
import NLS.ZakharovShabat.ClassicalSobolevRemainderBound

/-! Uniform high-frequency free comparison of the ACTUAL full physical
L2 fundamental solution, in the closed-interval uniform curve norm. -/
noncomputable section
open Set Metric Complex
open NLS.LinearVolterra NLS.Fourier
namespace NLS.ZakharovShabat

/-- Every physical L2 potential has ONE norm-open neighborhood and ONE
frequency threshold making the ACTUAL full fundamental solution arbitrarily
close to the free one, uniformly on the full closed time interval, horizontal
frequency strip, nearby complex potentials and unit initial vectors.
No H1 regularity is assumed of the source or neighboring potentials. -/
theorem exists_uniform_l2SolutionCurve_sub_free_small (u : IntervalPairL2)
    (H : ℝ) {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ T : ℝ, ∃ U : Set IntervalPairL2,
      0 < T ∧ IsOpen U ∧ u ∈ U ∧
      ∀ w ∈ U, ∀ z : ℂ, |z.im| ≤ H → T ≤ ‖z‖ →
        ∀ v : ℂ × ℂ, ‖v‖ ≤ 1 →
          ‖l2SolutionCurve w z v-l2SolutionCurve 0 z v‖ < epsilon := by
  let R := ‖u‖+1
  let K := Real.exp (2*H+2*R)
  have hK : 0 < K := Real.exp_pos _
  let delta := min (1/4) (epsilon/(8*K))
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hd1 : delta ≤ 1/4 := min_le_left _ _
  have hde : 8*K*delta ≤ epsilon := by
    have hh := min_le_right (1/4:ℝ) (epsilon/(8*K))
    have hm := (le_div_iff₀ (by positivity : 0 < 8*K)).mp hh
    nlinarith
  obtain ⟨a,ha⟩ := Metric.denseRange_iff.mp denseRange_sourcePeriodicH1L2Class u delta hd
  let G := sourcePeriodicH1L2Class a
  have hGu : ‖G-u‖ < delta := by simpa only [dist_eq_norm,norm_sub_rev] using ha
  have hGR : ‖G‖ ≤ R := by
    have hh := norm_add_le (G-u) u
    rw [sub_add_cancel] at hh
    dsimp [R]
    linarith
  let c := (Coeff.periodDoubleSobolev a.1,Coeff.periodDoubleSobolev a.2)
  let C := (4+Real.pi)*‖c‖*Real.exp (4*‖c‖+H)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hfree (z : ℂ) (hz : z ≠ 0) (hH : |z.im| ≤ H) (v : ℂ × ℂ) :
      ‖l2SolutionCurve G z v-l2SolutionCurve 0 z v‖ ≤ C/‖z‖*‖v‖ := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    change ‖l2SolutionCurve (sourcePeriodicH1L2Class a) z v t-l2SolutionCurve 0 z v t‖ ≤ _
    rw [sourcePeriodicH1L2Class_eq_classical,l2SolutionCurve_of_continuous,
      classicalSolutionCurve_apply,l2SolutionCurve_free]
    have hb := norm_classicalSolutionRemainder_sobolev_strip_le ‖c‖ H c le_rfl z hz hH v t
    change ‖classicalSolution (classicalSobolevPotential c) z v t-classicalFreeVector z v t‖ ≤ _ at hb
    exact hb.trans_eq (by dsimp [C]; ring)
  let T := 2*C/epsilon+1
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨T,ball u delta,hT,isOpen_ball,mem_ball_self hd,?_⟩
  intro w hw z hH hz v hv
  have hwu : ‖w-u‖ < delta := by simpa only [mem_ball,dist_eq_norm] using hw
  have hwR : ‖w‖ ≤ R := by
    have hh := norm_add_le (w-u) u
    rw [sub_add_cancel] at hh
    dsimp [R]
    linarith
  have hwG : ‖w-G‖ < 2*delta := by
    have hh := norm_sub_le (w-u) (G-u)
    rw [sub_sub_sub_cancel_right] at hh
    linarith
  have hzpos : 0 < ‖z‖ := hT.trans_le hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  have hdecay : C/‖z‖ < epsilon/2 := by
    apply (div_lt_iff₀ hzpos).mpr
    have hh : 2*C/epsilon < ‖z‖ := by dsimp [T] at hz; linarith
    have hm := (div_lt_iff₀ heps).mp hh
    nlinarith
  have hst := norm_l2SolutionCurve_sub_le_of_strip_bounds w G z v R H hwR hGR hH
  have hst' : ‖l2SolutionCurve w z v-l2SolutionCurve G z v‖ < epsilon/2 := by
    have hb : ‖v‖*K ≤ K := mul_le_of_le_one_left hK.le hv
    have hh : ‖v‖*K*‖w-G‖ ≤ K*(2*delta) :=
      mul_le_mul hb hwG.le (norm_nonneg _) hK.le
    dsimp only [K] at hb hh
    linarith
  have hfr : ‖l2SolutionCurve G z v-l2SolutionCurve 0 z v‖ < epsilon/2 := by
    exact ((hfree z hz0 hH v).trans (mul_le_of_le_one_right (by positivity) hv)).trans_lt hdecay
  have htri := norm_add_le (l2SolutionCurve w z v-l2SolutionCurve G z v)
    (l2SolutionCurve G z v-l2SolutionCurve 0 z v)
  rw [sub_add_sub_cancel] at htri
  exact htri.trans_lt (by linarith)

end NLS.ZakharovShabat
