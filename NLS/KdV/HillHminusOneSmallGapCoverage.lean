import NLS.KdV.HillHminusOneDiscAsymptotics
import NLS.KdV.HillHminusOneSourcePrimitive
import NLS.ZakharovShabat.FreeSineDisplacementBound

/-! # Arbitrarily small confinement of the actual high H^-1 branch points

At a trace root Delta²=4, a small trace error controls the sine squared.
The uniform filled-sine quotient bound then confines every high zero to
any prescribed small frequency disc. No spectral labels, reality, or
individual analytic root choices are required.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem four_norm_sin_sq_le_of_trace_root (D z : ℂ) {epsilon : ℝ}
    (hD : D^2 = 4) (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1)
    (herror : ‖D-2*cos z‖ ≤ epsilon) : 4*‖sin z‖^2 ≤ 5*epsilon := by
  have hnormsq : ‖D‖^2 = 4 := by rw [← norm_pow,hD]; norm_num
  have hnormD : ‖D‖ = 2 := by nlinarith [norm_nonneg D]
  have hfree : ‖2*cos z‖ ≤ 3 := by
    have ht := norm_le_norm_sub_add (2*cos z) D
    rw [norm_sub_rev (2*cos z) D,hnormD] at ht
    linarith
  have he : (D-2*cos z)*(D+2*cos z) = 4*sin z^2 := by
    have ht := Complex.sin_sq_add_cos_sq z
    linear_combination hD-4*ht
  have hfactor : 4*‖sin z‖^2 = ‖D-2*cos z‖*‖D+2*cos z‖ := by
    rw [← norm_mul,he,norm_mul,norm_pow]
    norm_num
  rw [hfactor]
  calc
    _ ≤ epsilon*(‖D‖+‖2*cos z‖) :=
      mul_le_mul herror (norm_add_le _ _) (norm_nonneg _) hepsilon
    _ ≤ epsilon*5 := mul_le_mul_of_nonneg_left (by rw [hnormD]; linarith) hepsilon
    _ = 5*epsilon := mul_comm _ _

/-- One complex H^-1 neighborhood confines all high characteristic zeros. -/
theorem exists_hillHminus_small_gap_coverage (q : PeriodOneHminusOne)
    (r : ℝ) (hr : 0 < r) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ n : ℕ, N ≤ n →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4),
          hillHminusRadicand a (z^2) = 0 → z ∈ ball ((Real.pi : ℂ)*n) r := by
  obtain ⟨C,hC,hdisplacement⟩ := exists_freeDisc_sine_displacement_bound
    (by linarith [Real.pi_pos] : Real.pi/4 < Real.pi)
  let epsilon : ℝ := min 1 (r^2/(5*(C+1)^2))
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hepsilon1 : epsilon ≤ 1 := min_le_left _ _
  have hepsilonr : epsilon*(5*(C+1)^2) ≤ r^2 :=
    (le_div_iff₀ (by positivity : 0 < 5*(C+1)^2)).mp (min_le_right _ _)
  obtain ⟨N,V,hN,hV,hq,hd⟩ := exists_hillHminus_disc_trace_approximation q (Real.pi/4)
    (by positivity) le_rfl epsilon hepsilon
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro a ha n hn z hz hzero
  have hD : hillHminusDiscriminant a (z^2)^2 = 4 := sub_eq_zero.mp hzero
  have hsine := four_norm_sin_sq_le_of_trace_root _ z hD hepsilon.le hepsilon1 (hd a ha n hn z hz)
  have hdist : ‖z-(Real.pi : ℂ)*n‖ ≤ C*‖sin z‖ :=
    hdisplacement (n : ℤ) z (by simpa only [mem_closedBall,dist_eq_norm,Int.cast_natCast] using hz)
  have hprod := mul_le_mul_of_nonneg_right hsine (sq_nonneg (C+1))
  have hsq : ((C+1)*‖sin z‖)^2 ≤ (r/2)^2 := by nlinarith
  have hbound : (C+1)*‖sin z‖ ≤ r/2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  have hsmall : ‖z-(Real.pi : ℂ)*n‖ < r := by
    have hc : C*‖sin z‖ ≤ (C+1)*‖sin z‖ := by nlinarith [norm_nonneg (sin z)]
    linarith
  simpa only [mem_ball,dist_eq_norm] using hsmall

end NLS.KdV
