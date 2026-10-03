import NLS.ZakharovShabat.ClassicalGradientFourierPowerBound
import NLS.ZakharovShabat.ClassicalEndpointGradientFiniteSummability

/-! # A single summable gradient bound over every spectral disc

The majorant is chosen before the spectral points, potential, initial
vector, endpoint functional, and observation. This uniformity permits
suprema and contour integration in G.7.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Simultaneous G.5 bounds throughout all discs of a fixed radius around the free lattice. -/
theorem exists_classicalEndpointGradient_disc_uniform_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (M : ℝ) (hM : 0 ≤ M) (B : ℝ) (hB : 0 ≤ B) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ), ‖v‖ ≤ 1 → ∀ (L : (ℂ × ℂ) →L[ℂ] ℂ), ‖L‖ ≤ 1 →
      ∀ (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ (n : ℤ) (z : ℂ),
      ‖z-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B →
      ‖classicalEndpointGradientFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (classicalSobolevPotential a) z z v L P‖ ≤ b n := by
  have hq1 : 1 < q := lt_of_le_of_lt
    (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq
  let : Fact (1 ≤ q) := ⟨hq1.le⟩
  let A := classicalGradientValueConstant M B
  let D := classicalGradientDerivativeConstant M B
  have hA : 0 ≤ A := classicalGradientValueConstant_nonneg M B hM
  have hD : 0 ≤ D := classicalGradientDerivativeConstant_nonneg M B hM
  obtain ⟨K,α,_,hα,hpow⟩ := exists_classicalGradientFourier_power_bound p hp q hq A D hA hD
  obtain ⟨N,hN,hcut⟩ := exists_near_free_frequency_cutoff B hB
  let g (n : ℤ) := K*(n.natAbs : ℝ)^(-α)
  have hg : Memℓp g (ENNReal.ofReal p) := (memlp_inverse_natAbs_rpow p (by linarith) α hα).const_mul K
  let R (n : ℤ) := Real.pi*(n.natAbs : ℝ)+B
  let head (n : ℤ) := (24+24*R n+8*M)*(Real.exp (4*M+2*R n))^3*unitIntervalC1FourierConstant hq1
  let b (n : ℤ) := if N ≤ n.natAbs then ‖g n‖ else ‖head n‖
  refine ⟨b,?_,?_⟩
  · exact memlp_of_natAbs_eventual_bound p (by linarith) b (fun n => ‖g n‖) hg.norm N
      (by intro n hn; simp [b,hn])
  intro a ha v hv L hL P hP n z hzB
  by_cases hn : N ≤ n.natAbs
  · obtain ⟨him,_,hzn⟩ := hcut n hn z hzB
    have hn1 : 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast lt_of_lt_of_le hN hn
    have hnp : 0 < (n.natAbs : ℝ) := by linarith
    have hzn' : (n.natAbs : ℝ) ≤ ‖z‖ := by nlinarith [Real.two_le_pi]
    have hz : z ≠ 0 := norm_pos_iff.mp (hnp.trans_le hzn')
    have hval (t : Icc (0 : ℝ) 1) :
        ‖classicalEndpointGradientRemainder (classicalSobolevPotential a) z z v L t‖ ≤ A/(n.natAbs : ℝ) :=
      (norm_classicalEndpointGradientRemainder_sobolev_strip_le M B a ha z hz him v hv L hL t).trans
        (div_le_div_of_nonneg_left hA hnp hzn')
    have hd (t : Icc (0 : ℝ) 1) :
        ‖deriv (classicalEndpointGradientRemainder (classicalSobolevPotential a) z z v L) t‖ ≤ D :=
      norm_deriv_classicalEndpointGradientRemainder_sobolev_strip_le M B a ha z hz him v hv L hL t
    exact (hpow _ z z v L P hP _ hn1 hval hd).trans
      (by simp only [b,if_pos hn]; exact Real.le_norm_self _)
  · have hzR : ‖z‖ ≤ R n := by
      have hc : ‖(Real.pi : ℂ)*(n : ℂ)‖ = Real.pi*(n.natAbs : ℝ) := by
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
          Complex.norm_intCast,Nat.cast_natAbs,Int.cast_abs]
      calc
        ‖z‖ = ‖(z-(Real.pi : ℂ)*(n : ℂ))+(Real.pi : ℂ)*(n : ℂ)‖ := by congr 1; ring
        _ ≤ ‖z-(Real.pi : ℂ)*(n : ℂ)‖+‖(Real.pi : ℂ)*(n : ℂ)‖ := norm_add_le _ _
        _ ≤ R n := by rw [hc]; dsimp [R]; linarith
    have hcoarse := norm_classicalEndpointGradientFourierCoefficients_all_frequencies_le hq1 M a ha z z v hv L hL P hP
    have hhead : (24+24*‖z‖+12*‖z-z‖+8*M)*(Real.exp (4*M+‖z‖+‖z‖))^3*
        unitIntervalC1FourierConstant hq1 ≤ head n := by
      have hconst := unitIntervalC1FourierConstant_nonneg hq1
      dsimp [head]
      simp only [sub_self,norm_zero,mul_zero,add_zero]
      rw [show 4*M+‖z‖+‖z‖ = 4*M+2*‖z‖ by ring]
      gcongr
    exact (hcoarse.trans hhead).trans (by simp only [b,if_neg hn]; exact Real.le_norm_self _)

end NLS.ZakharovShabat
