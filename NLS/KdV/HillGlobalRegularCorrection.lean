import NLS.KdV.HillRegularAngleCompatibility

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillDirichlet_real_terminal_angle (k : ℕ) (hk : 1 ≤ k)
    (hgap : hillRealGapHalfLength q hq hr k ≠ 0) :
    ∃ θ : ℝ, θ ∈ Icc (-Real.pi) Real.pi ∧
      cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) (θ:ℂ) =
        (hillDirichletEnergy q hq hr k hk : ℂ) ∧
      Complex.sin (θ:ℂ) = hillDirichletGapSine q hq hr k hk := by
  obtain ⟨e,he,hpoint,_,hsin⟩ := exists_hillDirichlet_terminal_angle q hq hr k hk hgap
  have he' : e ∈ segment ℝ ((-Real.pi : ℝ):ℂ) (Real.pi:ℂ) := by simpa only [ofReal_neg] using he
  have hi : e.im = 0 := im_eq_zero_of_mem_real_segment (-Real.pi) Real.pi e he'
  have heq : e = (e.re : ℂ) := by apply Complex.ext <;> simp [hi]
  refine ⟨e.re,re_mem_Icc_of_mem_real_segment (-Real.pi) Real.pi (by linarith [Real.pi_pos]) e he',?_,?_⟩
  · rw [heq] at hpoint
    exact hpoint
  · rw [heq] at hsin
    exact hsin

def hillDirichletSelectedRealAngle (k : ℕ) (hk : 1 ≤ k) (hgap : hillRealGapHalfLength q hq hr k ≠ 0) : ℝ :=
  Classical.choose (exists_hillDirichlet_real_terminal_angle q hq hr k hk hgap)

theorem hillDirichletSelectedRealAngle_spec (k : ℕ) (hk : 1 ≤ k) (hgap : hillRealGapHalfLength q hq hr k ≠ 0) :
    hillDirichletSelectedRealAngle q hq hr k hk hgap ∈ Icc (-Real.pi) Real.pi ∧
      cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k)
        (hillDirichletSelectedRealAngle q hq hr k hk hgap : ℂ) = (hillDirichletEnergy q hq hr k hk : ℂ) ∧
      Complex.sin (hillDirichletSelectedRealAngle q hq hr k hk hgap : ℂ) = hillDirichletGapSine q hq hr k hk :=
  Classical.choose_spec (exists_hillDirichlet_real_terminal_angle q hq hr k hk hgap)

def hillRegularAbelianCorrection (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) : ℂ :=
  if hc : hillRealGapHalfLength q hq hr k = 0 then 0 else
    hillRegularAbelianPrimitive q hq hr n hn k (hillDirichletSelectedRealAngle q hq hr k hk hc : ℂ)

theorem hillRegularAbelianCorrection_closed (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k)
    (hc : hillRealGapHalfLength q hq hr k = 0) : hillRegularAbelianCorrection q hq hr n hn k hk = 0 := by
  simp only [hillRegularAbelianCorrection,dif_pos hc]

theorem hillRegularAbelianCorrection_eq_of_terminal
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hgap : hillRealGapHalfLength q hq hr k ≠ 0) (θ : ℝ)
    (hpoint : cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) (θ:ℂ) =
      (hillDirichletEnergy q hq hr k hk : ℂ))
    (hsin : Complex.sin (θ:ℂ) = hillDirichletGapSine q hq hr k hk) :
    hillRegularAbelianCorrection q hq hr n hn k hk = hillRegularAbelianPrimitive q hq hr n hn k (θ:ℂ) := by
  rw [hillRegularAbelianCorrection,dif_neg hgap]
  have hspec := hillDirichletSelectedRealAngle_spec q hq hr k hk hgap
  exact hillRegularAbelianPrimitive_terminal_independent q hq hr n k hn hk hgap _ θ hspec.2.1 hpoint hspec.2.2 hsin

theorem hillRegularAbelianCorrection_im_eq_zero (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    (hillRegularAbelianCorrection q hq hr n hn k hk).im = 0 := by
  unfold hillRegularAbelianCorrection
  split_ifs with hc
  · exact zero_im
  · exact hillRegularAbelianPrimitive_im_eq_zero q hq hr n hn k hk _

end NLS.KdV
