import NLS.KdV.HillHminusOneCriticalGapLocalization
import NLS.KdV.ClassicalHillGapScaleBounds
import NLS.ComplexAnalysis.AnalyticTwoZeroRoot
import NLS.ComplexAnalysis.CollapsedPowerPeriods

/-! # Rough cut roots with the same actual critical gap localization

The root, endpoint pair, whole-disc square and selected critical pole are
kept together. The gap-scale bound uses the free-normalized quotient and
therefore has a constant independent of the auxiliary disc radius.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem exists_critical_gap_cut_roots :
    ∃ r : ℝ, ∃ M : ℕ, ∃ U : Set PeriodOneHminusOne,
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < M ∧ U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧
        ∀ n : ℕ+, M ≤ (n : ℕ) → ∃ K : ℂ × PeriodOneHminusOne → ℂ,
          AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ U) ∧
          (∀ t ∈ (hillHminusGapSquareDisc n r ×ˢ U) ∩ hillHminusContinuationDomain,
            K t = (hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
          ∀ a ∈ U, ∃ l u : ℂ, ∃ B : ℂ → ℂ,
            HillHminusHighGapPair a n r l u ∧
            l ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/8) ∧
            u ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/8) ∧
            closedBall ((l+u)/2) ‖l-u‖ ⊆
              ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ∧
            AnalyticOnNhd ℂ B
              (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u) ∧
            (∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u,
              B z ≠ 0 ∧ B z^2 = K (z,a)) ∧
            (l = u → AnalyticOnNhd ℂ B
              (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r))) ∧
            (l = u → B l = 0) ∧
            (∀ z ∈ closedBall ((l+u)/2) ‖l-u‖ \ segment ℝ l u,
              ‖B z‖ ≤ 3*‖l-u‖/(Real.pi*(n : ℕ))) ∧
            ‖hillHminusUniformCriticalPoint C N n a-(l+u)/2‖ ≤
              (1/(8*Real.pi*r))*‖l-u‖^2/(n : ℕ) ∧
            ‖hillHminusUniformCriticalPoint C N n a-(l+u)/2‖ ≤ ‖l-u‖/4 ∧
            (l = u → hillHminusUniformCriticalPoint C N n a = l) ∧
            ∀ z ∈ sphere ((l+u)/2) ‖l-u‖,
              ‖l-u‖/2 ≤ ‖z-hillHminusUniformCriticalPoint C N n a‖ := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := D.exists_critical_gap_square_localization
  obtain ⟨M,U,hM,hUV,hU,h0U,hdata⟩ := hfamily (1/16) (by norm_num) (by norm_num)
  refine ⟨r,M,U,hr,hrpi,hM,hUV,hU,h0U,?_⟩
  intro n hn
  obtain ⟨K,hK,_,hmatch,hpairs⟩ := hdata n hn
  refine ⟨K,hK,hmatch,?_⟩
  intro a ha
  obtain ⟨l,u,hpair,hl,hu,hQ,hfactor,hbound,hquad,hlinear,hcollapsed,hsep⟩ := hpairs a ha
  let c : ℝ := Real.pi*(n : ℕ)
  let E : ℂ := ((Real.pi : ℂ)*(n : ℕ))^2
  let R : ℝ := c*r
  let Q : ℂ → ℂ := twoZeroQuotient (fun z => K (z,a)) l u
  let L : ℂ := 4*((Real.pi : ℂ)*(n : ℕ))^2
  have hc : 0 < c := by dsimp only [c];positivity
  have hR : 0 < R := mul_pos hc hr
  have hLn : ‖L‖ = 4*c^2 := by simp [L,c,abs_of_pos Real.pi_pos]
  have hQne (z : ℂ) (hz : z ∈ ball E R) : Q z ≠ 0 := by
    intro he
    have hh := hbound z (ball_subset_closedBall hz)
    change ‖L*Q z+1‖ ≤ 1/16 at hh
    rw [he,mul_zero,zero_add,norm_one] at hh
    norm_num at hh
  have hQbound (z : ℂ) (hz : z ∈ closedBall E R) : ‖Q z‖ ≤ 4/c^2 := by
    have hh := hbound z hz
    change ‖L*Q z+1‖ ≤ 1/16 at hh
    have ht := norm_sub_le (L*Q z+1) (1 : ℂ)
    rw [add_sub_cancel_right,norm_one,norm_mul,hLn] at ht
    apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
    nlinarith
  obtain ⟨B,hB,hBsq,hBcollapsed⟩ := exists_analytic_squareRoot_on_two_zero_cut
    (fun z => K (z,a)) Q l u E R hR (hQ.mono ball_subset_closedBall)
      hQne (fun z _ => hfactor z)
  have hl' : l ∈ ball E (R/8) := by
    apply ball_subset_ball (by dsimp only [R,c];nlinarith [mul_pos hc hr] : (1/16/64)*(Real.pi*(n : ℕ)*r) ≤ R/8) hl
  have hu' : u ∈ ball E (R/8) := by
    apply ball_subset_ball (by dsimp only [R,c];nlinarith [mul_pos hc hr] : (1/16/64)*(Real.pi*(n : ℕ)*r) ≤ R/8) hu
  have hsub := closed_gap_ball_subset_energy_ball l u E R hR
    (mem_ball_iff_norm.mp hl').le (mem_ball_iff_norm.mp hu').le
  have hBzero (he : l = u) : B l = 0 := by
    subst u
    have hlR : l ∈ ball E R := ball_subset_ball (by linarith) hl'
    apply root_zero_of_punctured_square B (fun z => K (z,a)) (ball E R) l isOpen_ball hlR
      ((hBcollapsed rfl) l hlR).continuousAt
      ((hK (l,a) ⟨ball_subset_closedBall hlR,ha⟩).comp
        (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)).continuousAt
    · rw [hfactor l,sub_self,zero_mul,zero_mul]
    · intro z hz hzl
      exact (hBsq z ⟨hz,by simpa only [segment_same,mem_singleton_iff] using hzl⟩).2
  refine ⟨l,u,B,hpair,hl',hu',hsub,hB,hBsq,hBcollapsed,hBzero,?_,?_,hlinear,hcollapsed,hsep⟩
  · intro z hz
    have hzin := hsub hz.1
    have hk := norm_two_zero_square_on_gap_ball (fun z => K (z,a)) Q l u z c
      (hfactor z) (hQbound z (ball_subset_closedBall hzin)) hz.1
    exact norm_le_gap_scale_of_square_bound (B z) (K (z,a)) ‖l-u‖ c
      (norm_nonneg _) hc (hBsq z ⟨hzin,hz.2⟩).2 hk
  · convert hquad using 1; ring

end HillHminusUniformPeriodData
end NLS.KdV
