import NLS.KdV.HillHminusOneSmallCriticalControl
import NLS.KdV.HillHminusOneGapQuotientAsymptotics
import NLS.KdV.HillHminusOnePeriodBounds
import NLS.KdV.SquaredCoshCriticalDisc
import NLS.ComplexAnalysis.TwoZeroCriticalLocalization

/-! # Actual rough critical energies at quadratic gap scale -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem exists_critical_gap_square_localization :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1/16 →
        ∃ M : ℕ, ∃ U : Set PeriodOneHminusOne, 0 < M ∧ U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧
          ∀ n : ℕ+, M ≤ (n : ℕ) → ∃ K : ℂ × PeriodOneHminusOne → ℂ,
            AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ U) ∧
            (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ U,
              squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant t.2 t.1/2) ∧
            (∀ t ∈ (hillHminusGapSquareDisc n r ×ˢ U) ∩ hillHminusContinuationDomain,
              K t = (hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
            ∀ a ∈ U, ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
            l ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) ((epsilon/64)*(Real.pi*(n : ℕ)*r)) ∧
            u ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) ((epsilon/64)*(Real.pi*(n : ℕ)*r)) ∧
            AnalyticOnNhd ℂ (twoZeroQuotient (fun z => K (z,a)) l u) (hillHminusGapSquareDisc n r) ∧
            (∀ z, K (z,a) = (z-l)*(z-u)*twoZeroQuotient (fun z => K (z,a)) l u z) ∧
            (∀ z ∈ hillHminusGapSquareDisc n r,
              ‖(4*((Real.pi : ℂ)*(n : ℕ))^2)*twoZeroQuotient (fun z => K (z,a)) l u z+1‖ ≤ epsilon) ∧
            ‖hillHminusUniformCriticalPoint C N n a-(l+u)/2‖ ≤
              (2*epsilon/(Real.pi*r))*‖l-u‖^2/(n : ℕ) ∧
            ‖hillHminusUniformCriticalPoint C N n a-(l+u)/2‖ ≤ ‖l-u‖/4 ∧
            (l = u → hillHminusUniformCriticalPoint C N n a = l) ∧
            ∀ z ∈ sphere ((l+u)/2) ‖l-u‖,
              ‖l-u‖/2 ≤ ‖z-hillHminusUniformCriticalPoint C N n a‖ := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_hillHminus_normalized_gap_quotients 0
  obtain ⟨Us,hUsV,hUs,h0Us,hclose⟩ := D.toHillHminusAllContourPeriodData.exists_uniform_small_critical_control
    (r/32) (by positivity) (by linarith)
  refine ⟨r,hr,hrpi,?_⟩
  intro epsilon hepsilon hepsilon16
  obtain ⟨M,Vq,hM,hVq,h0Vq,hQfamily⟩ := hfamily epsilon hepsilon (by linarith)
  refine ⟨M,Vq ∩ Us,hM,fun _ ha => hUsV ha.2,hVq.inter hUs,⟨h0Vq,h0Us⟩,?_⟩
  intro n hn
  obtain ⟨K,hK,htrace,hmatch,hpairs⟩ := hQfamily n hn
  have hsub : hillHminusGapSquareDisc n r ×ˢ (Vq ∩ Us) ⊆ hillHminusGapSquareDisc n r ×ˢ Vq :=
    fun _ ht => ⟨ht.1,ht.2.1⟩
  refine ⟨K,hK.mono hsub,fun t ht => htrace t (hsub ht),
    fun t ht => hmatch t ⟨hsub ht.1,ht.2⟩,?_⟩
  intro a ha
  obtain ⟨l,u,hpair,hl,hu,hQ,hfactor,hbound⟩ := hpairs a ha.1
  let c : ℝ := Real.pi*(n : ℕ)
  let E : ℂ := ((Real.pi : ℂ)*(n : ℕ))^2
  let R : ℝ := c*r
  let mu : ℂ := hillHminusUniformCriticalPoint C N n a
  let Q : ℂ → ℂ := twoZeroQuotient (fun z => K (z,a)) l u
  let A : ℂ := 4*((Real.pi : ℂ)*(n : ℕ))^2
  have hc : 0 < c := by dsimp only [c];positivity
  have hR : 0 < R := mul_pos hc hr
  have hrc : r/8 ≤ c := by
    have hnreal : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
    dsimp only [c]
    nlinarith [Real.pi_pos]
  have hmu : mu ∈ ball E (R/8) := by
    have hh := square_mem_energy_ball_of_small_frequency c (r/8) hc (by positivity) hrc
      (sqrt mu) (by
        simpa only [c,ofReal_mul,ofReal_natCast,show (r/8)/4 = r/32 by ring,mem_ball,dist_eq_norm]
          using hclose n a ha.2)
    simpa only [complex_sqrt_sq,mu,E,R,c,ofReal_mul,ofReal_natCast,mul_div_assoc] using hh
  have hR8 : R/8 ≤ R := by linarith
  have hmuR : mu ∈ ball E R := ball_subset_ball hR8 hmu
  have hlc : l ∈ closedBall E (R/8) := by
    apply ball_subset_closedBall (ball_subset_ball ?_ hl)
    dsimp only [R,c]
    nlinarith
  have huc : u ∈ closedBall E (R/8) := by
    apply ball_subset_closedBall (ball_subset_ball ?_ hu)
    dsimp only [R,c]
    nlinarith
  have hmuC : mu ∈ closedBall E (R/8) := ball_subset_closedBall hmu
  have hmuDisc : mu ∈ hillHminusGapSquareDisc n r := ball_subset_closedBall hmuR
  have hAQ : ‖A*Q mu‖ ≤ 2 := by
    have hh := norm_sub_le (A*Q mu+1) (1 : ℂ)
    rw [add_sub_cancel_right,norm_one] at hh
    have hb := hbound mu hmuDisc
    change ‖A*Q mu+1‖ ≤ epsilon at hb
    linarith
  have hxl : ‖mu-l‖ ≤ R/4 := by
    have hh := norm_sub_le_norm_sub_add_norm_sub mu E l
    rw [norm_sub_rev E l] at hh
    have hx' := mem_closedBall_iff_norm.mp hmuC
    have hl' := mem_closedBall_iff_norm.mp hlc
    linarith
  have hxu : ‖mu-u‖ ≤ R/4 := by
    have hh := norm_sub_le_norm_sub_add_norm_sub mu E u
    rw [norm_sub_rev E u] at hh
    have hx' := mem_closedBall_iff_norm.mp hmuC
    have hu' := mem_closedBall_iff_norm.mp huc
    linarith
  have hAnorm : ‖A‖ = 4*c^2 := by simp [A,c,abs_of_pos Real.pi_pos]
  have hscaled : (4*c^2)*‖K (mu,a)‖ ≤ (R/4)*(R/4)*2 := by
    rw [← hAnorm,← norm_mul]
    calc
      _ = ‖(mu-l)*(mu-u)*(A*Q mu)‖ := by congr 1;rw [hfactor mu];ring
      _ = ‖mu-l‖*‖mu-u‖*‖A*Q mu‖ := by rw [norm_mul,norm_mul (mu-l) (mu-u)]
      _ ≤ _ := by gcongr
  have hKnorm : ‖K (mu,a)‖ ≤ r^2/32 := by
    calc
      _ ≤ ((R/4)*(R/4)*2)/(4*c^2) := (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hscaled)
      _ = _ := by dsimp only [R];field_simp;ring
  have hKsmall : ‖K (mu,a)‖ < Real.pi^2 := by
    have hh := mul_self_le_mul_self hr.le hrpi
    nlinarith [Real.pi_pos]
  have hKmu : AnalyticAt ℂ (fun z => K (z,a)) mu :=
    (hK (mu,a) ⟨hmuDisc,ha.1⟩).comp (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
  have hrel : (fun z => squaredCosh (K (z,a))) =ᶠ[𝓝 mu]
      (fun z => (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant a z/2) := by
    filter_upwards [isOpen_ball.mem_nhds hmuR] with z hz
    exact htrace (z,a) ⟨ball_subset_closedBall hz,ha.1⟩
  have hd := ((analyticOnNhd_squaredCosh (K (mu,a)) (mem_univ _)).differentiableAt.hasDerivAt).comp mu
    hKmu.differentiableAt.hasDerivAt
  have hdt := ((((analyticOnNhd_hillHminusDiscriminant_joint (mu,a) (mem_univ _)).comp
      (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)).differentiableAt.hasDerivAt.const_mul
    ((-1 : ℂ)^(n : ℕ))).div_const 2)
  have hder : deriv squaredCosh (K (mu,a))*deriv (fun z => K (z,a)) mu =
      ((-1 : ℂ)^(n : ℕ))*deriv (hillHminusDiscriminant a) mu/2 :=
    hd.deriv.symm.trans (hrel.deriv_eq.trans hdt.deriv)
  have hz := D.critical_zero n a (hUsV ha.2)
  change deriv (hillHminusDiscriminant a) mu = 0 at hz
  rw [hz,mul_zero,zero_div] at hder
  have hstationary : deriv (fun z => (z-l)*(z-u)*Q z) mu = 0 := by
    rw [← funext hfactor]
    exact (mul_eq_zero.mp hder).resolve_left (deriv_squaredCosh_ne_zero_of_norm_lt_pi_sq _ hKsmall)
  obtain ⟨hquad,hlinear⟩ := norm_critical_sub_midpoint_le_two_zero_gap Q A E l u mu R epsilon hR
    hepsilon.le hepsilon16 hQ hlc huc hmuC hbound hstationary
  refine ⟨l,u,hpair,hl,hu,hQ,hfactor,hbound,?_,hlinear,?_,fun z hz => gap_circle_critical_separation l u mu z hlinear hz⟩
  · apply hquad.trans_eq
    dsimp only [R,c]
    field_simp
  · intro he
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hh := hquad
    rw [he,sub_self,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_div] at hh
    simpa only [he,add_self_div_two] using le_antisymm hh (norm_nonneg _)

/-- The actual selected critical energy is quadratically close to the
actual gap midpoint, including exact equality at a collapsed pair. -/
theorem exists_critical_gap_localization :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1/16 →
        ∃ M : ℕ, ∃ U : Set PeriodOneHminusOne, 0 < M ∧ U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧
          ∀ n : ℕ+, M ≤ (n : ℕ) → ∀ a ∈ U, ∃ l u : ℂ,
            HillHminusHighGapPair a n r l u ∧
            ‖hillHminusUniformCriticalPoint C N n a-(l+u)/2‖ ≤
              (2*epsilon/(Real.pi*r))*‖l-u‖^2/(n : ℕ) ∧
            ‖hillHminusUniformCriticalPoint C N n a-(l+u)/2‖ ≤ ‖l-u‖/4 ∧
            (l = u → hillHminusUniformCriticalPoint C N n a = l) ∧
            ∀ z ∈ sphere ((l+u)/2) ‖l-u‖,
              ‖l-u‖/2 ≤ ‖z-hillHminusUniformCriticalPoint C N n a‖ := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := D.exists_critical_gap_square_localization
  refine ⟨r,hr,hrpi,?_⟩
  intro epsilon hepsilon hepsilon16
  obtain ⟨M,U,hM,hUV,hU,h0U,hdata⟩ := hfamily epsilon hepsilon hepsilon16
  refine ⟨M,U,hM,hUV,hU,h0U,?_⟩
  intro n hn a ha
  obtain ⟨K,_,_,_,hpairs⟩ := hdata n hn
  obtain ⟨l,u,hpair,_,_,_,_,_,hquad,hlinear,hcollapsed,hsep⟩ := hpairs a ha
  exact ⟨l,u,hpair,hquad,hlinear,hcollapsed,hsep⟩

/-- The near-zero rough-topology form of source (37), with one cutoff
and neighborhood before all high actual critical/gap pairs. -/
theorem exists_relative_critical_gap_bound (eta : ℝ) (heta : 0 < eta) :
    ∃ r : ℝ, ∃ M : ℕ, ∃ U : Set PeriodOneHminusOne,
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < M ∧ U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧
        ∀ n : ℕ+, M ≤ (n : ℕ) → ∀ a ∈ U, ∃ l u : ℂ,
          HillHminusHighGapPair a n r l u ∧
            ‖hillHminusUniformCriticalPoint C N n a-(l+u)/2‖ ≤ eta*‖l-u‖ := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := D.exists_critical_gap_localization
  let epsilon : ℝ := min (1/16) (eta/4)
  have hepsilon : 0 < epsilon := by dsimp only [epsilon];positivity
  have hepsilon16 : epsilon ≤ 1/16 := min_le_left _ _
  have hepsilonEta : 4*epsilon ≤ eta := by
    have hh := min_le_right (1/16 : ℝ) (eta/4)
    change epsilon ≤ eta/4 at hh
    linarith
  obtain ⟨M,U,hM,hUV,hU,h0U,hdata⟩ := hfamily epsilon hepsilon hepsilon16
  refine ⟨r,M,U,hr,hrpi,hM,hUV,hU,h0U,?_⟩
  intro n hn a ha
  obtain ⟨l,u,hpair,hquad,_,_,_⟩ := hdata n hn a ha
  let E : ℂ := ((Real.pi : ℂ)*(n : ℕ))^2
  have hl : ‖l-E‖ < Real.pi*(n : ℕ)*r := mem_ball_iff_norm.mp hpair.left_mem
  have hu : ‖u-E‖ < Real.pi*(n : ℕ)*r := mem_ball_iff_norm.mp hpair.right_mem
  have hgap : ‖l-u‖ ≤ 2*Real.pi*(n : ℕ)*r := by
    have hh := norm_sub_le_norm_sub_add_norm_sub l E u
    rw [norm_sub_rev E u] at hh
    linarith
  have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
  have hscaled : (2*epsilon/(Real.pi*r))*‖l-u‖^2/(n : ℕ) ≤ 4*epsilon*‖l-u‖ := by
    apply (div_le_iff₀ hnpos).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < Real.pi*r)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2*epsilon*‖l-u‖ by positivity)]
  exact ⟨l,u,hpair,hquad.trans (hscaled.trans
    (mul_le_mul_of_nonneg_right hepsilonEta (norm_nonneg _)))⟩

end HillHminusUniformPeriodData
end NLS.KdV
