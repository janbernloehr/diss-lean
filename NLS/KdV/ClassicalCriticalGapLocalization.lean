import NLS.KdV.ClassicalHillGapQuotientAsymptotics
import NLS.KdV.ClassicalCriticalTailAnalytic
import NLS.KdV.SquaredCoshCriticalDisc
import NLS.ComplexAnalysis.TwoZeroCriticalLocalization

/-! # Actual high critical energies at quadratic gap scale

The whole-disc deflated square estimate locates the actual critical
energy relative to its actual gap midpoint. Its normalized displacement
can be made arbitrarily small on one common complex tail neighborhood.
Coincident endpoints and the critical pole inside the gap circle are
included; no reality or open-gap lower bound is assumed.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem ClassicalHillHighGapPair.norm_gap_le {q : Curve ℂ} {n : ℕ+} {l u : ℂ}
    (h : ClassicalHillHighGapPair q n l u) : ‖l-u‖ ≤ 2*Real.pi^2*(n : ℕ) := by
  obtain ⟨z,hz,hzl⟩ := h.left_mem
  obtain ⟨w,hw,hwu⟩ := h.right_mem
  change z^2 = l at hzl
  change w^2 = u at hwu
  have hz' : ‖z-(Real.pi : ℂ)*(n : ℕ)‖ ≤ Real.pi/4 := (mem_ball_iff_norm.mp hz).le
  have hw' : ‖w-(Real.pi : ℂ)*(n : ℕ)‖ ≤ Real.pi/4 := (mem_ball_iff_norm.mp hw).le
  have hcenter : ‖(Real.pi : ℂ)*(n : ℕ)‖ = Real.pi*(n : ℕ) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_natCast]
  have hzn : ‖z‖ ≤ Real.pi*(n : ℕ)+Real.pi/4 := by
    have ht := norm_le_norm_sub_add z ((Real.pi : ℂ)*(n : ℕ))
    rw [hcenter] at ht
    linarith
  have hwn : ‖w‖ ≤ Real.pi*(n : ℕ)+Real.pi/4 := by
    have ht := norm_le_norm_sub_add w ((Real.pi : ℂ)*(n : ℕ))
    rw [hcenter] at ht
    linarith
  have hdiff : ‖z-w‖ ≤ Real.pi/2 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub z ((Real.pi : ℂ)*(n : ℕ)) w
    rw [norm_sub_rev ((Real.pi : ℂ)*(n : ℕ)) w] at ht
    linarith
  have hsum : ‖z+w‖ ≤ 2*Real.pi*(n : ℕ)+Real.pi/2 :=
    (norm_add_le z w).trans (by linarith)
  rw [← hzl,← hwu,sq_sub_sq,norm_mul]
  calc
    _ ≤ (2*Real.pi*(n : ℕ)+Real.pi/2)*(Real.pi/2) :=
      mul_le_mul hsum hdiff (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      have hn : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
      nlinarith [sq_pos_of_pos Real.pi_pos]

theorem exists_classicalHill_critical_gap_localization (q : Curve ℂ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1/16 →
        ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
          ∀ n : ℕ+, N ≤ (n : ℕ) →
            AnalyticOnNhd ℂ (fun a => classicalHillHighCriticalPoint a n) V ∧
            AnalyticOnNhd ℂ (fun a => classicalHillHighMidpoint a n) V ∧
            AnalyticOnNhd ℂ (fun a => classicalHillHighSquaredGap a n) V ∧
            ∀ a ∈ V,
              ‖classicalHillHighCriticalPoint a n-classicalHillHighMidpoint a n‖ ≤
                (2*epsilon/(Real.pi*r))*‖classicalHillHighSquaredGap a n‖/(n : ℕ) ∧
              (classicalHillHighSquaredGap a n = 0 →
                classicalHillHighCriticalPoint a n = classicalHillHighMidpoint a n) ∧
              ∃ l u : ℂ, ClassicalHillHighGapPair a n l u ∧
                ‖classicalHillHighCriticalPoint a n-(l+u)/2‖ ≤ ‖l-u‖/4 ∧
                ∀ z ∈ sphere ((l+u)/2) ‖l-u‖,
                  ‖l-u‖/2 ≤ ‖z-classicalHillHighCriticalPoint a n‖ := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_classicalHill_normalized_gap_quotients q
  obtain ⟨Nd,Vd,_,hVd,hqd,hclose⟩ :=
    exists_classicalHill_small_critical_frequency_neighborhood q (r/32) (by positivity)
  obtain ⟨Nc,Vc,_,hVc,hqc,hcrit⟩ := exists_analytic_classicalHillHighCriticalPoints q
  obtain ⟨Ng,Vg,_,hVg,hqg,hgap⟩ := exists_analytic_classicalHillHighGapFamilies q
  refine ⟨r,hr,hrpi,?_⟩
  intro epsilon hepsilon hepsilon16
  obtain ⟨Nq,Vq,hNq,hVq,hqq,hQfamily⟩ := hfamily epsilon hepsilon (by linarith)
  let N := max Nq (max Nd (max (Nc+1) (Ng+1)))
  let V := Vq ∩ (Vd ∩ (Vc ∩ Vg))
  refine ⟨N,V,hNq.trans_le (le_max_left _ _),hVq.inter (hVd.inter (hVc.inter hVg)),
    ⟨hqq,hqd,hqc,hqg⟩,?_⟩
  intro n hn
  have hnq : Nq ≤ (n : ℕ) := (le_max_left _ _).trans hn
  have hnd : Nd ≤ (n : ℕ) := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnc : Nc < (n : ℕ) := by
    have := (le_max_left (Nc+1) (Ng+1)).trans ((le_max_right Nd _).trans ((le_max_right Nq _).trans hn))
    omega
  have hng : Ng < (n : ℕ) := by
    have := (le_max_right (Nc+1) (Ng+1)).trans ((le_max_right Nd _).trans ((le_max_right Nq _).trans hn))
    omega
  refine ⟨((hcrit n hnc).2.1).mono (fun _ ha => ha.2.2.1),
    ((hgap n hng).1).mono (fun _ ha => ha.2.2.2),
    ((hgap n hng).2.1).mono (fun _ ha => ha.2.2.2),?_⟩
  intro a ha
  obtain ⟨K,hK,htrace,_,hpairs⟩ := hQfamily n hnq
  obtain ⟨l,u,hpair,hl,hu,hQ,hfactor,hbound⟩ := hpairs a ha.1
  let c : ℝ := Real.pi*(n : ℕ)
  let E : ℂ := ((Real.pi : ℂ)*(n : ℕ))^2
  let R : ℝ := c*r
  let mu : ℂ := classicalHillHighCriticalPoint a n
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
      (classicalHillFrequencyCritical a n) (by
        simpa only [c,ofReal_mul,ofReal_natCast,show (r/8)/4 = r/32 by ring,mem_ball,dist_eq_norm]
          using hclose a ha.2.1 n hnd)
    simpa only [classicalHillHighCriticalPoint,mu,E,R,c,ofReal_mul,ofReal_natCast,mul_div_assoc] using hh
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
  have hmuDisc : mu ∈ classicalHillGapSquareDisc n r := ball_subset_closedBall hmuR
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
      (fun z => (-1 : ℂ)^(n : ℕ)*classicalHillDiscriminant a z/2) := by
    filter_upwards [isOpen_ball.mem_nhds hmuR] with z hz
    exact htrace (z,a) ⟨ball_subset_closedBall hz,ha.1⟩
  have hd := ((analyticOnNhd_squaredCosh (K (mu,a)) (mem_univ _)).differentiableAt.hasDerivAt).comp mu
    hKmu.differentiableAt.hasDerivAt
  have hdt := (((analyticOnNhd_classicalHillDiscriminant a mu (mem_univ _)).differentiableAt.hasDerivAt.const_mul
    ((-1 : ℂ)^(n : ℕ))).div_const 2)
  have hder : deriv squaredCosh (K (mu,a))*deriv (fun z => K (z,a)) mu =
      ((-1 : ℂ)^(n : ℕ))*deriv (classicalHillDiscriminant a) mu/2 :=
    hd.deriv.symm.trans (hrel.deriv_eq.trans hdt.deriv)
  have hz := ((hcrit n hnc).2.2 a ha.2.2.1).2.1
  change deriv (classicalHillDiscriminant a) mu = 0 at hz
  rw [hz,mul_zero,zero_div] at hder
  have hstationary : deriv (fun z => (z-l)*(z-u)*Q z) mu = 0 := by
    rw [← funext hfactor]
    exact (mul_eq_zero.mp hder).resolve_left (deriv_squaredCosh_ne_zero_of_norm_lt_pi_sq _ hKsmall)
  obtain ⟨hquad,hlinear⟩ := norm_critical_sub_midpoint_le_two_zero_gap Q A E l u mu R epsilon hR
    hepsilon.le hepsilon16 hQ hlc huc hmuC hbound hstationary
  have hgapnorm : ‖classicalHillHighSquaredGap a n‖ = ‖l-u‖^2 := by rw [hpair.squaredGap_eq,norm_pow]
  have hactual : ‖mu-classicalHillHighMidpoint a n‖ ≤
      (2*epsilon/(Real.pi*r))*‖classicalHillHighSquaredGap a n‖/(n : ℕ) := by
    rw [hpair.midpoint_eq]
    apply hquad.trans_eq
    rw [hgapnorm]
    dsimp only [R,c]
    field_simp
  refine ⟨hactual,?_,l,u,hpair,hlinear,fun z hz => gap_circle_critical_separation l u mu z hlinear hz⟩
  intro hzero
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [hzero,norm_zero,mul_zero,zero_div] at hactual
  exact le_antisymm hactual (norm_nonneg _)

/-- The normalized critical displacement is uniformly smaller than any
prescribed multiple of the squared-gap scale on a common complex tail. -/
theorem exists_classicalHill_critical_gap_ratio_bound (q : Curve ℂ) (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ n : ℕ+, N ≤ (n : ℕ) →
        ‖classicalHillHighCriticalPoint a n-classicalHillHighMidpoint a n‖ ≤
          eta*‖classicalHillHighSquaredGap a n‖/(n : ℕ) := by
  obtain ⟨r,hr,_,hfamily⟩ := exists_classicalHill_critical_gap_localization q
  let epsilon := min (1/16) (eta*(Real.pi*r)/2)
  have hepsilon : 0 < epsilon := by dsimp only [epsilon];positivity
  have hepsilon16 : epsilon ≤ 1/16 := min_le_left _ _
  obtain ⟨N,V,hN,hV,hq,hbound⟩ := hfamily epsilon hepsilon hepsilon16
  have hcoeff : 2*epsilon/(Real.pi*r) ≤ eta := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := min_le_right (1/16 : ℝ) (eta*(Real.pi*r)/2)
    change epsilon ≤ eta*(Real.pi*r)/2 at hh
    linarith
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro a ha n hn
  exact ((hbound n hn).2.2.2 a ha).1.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)) (by positivity))

/-- The continuous-potential form of source (37), with one complex
neighborhood and cutoff before all retained actual endpoint pairs. -/
theorem exists_classicalHill_relative_critical_gap_bound (q : Curve ℂ) (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ n : ℕ+, N ≤ (n : ℕ) →
        ∃ l u : ℂ, ClassicalHillHighGapPair a n l u ∧
          ‖classicalHillHighCriticalPoint a n-(l+u)/2‖ ≤ eta*‖l-u‖ := by
  obtain ⟨N,V,hN,hV,hq,hbound⟩ := exists_classicalHill_critical_gap_ratio_bound q
    (eta/(2*Real.pi^2)) (by positivity)
  obtain ⟨M,W,_,hW,hqW,hfamily⟩ := exists_analytic_classicalHillHighGapFamilies q
  refine ⟨max N (M+1),V ∩ W,hN.trans_le (le_max_left _ _),hV.inter hW,⟨hq,hqW⟩,?_⟩
  intro a ha n hn
  have hnN : N ≤ (n : ℕ) := (le_max_left _ _).trans hn
  have hnM : M < (n : ℕ) := by have := (le_max_right N (M+1)).trans hn;omega
  obtain ⟨l,u,hpair⟩ := (hfamily n hnM).2.2.2 a ha.2
  have hb := hbound a ha.1 n hnN
  rw [hpair.midpoint_eq,hpair.squaredGap_eq,norm_pow] at hb
  have hg := hpair.norm_gap_le
  have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
  have hgscale : ‖l-u‖^2/(n : ℕ) ≤ (2*Real.pi^2)*‖l-u‖ := by
    apply (div_le_iff₀ hnpos).mpr
    nlinarith [mul_le_mul_of_nonneg_right hg (norm_nonneg (l-u))]
  refine ⟨l,u,hpair,hb.trans ?_⟩
  calc
    _ = (eta/(2*Real.pi^2))*(‖l-u‖^2/(n : ℕ)) := by ring
    _ ≤ (eta/(2*Real.pi^2))*((2*Real.pi^2)*‖l-u‖) :=
      mul_le_mul_of_nonneg_left hgscale (by positivity)
    _ = eta*‖l-u‖ := by field_simp

end NLS.KdV
