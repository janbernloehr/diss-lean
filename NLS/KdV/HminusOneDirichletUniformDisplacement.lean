import NLS.KdV.HminusOneDirichletUniformControl
import NLS.ZakharovShabat.CanonicalBoundarySmallDisks
import NLS.ComplexAnalysis.SquaredFrequencyDisks

/-! Locally uniform o(n) errors of the actual full complex native Dirichlet
labels, in the ORIGINAL H^-1 potential topology and original positive index. -/
noncomputable section
open Set Complex Filter Topology Metric NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

/-- One original complex H^-1 neighborhood makes the scaled errors of ALL
high intrinsic Dirichlet labels arbitrarily small. The fixed Miura chart
and energy shift remain auxiliary proof data. -/
theorem HillHminusMiuraChart.exists_uniform_small_dirichletDisplacement
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    {delta : ℝ} (hd : 0 < delta) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ C.domain ∧
      ∀ a ∈ V, ∀ n : ℕ+, N < (n:ℕ) →
        ‖hillHminusDirichletComplexLabels a n-((Real.pi:ℂ)*(n:ℕ))^2‖ < delta*(n:ℝ) := by
  let r := min (Real.pi/4) (min 1 (delta/(2*(2*Real.pi+1))))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrpi : r ≤ Real.pi/4 := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrd : r*(2*Real.pi+1) ≤ delta/2 := by
    have h := (min_le_right (Real.pi/4) (min 1 (delta/(2*(2*Real.pi+1))))).trans
      (min_le_right _ _)
    have hp : 0 < 2*(2*Real.pi+1) := by positivity
    have hh := (le_div_iff₀ hp).mp h
    dsimp [r]
    nlinarith
  let T := auxiliaryPeriodOneDirichletPotential (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2:ℝ≥0∞))
  let F : PeriodOneHminusOne → dirichletSubspace (p := 2) :=
    fun a => T (hillMiuraDiagonal (C.lift a))
  have hF : AnalyticOnNhd ℂ F C.domain := by
    intro a ha
    exact (T.analyticAt _).comp ((hillMiuraDiagonal.analyticAt _).comp (C.lift_analytic a ha))
  obtain ⟨N₀,V₀,hN₀,hV₀,hq₀,hsub,hcontrol,_⟩ :=
    C.exists_uniform_analytic_dirichletControl q hq
  obtain ⟨N₁,U,_,hU,_,hqU,_,hsmall⟩ :=
    exists_uniform_small_canonicalBoundaryDisks (by simp) (by norm_num) (F q) hr hrpi
  obtain ⟨M,hM⟩ := exists_nat_gt (2*‖C.energyShift‖/delta)
  let N := max N₀ (max N₁ M)
  let V := V₀ ∩ (C.domain ∩ F ⁻¹' U)
  have hV : IsOpen V := hV₀.inter
    (hF.continuousOn.isOpen_inter_preimage C.domain_open hU)
  refine ⟨N,V,hN₀.trans_le (le_max_left _ _),hV,⟨hq₀,hq,hqU⟩,
    fun a ha => ha.2.1,?_⟩
  intro a ha n hn
  have hn₀ : N₀ < (n:ℕ) := (le_max_left _ _).trans_lt hn
  have hn₁ : N₁ < (n:ℕ) := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hn
  have hnM : M < (n:ℕ) := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hn
  have hdisk := hsmall (F a) ha.2.2 .dirichlet ((n:ℕ):ℤ) (by simpa using hn₁)
  have hz : ‖hillMiuraDiracDirichlet (C.lift a) (n:ℕ)-(Real.pi:ℂ)*(n:ℕ)‖ ≤ r := by
    have hh : ‖hillMiuraDiracDirichlet (C.lift a) (n:ℕ)-(Real.pi:ℂ)*(n:ℕ)‖ < r := by
      simpa only [F,T,hillMiuraDiracDirichlet,canonicalAuxiliaryPeriodOneRoots,Int.cast_natCast,
        mem_ball,dist_eq_norm] using hdisk
    exact hh.le
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast n.property
  have hc : ‖C.energyShift‖ < delta/2*(n:ℝ) := by
    have hMn : (M:ℝ) < (n:ℝ) := by exact_mod_cast hnM
    have hh := (div_lt_iff₀ hd).mp (hM.trans hMn)
    nlinarith
  rw [hillHminusDirichletComplexLabels_eq_tail_of_control a (C.lift a) C.energyShift
    N₀ (hcontrol a ha.1) n hn₀,hillMiuraDirichletEnergy]
  have hb := norm_squared_shift_displacement_le (hillMiuraDiracDirichlet (C.lift a) (n:ℕ))
    ((Real.pi:ℂ)*(n:ℕ)) C.energyShift
  have hw : ‖(Real.pi:ℂ)*(n:ℕ)‖ = Real.pi*(n:ℝ) := by
    simp [Real.pi_pos.le]
  rw [hw] at hb
  have hproduct : ‖hillMiuraDiracDirichlet (C.lift a) (n:ℕ)-(Real.pi:ℂ)*(n:ℕ)‖ *
      (2*(Real.pi*(n:ℝ))+‖hillMiuraDiracDirichlet (C.lift a) (n:ℕ)-(Real.pi:ℂ)*(n:ℕ)‖) ≤
      delta/2*(n:ℝ) := by
    calc
      _ ≤ r*(2*(Real.pi*(n:ℝ))+r) := by gcongr
      _ ≤ r*(2*Real.pi+1)*(n:ℝ) := by
        have hh : r ≤ (n:ℝ) := hr1.trans hn1
        nlinarith
      _ ≤ delta/2*(n:ℝ) := mul_le_mul_of_nonneg_right hrd (by positivity)
  linarith

/-- The local uniform o(n) asymptotic requires no supplied lift or chart. -/
theorem exists_uniform_small_hillHminusDirichletDisplacement
    (q : PeriodOneHminusOne) {delta : ℝ} (hd : 0 < delta) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ n : ℕ+, N < (n:ℕ) →
        ‖hillHminusDirichletComplexLabels a n-((Real.pi:ℂ)*(n:ℕ))^2‖ < delta*(n:ℝ) := by
  obtain ⟨N,V,hN,hV,hq,_,he⟩ :=
    (hillHminusMiuraChartAt q).exists_uniform_small_dirichletDisplacement q
      (mem_hillHminusMiuraChartAt q) hd
  exact ⟨N,V,hN,hV,hq,he⟩

end NLS.KdV
