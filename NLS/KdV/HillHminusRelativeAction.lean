import NLS.KdV.HillHminusRelativeRoot
import NLS.ComplexAnalysis.JointSpectralDerivativeAnalytic
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! Relative fixed-circle actions use the actual entire H-minus-one trace
and the root normalized by the original physical energy product. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillHminusRelativeActionIntegrand (t : ℂ × PeriodOneHminusOne) : ℂ :=
  t.1 * deriv (hillHminusDiscriminant t.2) t.1 / hillHminusRelativeRoot q hq hr t

theorem analyticOnNhd_hillHminusRelativeActionIntegrand :
    AnalyticOnNhd ℂ (hillHminusRelativeActionIntegrand q hq hr)
      (hillHminusRelativeRootDomain q hq hr) := by
  have hd := analyticOnNhd_spectral_deriv_of_analyticOnNhd
    (fun t : ℂ × PeriodOneHminusOne => hillHminusDiscriminant t.2 t.1)
    univ isOpen_univ analyticOnNhd_hillHminusDiscriminant_joint
  intro t ht
  exact (analyticAt_fst.mul (hd t (mem_univ _))).div
    (analyticOnNhd_hillHminusRelativeRoot q hq hr t ht)
    (hillHminusRelativeRoot_ne_zero q hq hr t ht)

def hillHminusRelativeAction (n : ℕ) (a : PeriodOneHminusOne) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∮ z in C((hillRealGapCenter q hq hr n : ℂ),
      hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n),
    hillHminusRelativeActionIntegrand q hq hr (z,a)

/-- A single complex H-minus-one neighborhood works for the whole fixed
energy contour, including at low indices and collapsed selected gaps. -/
theorem exists_hillHminusRelativeAction_analytic_neighborhood
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ hillOriginalHminusSource q ∈ U ∧
      AnalyticOnNhd ℂ (hillHminusRelativeAction q hq hr n) U ∧
      ∀ a ∈ U, ∀ z ∈ sphere (hillRealGapCenter q hq hr n : ℂ)
          (hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n),
        (z,a) ∈ hillHminusRelativeRootDomain q hq hr := by
  let c := (hillRealGapCenter q hq hr n : ℂ)
  let R := hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n
  have hR : 0 ≤ R := add_nonneg (hillRealGapContour_geometry q hq hr n hn).1
    (hillRealGapContour_geometry q hq hr n hn).2.1.le
  have hslice : sphere c R ×ˢ ({hillOriginalHminusSource q} : Set PeriodOneHminusOne) ⊆
      hillHminusRelativeRootDomain q hq hr := by
    rintro ⟨z,a⟩ ⟨hz,ha⟩
    rcases mem_singleton_iff.mp ha with rfl
    exact mem_hillHminusRelativeRootDomain_base q hq hr z
      (hillRealGapContour_sphere_subset q hq hr n hn hz)
  obtain ⟨W,U,_,hU,hKW,hqU,hWU⟩ := generalized_tube_lemma
    (isCompact_sphere c R) isCompact_singleton
    (isOpen_hillHminusRelativeRootDomain q hq hr) hslice
  have hcircle : ∀ a ∈ U, ∀ z ∈ sphere c R,
      (z,a) ∈ hillHminusRelativeRootDomain q hq hr :=
    fun a ha z hz => hWU ⟨hKW hz,ha⟩
  refine ⟨U,hU,hqU (mem_singleton _),?_,hcircle⟩
  exact analyticOnNhd_const.mul (analyticOnNhd_circleIntegral_of_jointAnalytic
    (hillHminusRelativeActionIntegrand q hq hr)
    (isOpen_hillHminusRelativeRootDomain q hq hr)
    (analyticOnNhd_hillHminusRelativeActionIntegrand q hq hr) c R hR hU hcircle)

end NLS.KdV
