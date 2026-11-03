import NLS.KdV.HillHminusOneAllRealPeriods
import NLS.ComplexAnalysis.CompactCoordinateContinuation
import Mathlib.Topology.MetricSpace.Thickening

/-! # A jointly analytic actual-primitive germ around every canonical gap circle

Invert the hyperbolic trace in the uniform norm on a compact collar of the
circle. The full reference primitive fixes all logarithm values at once,
retaining its additive period. The open collar and complex potential
neighborhood precede every contour point; no central index is omitted.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_joint_contour_primitive
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧
      sphere (hillHminusRealGapCenter q hr (n : ℕ) : ℂ)
        (hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)) ⊆ Ω ∧
      Ω ⊆ hillHminusRealCutDomain q hr ∧
      ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧ ∃ F : ℂ × PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ F (Ω ×ˢ V) ∧
        (∀ z ∈ Ω, F (z,q) = hillHminusRealCutPrimitive q z) ∧
        ∀ t ∈ Ω ×ˢ V, 2 * cosh (F t) = hillHminusDiscriminant t.2 t.1 ∧ sinh (F t) ≠ 0 := by
  let S := sphere (hillHminusRealGapCenter q hr (n : ℕ) : ℂ)
    (hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ))
  have hS : IsCompact S := isCompact_sphere _ _
  have hSU : S ⊆ hillHminusRealCutDomain q hr :=
    hillHminusRealGapContour_sphere_subset q hr (n : ℕ) n.property
  obtain ⟨δ,hδ,hδU⟩ := hS.exists_cthickening_subset_open
    (isOpen_hillHminusRealCutDomain q hr) hSU
  let K := cthickening δ S
  let Ω := thickening δ S
  have hK : IsCompact K := hS.cthickening
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hΩ : IsOpen Ω := isOpen_thickening
  have hΩK : Ω ⊆ K := thickening_subset_cthickening δ S
  have hKU : K ⊆ hillHminusRealCutDomain q hr := hδU
  let u : C(K,ℂ) := ⟨fun z => hillHminusRealCutPrimitive q z,
    continuousOn_iff_continuous_domRestrict.mp
      ((analyticOnNhd_hillHminusRealCutPrimitive q hr).continuousOn.mono hKU)⟩
  have hu (z : K) : deriv cosh (u z) ≠ 0 := by
    rw [(Complex.hasDerivAt_cosh (u z)).deriv]
    intro hz
    have hne := hillHminusRealCutRoot_ne_zero q hr z (hKU z.property)
    apply hne
    change 2 * sinh (u z) = 0
    rw [hz,mul_zero]
  let D : ℂ × PeriodOneHminusOne → ℂ := fun t => hillHminusDiscriminant t.2 t.1 / 2
  have hD : AnalyticOnNhd ℂ D univ := by
    intro t _
    exact (analyticOnNhd_hillHminusDiscriminant_joint t (mem_univ _)).div_const
  have hbase (z : K) : D (z,q) = cosh (u z) := by
    have ht := hillHminusRealCutPrimitive_trace q hr z (hKU z.property)
    change hillHminusDiscriminant q z / 2 = cosh (hillHminusRealCutPrimitive q z)
    linear_combination -ht / 2
  have hcosh : AnalyticOnNhd ℂ cosh univ := fun _ _ => Complex.analyticAt_cosh
  obtain ⟨V,hV,hq,F,hF,hbaseF,hdata⟩ :=
    exists_joint_compact_coordinate_continuation K Ω hΩ hΩK cosh hcosh u hu D hD q hbase
  refine ⟨Ω,hΩ,self_subset_thickening hδ S,hΩK.trans hKU,V,hV,hq,F,hF,?_,?_⟩
  · intro z hz
    exact hbaseF ⟨z,hΩK hz⟩
  · intro t ht
    have hd := hdata t ht
    constructor
    · have he : cosh (F t) = hillHminusDiscriminant t.2 t.1 / 2 := hd.1
      linear_combination 2 * he
    · simpa only [(Complex.hasDerivAt_cosh (F t)).deriv] using hd.2

end NLS.KdV
