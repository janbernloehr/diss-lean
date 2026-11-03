import NLS.KdV.HillHminusOneJointContourPrimitive
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! # Analytic germs of the actual H^-1 gap periods at every positive index

A single trace-normalized primitive collar yields all polynomial moments
and the shifted cubic moment on the same complex potential neighborhood.
At the reference real potential they are the literal canonical periods,
with the original counterclockwise normalization and no extra factor i.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_analytic_gap_period_germs
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧
      sphere (hillHminusRealGapCenter q hr (n : ℕ) : ℂ)
        (hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)) ⊆ Ω ∧
      ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧
        ∃ F : ℂ × PeriodOneHminusOne → ℂ,
          AnalyticOnNhd ℂ F (Ω ×ˢ V) ∧
          (∀ z ∈ Ω, F (z,q) = hillHminusRealCutPrimitive q z) ∧
          (∀ t ∈ Ω ×ˢ V, 2 * cosh (F t) = hillHminusDiscriminant t.2 t.1 ∧ sinh (F t) ≠ 0) ∧
          ∃ A : ℕ → PeriodOneHminusOne → ℂ, ∃ R : PeriodOneHminusOne → ℂ,
            (∀ m p, A m p = -(Real.pi : ℂ)⁻¹ * ∮ z in C(
              (hillHminusRealGapCenter q hr (n : ℕ) : ℂ),
              hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)),
                z^m * F (z,p)) ∧
            (∀ p, R p = (Real.pi : ℂ)⁻¹ * ∮ z in C(
              (hillHminusRealGapCenter q hr (n : ℕ) : ℂ),
              hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)),
                (F (z,p)+I*(n : ℂ)*Real.pi)^3) ∧
            (∀ m, AnalyticOnNhd ℂ (A m) V ∧ A m q = hillHminusRealGapContourMoment q hr n m) ∧
            AnalyticOnNhd ℂ R V ∧ R q = hillHminusRealGapCubicContourMoment q hr n := by
  obtain ⟨Ω,hΩ,hcircle,_,V,hV,hq,F,hF,hbase,htrace⟩ :=
    exists_hillHminus_joint_contour_primitive q hr n
  let c : ℂ := hillHminusRealGapCenter q hr (n : ℕ)
  let r := hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)
  have hradius : 0 ≤ r := (hillHminusRealGapContourRadius_pos q hr n).le
  let A : ℕ → PeriodOneHminusOne → ℂ := fun m p =>
    -(Real.pi : ℂ)⁻¹ * ∮ z in C(c,r), z^m * F (z,p)
  let R : PeriodOneHminusOne → ℂ := fun p =>
    (Real.pi : ℂ)⁻¹ * ∮ z in C(c,r), (F (z,p)+I*(n : ℂ)*Real.pi)^3
  refine ⟨Ω,hΩ,hcircle,V,hV,hq,F,hF,hbase,htrace,A,R,fun _ _ => rfl,fun _ => rfl,?_,?_,?_⟩
  · intro m
    constructor
    · have hi := analyticOnNhd_circleIntegral_of_jointAnalytic
        (fun t : ℂ × PeriodOneHminusOne => t.1^m * F t) (hΩ.prod hV)
        (fun t ht => (analyticAt_fst.pow m).mul (hF t ht)) c r hradius hV
        (fun p hp z hz => ⟨hcircle hz,hp⟩)
      intro p hp
      exact analyticAt_const.mul (hi p hp)
    · change -(Real.pi : ℂ)⁻¹ * (∮ z in C(c,r), z^m * F (z,q)) =
        -(Real.pi : ℂ)⁻¹ * (∮ z in C(c,r), z^m * hillHminusRealCutPrimitive q z)
      congr 1
      apply circleIntegral.integral_congr hradius
      intro z hz
      dsimp only
      rw [hbase z (hcircle hz)]
  · have hi := analyticOnNhd_circleIntegral_of_jointAnalytic
      (fun t : ℂ × PeriodOneHminusOne => (F t+I*(n : ℂ)*Real.pi)^3) (hΩ.prod hV)
      (fun t ht => ((hF t ht).add analyticAt_const).pow 3) c r hradius hV
      (fun p hp z hz => ⟨hcircle hz,hp⟩)
    intro p hp
    exact analyticAt_const.mul (hi p hp)
  · change (Real.pi : ℂ)⁻¹ * (∮ z in C(c,r), (F (z,q)+I*(n : ℂ)*Real.pi)^3) =
      (Real.pi : ℂ)⁻¹ * (∮ z in C(c,r), (hillHminusRealCutPrimitive q z+I*(n : ℂ)*Real.pi)^3)
    congr 1
    apply circleIntegral.integral_congr hradius
    intro z hz
    dsimp only
    rw [hbase z (hcircle hz)]

end NLS.KdV
