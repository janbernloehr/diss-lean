import NLS.KdV.HillHminusOneAllGapSquares
import NLS.KdV.HillHminusOneFinitePeriodExtensions
import NLS.ComplexAnalysis.PhysicalCutCubicSign

/-! # Nonpositivity of every actual H^-1 canonical cubic period

The whole-gap filled square is nonnegative on the real cut. The global
physical half-plane signs fix the upper-minus-lower jump, so the literal
counterclockwise cubic period is nonpositive at every positive index,
including central and collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusRealGapCubicContourMoment_nonpositive
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    (hillHminusRealGapCubicContourMoment q hr n).re ≤ 0 ∧
      (hillHminusRealGapCubicContourMoment q hr n).im = 0 := by
  obtain ⟨hd,hη,hl,hu,hsub⟩ := hillHminusRealGapContour_geometry q hr (n : ℕ) n.property
  let c := hillHminusRealGapCenter q hr (n : ℕ)
  let d := hillHminusRealGapHalfLength q hr (n : ℕ)
  let η := hillHminusRealGapCollar q hr (n : ℕ)
  have hcd : c-d = hillHminusRealLabels q hr (2*(n : ℕ)-1) := hl
  have hcp : c+d = hillHminusRealLabels q hr (2*(n : ℕ)) := hu
  let f : ℂ → ℂ := fun z => hillHminusRealCutPrimitive q z+I*(n : ℂ)*Real.pi
  let g := hillHminusRealGapPrimitiveSquare q (n : ℕ)
  have hf : AnalyticOnNhd ℂ f
      (ball (c : ℂ) (d+2*η) \ segment ℝ (hillHminusRealLabels q hr (2*(n : ℕ)-1) : ℂ)
        (hillHminusRealLabels q hr (2*(n : ℕ)) : ℂ)) :=
    ((analyticOnNhd_hillHminusRealCutPrimitive q hr).mono hsub).add analyticOnNhd_const
  have hg : AnalyticOnNhd ℂ g (ball (c : ℂ) (d+2*η)) :=
    analyticOnNhd_hillHminusRealGapPrimitiveSquare q hr (n : ℕ) n.property
  have hprofile (x : ℝ) (hx : x ∈ Icc (c-d) (c+d)) :
      g x = (hillHminusRealGapProfile q (n : ℕ) x : ℂ)^2 := by
    apply hillHminusRealGapPrimitiveSquare_on_gap q hr (n : ℕ) n.property x
    simpa only [hcd,hcp] using hx
  have hfre (z : ℂ) (hi : z.im ≠ 0) : (f z).re = (hillHminusContinuedPrimitive (z,q)).re := by
    simp [f,hillHminusRealCutPrimitive,hi]
  have hsign := circleIntegral_cubic_re_nonpos_of_physical_cut_square f g c d (d+η) (d+2*η)
    hd (by linarith) (by linarith)
    (by simpa only [hcd,hcp] using hf) hg (fun _ _ => rfl)
    (fun x hx => by rw [hprofile x hx,← ofReal_pow,ofReal_im])
    (fun x hx => by rw [hprofile x hx,← ofReal_pow,ofReal_re]; exact sq_nonneg _)
    (fun z _ hi => by rw [hfre z hi.ne']; exact hillHminusContinuedPrimitive_re_pos q hr z hi)
    (fun z _ hi => by rw [hfre z hi.ne]; exact hillHminusContinuedPrimitive_re_neg q hr z hi)
  have hraw : hillHminusRealGapCubicContourMoment q hr n =
      (Real.pi : ℂ)⁻¹ * ∮ z in C((c : ℂ),d+η), f z^3 := rfl
  rw [hraw]
  constructor
  · simpa only [← ofReal_inv,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero] using
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr Real.pi_pos.le) hsign.1
  · simp only [← ofReal_inv,mul_im,ofReal_re,ofReal_im,hsign.2,mul_zero,zero_mul,add_zero]

/-- Simultaneous finite-head analyticity retains the actual cubic sign at
all nearby real inputs, including low indices and repeated endpoints. -/
theorem exists_hillHminus_finite_nonpositive_period_extensions
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (S : Finset ℕ+) :
    ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ q ∈ W ∧
      ∃ A : ℕ+ → ℕ → PeriodOneHminusOne → ℂ, ∃ R : ℕ+ → PeriodOneHminusOne → ℂ,
        ∀ n ∈ S, (∀ m, AnalyticOnNhd ℂ (A n m) W) ∧ AnalyticOnNhd ℂ (R n) W ∧
          ∀ p ∈ W, ∀ hp : IsRealPeriodOneHminusOne p,
            (∀ m, A n m p = hillHminusRealGapContourMoment p hp n m) ∧
            R n p = hillHminusRealGapCubicContourMoment p hp n ∧
            (R n p).re ≤ 0 ∧ (R n p).im = 0 := by
  obtain ⟨W,hW,hq,A,R,hdata⟩ := exists_hillHminus_finite_canonical_period_extensions q hr S
  refine ⟨W,hW,hq,A,R,?_⟩
  intro n hn
  obtain ⟨hA,hR,hreal⟩ := hdata n hn
  refine ⟨hA,hR,?_⟩
  intro p hp hpr
  obtain ⟨hAm,hRm⟩ := hreal p hp hpr
  refine ⟨hAm,hRm,?_⟩
  rw [hRm]
  exact hillHminusRealGapCubicContourMoment_nonpositive p hpr n

end NLS.KdV
