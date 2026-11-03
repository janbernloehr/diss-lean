import NLS.KdV.HillHminusOneGapCoordinateRegularity
import NLS.ComplexAnalysis.CompactCoordinateContinuation

/-! # Jointly analytic filled H^-1 Hill gap squares at every index

The inverse squared-cosh coordinate acts on the full compact disc at once.
The resulting analytic family agrees with the actual filled square on the
entire reference disc, including central endpoints and collapsed gaps.
Its one complex potential neighborhood is chosen before all energies.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_joint_gap_square_on_disc
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (n : ℕ) (hn : 1 ≤ n) (R : ℝ)
    (hR : R < hillHminusRealGapHalfLength q hr n + 2 * hillHminusRealGapCollar q hr n) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧ ∃ K : ℂ × PeriodOneHminusOne → ℂ,
      AnalyticOnNhd ℂ K (ball (hillHminusRealGapCenter q hr n : ℂ) R ×ˢ V) ∧
      (∀ z ∈ closedBall (hillHminusRealGapCenter q hr n : ℂ) R,
        K (z,q) = hillHminusRealGapPrimitiveSquare q n z) ∧
      ∀ t ∈ ball (hillHminusRealGapCenter q hr n : ℂ) R ×ˢ V,
        coshSquareCoordinate (K t) = (-1 : ℂ)^n * hillHminusDiscriminant t.2 t.1 / 2 ∧
          deriv coshSquareCoordinate (K t) ≠ 0 := by
  let S := closedBall (hillHminusRealGapCenter q hr n : ℂ) R
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hsub : S ⊆ ball (hillHminusRealGapCenter q hr n : ℂ)
      (hillHminusRealGapHalfLength q hr n + 2 * hillHminusRealGapCollar q hr n) :=
    closedBall_subset_ball hR
  let u : C(S,ℂ) := ⟨fun z => hillHminusRealGapPrimitiveSquare q n z,
    continuousOn_iff_continuous_domRestrict.mp
      ((analyticOnNhd_hillHminusRealGapPrimitiveSquare q hr n hn).continuousOn.mono hsub)⟩
  have hu : ∀ z : S, deriv coshSquareCoordinate (u z) ≠ 0 := by
    intro z
    exact deriv_coshSquareCoordinate_hillHminusRealGapPrimitiveSquare_ne_zero q hr n hn z
      (hsub z.property)
  let D : ℂ × PeriodOneHminusOne → ℂ :=
    fun t => (-1 : ℂ)^n * hillHminusDiscriminant t.2 t.1 / 2
  have hD : AnalyticOnNhd ℂ D univ := by
    intro t _
    exact (analyticAt_const.mul (analyticOnNhd_hillHminusDiscriminant_joint t (mem_univ _))).div_const
  have hbase (z : S) : D (z,q) = coshSquareCoordinate (u z) :=
    (hillHminusRealGapPrimitiveSquare_cosh q hr n z).symm
  obtain ⟨V,hV,hq,K,hK,hbaseK,hdata⟩ := exists_joint_compact_coordinate_continuation S
    (ball (hillHminusRealGapCenter q hr n : ℂ) R) isOpen_ball ball_subset_closedBall
    coshSquareCoordinate analyticOnNhd_coshSquareCoordinate u hu D hD q hbase
  refine ⟨V,hV,hq,K,hK,?_,hdata⟩
  intro z hz
  exact hbaseK ⟨z,hz⟩

/-- A single joint analytic square on a disc strictly enclosing the canonical
integration circle, for every positive gap index, including collisions. -/
theorem exists_hillHminus_joint_filled_gap_square
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ R : ℝ,
      hillHminusRealGapHalfLength q hr n + hillHminusRealGapCollar q hr n < R ∧
      R < hillHminusRealGapHalfLength q hr n + 2 * hillHminusRealGapCollar q hr n ∧
      ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧ ∃ K : ℂ × PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ K (ball (hillHminusRealGapCenter q hr n : ℂ) R ×ˢ V) ∧
        (∀ z ∈ closedBall (hillHminusRealGapCenter q hr n : ℂ) R,
          K (z,q) = hillHminusRealGapPrimitiveSquare q n z) ∧
        ∀ t ∈ ball (hillHminusRealGapCenter q hr n : ℂ) R ×ˢ V,
          coshSquareCoordinate (K t) = (-1 : ℂ)^n * hillHminusDiscriminant t.2 t.1 / 2 ∧
            deriv coshSquareCoordinate (K t) ≠ 0 := by
  obtain ⟨_,hη,_,_,_⟩ := hillHminusRealGapContour_geometry q hr n hn
  let R := hillHminusRealGapHalfLength q hr n + 3 * hillHminusRealGapCollar q hr n / 2
  have houter : R < hillHminusRealGapHalfLength q hr n + 2 * hillHminusRealGapCollar q hr n := by
    dsimp only [R]
    linarith
  refine ⟨R,?_,houter,exists_hillHminus_joint_gap_square_on_disc q hr n hn R houter⟩
  dsimp only [R]
  linarith

end NLS.KdV
