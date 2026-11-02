import NLS.KdV.ClassicalRoughNormalizationCompatibility
import NLS.KdV.ClassicalNormalizedOddMoments
import NLS.ComplexAnalysis.DenseLinearAnalyticUniqueness

/-! # Actual all-mode odd normalized moments on a rough-open neighborhood

Exact continuous/rough compatibility, analytic uniqueness on the connected
linear preimage, and actual Fourier density transfer cancellation to the
whole rough ball. A bounded continuous-potential ball is not assumed dense.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_normalized_all_odd_moments :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      ∃ R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ AnalyticOnNhd ℂ R V ∧
        R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧ (∀ q ∈ V, ‖R q‖ ≤ 2) ∧
        (∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusNormalizedNumerator C N R n) (univ ×ˢ V)) ∧
        (∀ n : ℕ+, ∀ lambda : ℂ, hillHminusNormalizedNumerator C N R n (lambda,0) = classicalHillFreePsi n lambda) ∧
        (∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (hillHminusNormalizedMoment C N R n k m) V) ∧
        (∀ q ∈ V, ∀ n k : ℕ+,
          (2*(Real.pi : ℂ))⁻¹*hillHminusNormalizedMoment C N R n k 0 q = if n = k then 1 else 0) ∧
        (∀ q ∈ V, ∀ n k : ℕ+, ∀ l : ℕ, hillHminusNormalizedMoment C N R n k (2*l+1) q = 0) ∧
        ∃ A : ℝ, HillHminusUniformPeriodData C N V A := by
  obtain ⟨M,W,Tc,Rc,_,_,_,_,hRca,_,_,hinvc,hentryc,B,Dc⟩ := exists_classicalHill_analytic_period_inverse
  obtain ⟨Uo,_,hUo,h0Uo,_,hodd⟩ := Dc.exists_normalized_all_odd_moments Rc hRca
  obtain ⟨C,N,V,U,R,hN,hV,h0V,_,_,hU,h0U,hRa,hR0,hRn,hPsi,hFree,hZero,hMom,_,_,hCompat,A,Dr⟩ :=
    Dc.exists_rough_normalization_compatibility Tc Rc hentryc (fun q hq => (hinvc q hq).1)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
  let Z : Set PeriodOneHminusOne := ball 0 r
  have h0Z : (0 : PeriodOneHminusOne) ∈ Z := mem_ball_self hr
  refine ⟨C,N,Z,R,hN,isOpen_ball,h0Z,hRa.mono hball,hR0,fun q hq => hRn q (hball hq),
    fun n => (hPsi n).mono (fun _ ht => ⟨ht.1,hball ht.2⟩),hFree,
    fun n k m => (hMom n k m).mono hball,
    fun q hq n k => hZero n k q (hball hq),?_,A,Dr.mono hball isOpen_ball h0Z⟩
  intro q hq n k l
  have hnear : (fun a => hillHminusNormalizedMoment C N R n k (2*l+1) (classicalHillHminusInclusion a))
      =ᶠ[𝓝 (0 : Curve ℂ)] 0 := by
    filter_upwards [(hU.inter hUo).mem_nhds ⟨h0U,h0Uo⟩] with a ha
    exact (hCompat n k (2*l+1) a ha.1).trans (hodd a ha.2 n k l)
  exact eqOn_zero_of_dense_linear_pullback classicalHillHminusInclusion
    denseRange_classicalHillHminusInclusion Z isOpen_ball (convex_ball 0 r) h0Z
    (hillHminusNormalizedMoment C N R n k (2*l+1)) ((hMom n k _).mono hball) hnear hq

end NLS.KdV
