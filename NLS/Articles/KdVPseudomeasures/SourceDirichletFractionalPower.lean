import NLS.KdV.HminusOneFractionalDirichletProjections
import NLS.KdV.HillFractionalPeriodOneExtraction
import NLS.KdV.SingularDirichletProjectionAnalytic

/-! Locally uniform power bounds on the original complex Sobolev scale.
The period-one extraction is defined on the whole ambient space; for
physical period-one inputs it reconstructs the identical distribution.
-/
noncomputable section
open Set Metric Complex NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat

def sourceFractionalNative (r : ℝ) (hr1 : r ≤ 1) :
    FourierLebesgueSpace (2:ℝ) (-r) 2 →L[ℂ] PeriodOneHminusOne :=
  periodOneOriginalExtract.comp (hillSobolevBaseInclusion r hr1)

def sourceFractionalPeriodOneCoefficients (r : ℝ) (hr1 : r ≤ 1) :
    FourierLebesgueSpace (2:ℝ) (-r) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (-r)) 2 :=
  (hillFractionalPeriodOneExtract r hr1).comp
    (sobolevCoefficients (-r) 2).toContinuousLinearEquiv.toContinuousLinearMap

theorem sourceFractionalNative_coefficients (r : ℝ) (hr1 : r ≤ 1)
    (q : FourierLebesgueSpace (2:ℝ) (-r) 2) :
    sobolevInclusion (show (-1:ℝ) ≤ -r by linarith)
        (sourceFractionalPeriodOneCoefficients r hr1 q) = sourceFractionalNative r hr1 q :=
  hillFractionalPeriodOneExtract_native r hr1 (sobolevCoefficients (-r) 2 q)

theorem norm_sourceFractionalPeriodOneCoefficients_le (r : ℝ) (hr1 : r ≤ 1)
    (q : FourierLebesgueSpace (2:ℝ) (-r) 2) :
    ‖sourceFractionalPeriodOneCoefficients r hr1 q‖ ≤ 2*‖q‖ := by
  exact (norm_hillFractionalPeriodOneExtract_le r hr1 _).trans_eq
    (by
      change 2*‖sobolevCoefficients (-r) 2 q‖ = 2*‖q‖
      rw [LinearIsometryEquiv.norm_map])

def sourceFractionalDirichletProjectionError (r : ℝ) (hr1 : r ≤ 1)
    (n : ℕ+) (q : FourierLebesgueSpace (2:ℝ) (-r) 2) :
    IntervalL2 →L[ℂ] C(Icc (0:ℝ) 1,ℂ) :=
  singularDirichletContinuousRieszProjection
      (periodOneOriginal (sourceFractionalNative r hr1 q)) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
    singularDirichletContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)

theorem sourceFractionalDirichletProjectionError_zero (r : ℝ) (hr1 : r ≤ 1) (n : ℕ+) :
    sourceFractionalDirichletProjectionError r hr1 n 0 = 0 := by
  unfold sourceFractionalDirichletProjectionError
  rw [map_zero,map_zero]
  exact _root_.sub_self (singularDirichletContinuousRieszProjection
    (0 : FourierLebesgueSpace (2:ℝ) (-1) 2) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ))

theorem exists_local_sourceFractionalDirichletProjection_power_bound
    (r : ℝ) (hr : 1/2 < r) (hr1 : r < 1)
    (q : FourierLebesgueSpace (2:ℝ) (-r) 2) :
    ∃ N : ℕ, ∃ U : Set (FourierLebesgueSpace (2:ℝ) (-r) 2), ∃ B : ℝ,
      IsOpen U ∧ q ∈ U ∧ 0 ≤ B ∧ ∀ n : ℕ+, N ≤ (n:ℕ) →
        AnalyticOnNhd ℂ (sourceFractionalDirichletProjectionError r hr1.le n) U ∧
        ∀ b ∈ U, ‖sourceFractionalDirichletProjectionError r hr1.le n b‖ ≤ B*(n:ℝ)^(-(1-r)) := by
  let G := sourceFractionalNative r hr1.le
  let M := 2*(‖q‖+1)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  obtain ⟨N₀,V₀,B,_,hV₀,hq₀,hB,hbound⟩ :=
    exists_local_fractional_hillHminusDirichletProjection_bound (G q) r hr hr1 M hM
  obtain ⟨N₁,V₁,_,hV₁,hq₁,_,hcircles⟩ := exists_uniform_hillHminusDirichlet_sourceCircles (G q)
  let U := ball q 1 ∩ G ⁻¹' (V₀ ∩ V₁)
  have hU : IsOpen U := isOpen_ball.inter ((hV₀.inter hV₁).preimage G.continuous)
  refine ⟨max N₀ N₁+1,U,B,hU,⟨mem_ball_self (by norm_num),hq₀,hq₁⟩,hB,?_⟩
  intro n hn
  have hn₀ : N₀ < (n:ℕ) := by omega
  have hn₁ : N₁ < (n:ℕ) := by omega
  have hcircle : ∀ b ∈ U, sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆
      singularDirichletResolventSet (periodOneOriginal (G b)) := by
    intro b hb
    exact (hcircles (G b) hb.2.2 n hn₁).1
  have han := analyticOnNhd_singularDirichletContinuousRieszProjection_comp
    (periodOneOriginal.comp G) U hU (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) (by positivity) hcircle
  refine ⟨fun b hb => (han b hb).sub analyticAt_const,?_⟩
  intro b hb
  have hbnorm : ‖b‖ ≤ ‖q‖+1 := by
    have hd : ‖b-q‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hb.1
    have ht := norm_add_le (b-q) q
    rw [sub_add_cancel] at ht
    linarith
  have hcoeff : ‖sourceFractionalPeriodOneCoefficients r hr1.le b‖ ≤ M :=
    (norm_sourceFractionalPeriodOneCoefficients_le r hr1.le b).trans
      (mul_le_mul_of_nonneg_left hbnorm (by norm_num))
  have heq := sourceFractionalNative_coefficients r hr1.le b
  have hh := hbound (sourceFractionalPeriodOneCoefficients r hr1.le b) hcoeff
    (by rw [heq]; exact hb.2.1) n hn₀
  rw [heq] at hh
  exact hh

end NLS.Articles.KdVPseudomeasures
