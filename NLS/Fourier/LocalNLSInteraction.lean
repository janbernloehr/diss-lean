import NLS.Fourier.CubicNLS
import NLS.SequenceSpaces.WeightedPhaseFlow
import Mathlib.Analysis.ODE.ExistUnique

/-! # Local existence in the NLS interaction representation

Removing the quadratic linear phases leaves a continuous time-dependent
field with uniform local Lipschitz estimates in each weighted ℓ¹ space.
Picard–Lindelöf constructs a solution on a positive two-sided time interval.
-/
noncomputable section
open Set Metric Filter Topology
open scoped NNReal
namespace NLS.Fourier

/-- The free period-one Schrödinger group with the physical NLS time sign. -/
def nlsFreeFlow (w : Weight) (time : ℝ) : WeightedCoeff w 1 →ₗᵢ[ℂ] WeightedCoeff w 1 :=
  WeightedCoeff.phaseFlow w (fun n => -(2*Real.pi*(n : ℝ))^2) time

@[simp] theorem nlsFreeFlow_zero (w : Weight) (a : WeightedCoeff w 1) : nlsFreeFlow w 0 a = a :=
  WeightedCoeff.phaseFlow_zero w _ a

@[simp] theorem norm_nlsFreeFlow (w : Weight) (time : ℝ) (a : WeightedCoeff w 1) :
    ‖nlsFreeFlow w time a‖ = ‖a‖ := (nlsFreeFlow w time).norm_map a

theorem nlsFreeFlow_add (w : Weight) (time r : ℝ) (a : WeightedCoeff w 1) :
    nlsFreeFlow w time (nlsFreeFlow w r a) = nlsFreeFlow w (time+r) a :=
  WeightedCoeff.phaseFlow_add w _ time r a

theorem continuous_nlsFreeFlow (w : Weight) :
    Continuous (fun x : ℝ × WeightedCoeff w 1 => nlsFreeFlow w x.1 x.2) :=
  WeightedCoeff.continuous_phaseFlow w (by simp) _

/-- The cubic NLS field after conjugation by the free Schrödinger group. -/
def nlsInteraction (w : SpectralWeight) (time : ℝ) (a : WeightedCoeff w.toWeight 1) :
    WeightedCoeff w.toWeight 1 :=
  nlsFreeFlow w.toWeight (-time) (cubicNLS w (nlsFreeFlow w.toWeight time a))

theorem continuous_nlsInteraction (w : SpectralWeight) :
    Continuous (fun x : ℝ × WeightedCoeff w.toWeight 1 => nlsInteraction w x.1 x.2) :=
by
  have hf : Continuous (fun x : ℝ × WeightedCoeff w.toWeight 1 =>
      cubicNLS w (nlsFreeFlow w.toWeight x.1 x.2)) :=
    (continuous_cubicNLS w).comp (continuous_nlsFreeFlow w.toWeight)
  have hg : Continuous (fun x : ℝ × WeightedCoeff w.toWeight 1 =>
      (-x.1,cubicNLS w (nlsFreeFlow w.toWeight x.1 x.2))) := continuous_fst.neg.prodMk hf
  have h := (continuous_nlsFreeFlow w.toWeight).comp hg
  simpa only [Function.comp_def,nlsInteraction] using h

/-- The interaction field has the same cubic bound at every real time. -/
theorem norm_nlsInteraction_le (w : SpectralWeight) (time : ℝ) (a : WeightedCoeff w.toWeight 1) :
    ‖nlsInteraction w time a‖ ≤ 2*‖a‖^3 := by
  simpa only [nlsInteraction,norm_nlsFreeFlow] using
    norm_cubicNLS_le w (nlsFreeFlow w.toWeight time a)

/-- Its Lipschitz constant on a bounded ball is independent of time. -/
theorem norm_nlsInteraction_sub_le (w : SpectralWeight) (time R : ℝ)
    (a b : WeightedCoeff w.toWeight 1) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖nlsInteraction w time a-nlsInteraction w time b‖ ≤ 6*R^2*‖a-b‖ := by
  have h := norm_cubicNLS_sub_le w R (nlsFreeFlow w.toWeight time a) (nlsFreeFlow w.toWeight time b)
    (by simpa only [norm_nlsFreeFlow] using ha) (by simpa only [norm_nlsFreeFlow] using hb)
  simpa only [nlsInteraction,← map_sub,norm_nlsFreeFlow] using h

/-- Every weighted ℓ¹ initial datum has a local interaction solution. -/
theorem exists_local_nlsInteraction (w : SpectralWeight) (a : WeightedCoeff w.toWeight 1) :
    ∃ T > 0, ∃ v : ℝ → WeightedCoeff w.toWeight 1, v 0 = a ∧
      ∀ time ∈ Icc (-T) T, HasDerivWithinAt v (nlsInteraction w time (v time)) (Icc (-T) T) time := by
  let R : ℝ := ‖a‖+1
  have hR : 0 < R := by dsimp [R]; positivity
  let L : ℝ≥0 := ⟨2*R^3,by positivity⟩
  let K : ℝ≥0 := ⟨6*R^2,by positivity⟩
  let T : ℝ := 1/(L+1)
  have hT : 0 < T := by dsimp [T]; positivity
  have hbound (b : WeightedCoeff w.toWeight 1) (hb : b ∈ closedBall a 1) : ‖b‖ ≤ R := by
    have hd : ‖b-a‖ ≤ 1 := mem_closedBall_iff_norm.mp hb
    exact (norm_le_norm_sub_add b a).trans (by dsimp [R]; linarith)
  have hPL : IsPicardLindelof (nlsInteraction w) (tmin := -T) (tmax := T)
      ⟨0,by constructor <;> linarith⟩ a 1 0 L K := by
    constructor
    · intro time _
      apply LipschitzOnWith.of_dist_le_mul
      intro b hb c hc
      simpa only [dist_eq_norm,K,NNReal.coe_mk] using! norm_nlsInteraction_sub_le w time R b c (hbound b hb) (hbound c hc)
    · intro b _
      exact ((continuous_nlsInteraction w).comp (continuous_id.prodMk continuous_const)).continuousOn
    · intro time _ b hb
      exact (norm_nlsInteraction_le w time b).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg b) (hbound b hb) 3) (by norm_num))
    · change (L : ℝ)*max (T-0) (0- -T) ≤ (1 : ℝ)-(0 : ℝ)
      simp only [sub_zero,zero_sub,neg_neg,max_self]
      dsimp [T]
      rw [mul_one_div,div_le_one (by positivity)]
      linarith
  obtain ⟨v,hv0,hv⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨T,hT,v,hv0,hv⟩

end NLS.Fourier
