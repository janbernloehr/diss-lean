import NLS.KdV.InnerFrequencyCircleResolvent
import NLS.KdV.HillHminusOneInnerDifferentialBound
import NLS.KdV.HillHminusOneNormalizedNumeratorSequence
import NLS.KdV.HillHminusOneSmallCriticalControl
/-! # Uniform full Hilbert norm decay of actual normalized densities

The literal filled critical numerator identity and the actual period-inverse
transpose give C/k decay for all output indices together, on one complex
H^-1 neighborhood before every positive inner contour, including the own mode.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem normalized_density_bound_of_critical_control
    (R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2))
    (q : PeriodOneHminusOne) (hq : q ∈ V) (hR : ‖R q‖ ≤ 2)
    (hcrit : ∀ m : ℕ+, ‖sqrt (hillHminusUniformCriticalPoint C N m q)-(Real.pi : ℂ)*(m : ℕ)‖ ≤ Real.pi/16)
    (k : ℕ+) (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/8)) :
    ‖(hillHminusContinuedRoot (z^2,q))⁻¹ • hillHminusNormalizedNumeratorSequence C N R (z^2,q)‖ ≤
      (192/Real.pi)*‖hillHminusDiscriminantDerivative (z^2,q)/hillHminusContinuedRoot (z^2,q)‖ := by
  let a := (hillHminusContinuedRoot (z^2,q))⁻¹ • hillHminusNumeratorHilbert C N (z^2,q)
  let H := (2*Real.pi)*‖hillHminusDiscriminantDerivative (z^2,q)/hillHminusContinuedRoot (z^2,q)‖
  have ha : ‖a‖ ≤ (48/Real.pi^2)*H := by
    apply innerFrequencyCircle_hilbert_norm_bound
      (fun m => hillHminusUniformCriticalPoint C N m q) hcrit k z hz a H (by positivity)
    · intro m
      have hne := (innerFrequencyCircle_resolvent_bound
        (fun j => hillHminusUniformCriticalPoint C N j q) hcrit k m z hz).1
      have hnum : hillHminusUniformNumerator C N m (z^2,q) =
          (2*(m : ℂ)*Real.pi)*hillHminusDiscriminantDerivative (z^2,q)/
            (z^2-hillHminusUniformCriticalPoint C N m q) := by
        apply (eq_div_iff hne).mpr
        exact (mul_comm _ _).trans (D.numerator_factor m q hq (z^2))
      have he : hillHminusUniformNumerator C N m (z^2,q)/hillHminusContinuedRoot (z^2,q) =
          (2*(Real.pi : ℂ))*(hillHminusDiscriminantDerivative (z^2,q)/hillHminusContinuedRoot (z^2,q))*
            ((m : ℂ)/(z^2-hillHminusUniformCriticalPoint C N m q)) := by
        rw [hnum]
        ring
      change ‖(hillHminusContinuedRoot (z^2,q))⁻¹ * hillHminusNumeratorHilbert C N (z^2,q) (m : ℤ)‖ ≤ _
      rw [D.numeratorHilbert_positive _ ⟨mem_univ _,hq⟩ m,← div_eq_inv_mul,he,
        norm_mul,norm_mul,norm_mul,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    · intro j hj
      change (hillHminusContinuedRoot (z^2,q))⁻¹ * hillHminusNumeratorHilbert C N (z^2,q) j = 0
      rw [D.numeratorHilbert_spec.1 _ ⟨mem_univ _,hq⟩ j,hillHminusNumeratorCoordinates,
        dif_neg (by omega : ¬0 < j),mul_zero]
  have htranspose : (hillHminusContinuedRoot (z^2,q))⁻¹ • hillHminusNormalizedNumeratorSequence C N R (z^2,q) =
      Coeff.hilbertMatrixTranspose (R q) a := by
    rw [hillHminusNormalizedNumeratorSequence,map_smul]
  rw [htranspose]
  calc
    _ ≤ ‖R q‖*‖a‖ := Coeff.norm_hilbertMatrixTranspose_apply_le _ _
    _ ≤ 2*((48/Real.pi^2)*H) := mul_le_mul hR ha (norm_nonneg _) (by norm_num)
    _ = _ := by dsimp only [H]; field_simp; ring

theorem exists_uniform_inner_normalized_density_bound
    (R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2))
    (hR : ∀ q ∈ V, ‖R q‖ ≤ 2) :
    ∃ U : Set PeriodOneHminusOne, U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 < K ∧ ∀ q ∈ U, ∀ k : ℕ+,
        ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/8),
          (z^2,q) ∈ hillHminusContinuationDomain ∧
          ‖(hillHminusContinuedRoot (z^2,q))⁻¹ • hillHminusNormalizedNumeratorSequence C N R (z^2,q)‖ ≤ K/(k : ℝ) := by
  obtain ⟨δ,K,hδ,hK,hd⟩ := exists_hillHminus_uniform_inner_differential_bound
  obtain ⟨W,hWV,hW,h0W,hcrit⟩ := D.toHillHminusAllContourPeriodData.exists_uniform_small_critical_control
    (Real.pi/16) (by positivity) (by linarith [Real.pi_pos])
  refine ⟨W ∩ ball 0 δ,fun _ hq => hWV hq.1,hW.inter isOpen_ball,
    ⟨h0W,mem_ball_self hδ⟩,(192/Real.pi)*K,by positivity,?_⟩
  intro q hq k z hz
  obtain ⟨ht,hbound⟩ := hd q hq.2 k z hz
  refine ⟨ht,?_⟩
  calc
    _ ≤ (192/Real.pi)*‖hillHminusDiscriminantDerivative (z^2,q)/hillHminusContinuedRoot (z^2,q)‖ :=
      D.normalized_density_bound_of_critical_control R q (hWV hq.1) (hR q (hWV hq.1))
        (fun m => (hcrit m q hq.1).le) k z hz
    _ ≤ (192/Real.pi)*(K/(k : ℝ)) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring
end HillHminusUniformPeriodData
end NLS.KdV
