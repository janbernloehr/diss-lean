import NLS.Fourier.LowerDyadicTent
import NLS.ZakharovShabat.OrderedTriangularNormalization

/-! # An ordered dyadic source with an actual prescribed periodic spectral point -/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The signed upper sum precedes the unit-area lower tent. -/
def orderedDyadicCurve (J : ℕ) : Curve (ℂ × ℂ) where
  toFun t := (dyadicTentSum J t, lowerDyadicTent J t)
  continuous_toFun := by fun_prop

/-- Both components use the original unit-period Fourier coefficients. -/
def orderedDyadicSource (J : ℕ) (hJ : 2 ≤ J) : CoeffPair 2 :=
  WithLp.toLp 2 (dyadicTentSumCoefficients J, lowerDyadicTentCoefficients J hJ)

theorem physicalBase_orderedDyadicSource (J : ℕ) (hJ : 2 ≤ J) :
    physicalBase (periodOnePotential (orderedDyadicSource J hJ)) =ᵐ[volume.restrict (Ioc 0 1)]
      extend (orderedDyadicCurve J) := by
  have hu := circlePullback_dyadicTentSumCoefficients J
  have hv := circlePullback_lowerDyadicTentCoefficients J hJ
  filter_upwards [hu,hv,ae_restrict_mem measurableSet_Ioc] with x hx hy hmem
  rw [show extend (orderedDyadicCurve J) x = orderedDyadicCurve J ⟨x,hmem.1.le,hmem.2⟩ from
    extend_coe _ ⟨x,hmem.1.le,hmem.2⟩]
  exact Prod.ext hx hy

theorem orderedDyadicCurve_support (J : ℕ) :
    HasOrderedTriangularSupport (orderedDyadicCurve J) (1-dyadicTentWidth J) := by
  intro t
  constructor
  · intro ht
    change (lowerDyadicTent J t.val : ℂ) = 0
    rw [lowerDyadicTent_eq_zero_before J ht, ofReal_zero]
  · intro ht
    change (dyadicTentSum J t.val : ℂ) = 0
    rw [dyadicTentSum_eq_zero_near_ends J (Or.inr ht), ofReal_zero]

/-- The real upper interaction at imaginary height H. -/
def dyadicUpperInteraction (J : ℕ) (H : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, dyadicTentSum J x*Real.exp (-2*H*x)

/-- The real lower interaction at imaginary height H. -/
def dyadicLowerInteraction (J : ℕ) (H : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, lowerDyadicTent J x*Real.exp (2*H*x)

theorem orderedDyadicCurve_interactions (J : ℕ) (H : ℝ) :
    upperInteractionPrimitive (orderedDyadicCurve J) (I*H) 1 = I*(dyadicUpperInteraction J H : ℂ) ∧
    lowerInteractionPrimitive (orderedDyadicCurve J) (I*H) 1 = -I*(dyadicLowerInteraction J H : ℂ) := by
  constructor
  · unfold upperInteractionPrimitive dyadicUpperInteraction
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    dsimp only
    rw [show extend (orderedDyadicCurve J) x = orderedDyadicCurve J ⟨x,hx⟩ from extend_coe _ ⟨x,hx⟩]
    change I*(dyadicTentSum J x : ℂ)*exp (2*I*(I*H)*x) = _
    rw [show 2*I*(I*H)*(x : ℂ) = ((-2*H*x : ℝ) : ℂ) by push_cast; ring_nf; simp [I_sq],
      ← Complex.ofReal_exp]
    push_cast
    ring
  · unfold lowerInteractionPrimitive dyadicLowerInteraction
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    dsimp only
    rw [show extend (orderedDyadicCurve J) x = orderedDyadicCurve J ⟨x,hx⟩ from extend_coe _ ⟨x,hx⟩]
    change -I*(lowerDyadicTent J x : ℂ)*exp (-2*I*(I*H)*x) = _
    rw [show -2*I*(I*H)*(x : ℂ) = ((2*H*x : ℝ) : ℂ) by push_cast; ring_nf; simp [I_sq],
      ← Complex.ofReal_exp]
    push_cast
    ring

theorem dyadicUpperInteraction_pow_pos (P : ℕ) (hP : 3 ≤ P) :
    0 < dyadicUpperInteraction (2*P) (2^P) := by
  have h := integral_dyadicTentSum_pow_height P hP
  have hpos : (0 : ℝ) < (P-2 : ℕ) := by exact_mod_cast (show 0 < P-2 by omega)
  exact (div_pos hpos (by norm_num)).trans_le h

theorem dyadicLowerInteraction_pos (J : ℕ) (hJ : 2 ≤ J) (H : ℝ) (hH : 0 ≤ H) :
    0 < dyadicLowerInteraction J H :=
  (Real.exp_pos _).trans_le (integral_lowerDyadicTent_exp_lower J hJ H hH)

theorem orderedDyadicCurve_interaction_ne_zero (P : ℕ) (hP : 3 ≤ P) :
    upperInteractionPrimitive (orderedDyadicCurve (2*P)) (I*(2^P : ℝ)) 1*
      lowerInteractionPrimitive (orderedDyadicCurve (2*P)) (I*(2^P : ℝ)) 1 ≠ 0 := by
  obtain ⟨hu,hv⟩ := orderedDyadicCurve_interactions (2*P) (2^P)
  rw [hu,hv]
  exact mul_ne_zero
    (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr (dyadicUpperInteraction_pow_pos P hP).ne'))
    (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (ofReal_ne_zero.mpr
      (dyadicLowerInteraction_pos (2*P) (by omega) (2^P) (by positivity)).ne'))

/-- Normalization puts the prescribed point in the actual periodic spectrum. -/
theorem normalized_orderedDyadicSource_mem_periodicSpectrum
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h2p : (2 : ℝ≥0∞) ≤ p)
    (P : ℕ) (hP : 3 ≤ P) :
    I*(2^P : ℝ) ∈ periodicSpectrum hp (periodOnePotential (CoeffPair.exponentInclusion h2p
      (scaleUpperSource (orderedPeriodicNormalization (orderedDyadicCurve (2*P)) (I*(2^P : ℝ)))
        (orderedDyadicSource (2*P) (by omega))))) :=
  source_mem_periodicSpectrum_orderedPeriodicNormalization hp h2p _ _
    (physicalBase_orderedDyadicSource (2*P) (by omega)) (orderedDyadicCurve_support (2*P)) _
    (orderedDyadicCurve_interaction_ne_zero P hP)

/-- The upper coefficients cannot vanish, since their reconstructed weighted integral is positive. -/
theorem dyadicTentSumCoefficients_twice_ne_zero (P : ℕ) (hP : 3 ≤ P) :
    dyadicTentSumCoefficients (2*P) ≠ 0 := by
  intro hz
  have hu := circlePullback_dyadicTentSumCoefficients (2*P)
  rw [hz,map_zero,map_zero] at hu
  have hzero := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
    (circle_ae_pullback (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := AddCircle.haarAddCircle)))
  have he : dyadicUpperInteraction (2*P) (2^P) = 0 := by
    unfold dyadicUpperInteraction
    calc
      _ = ∫ x in (0 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        filter_upwards [hu,hzero] with x hx hx0
        have hxreal : dyadicTentSum (2*P) x = 0 := by
          apply Complex.ofReal_injective
          exact hx.symm.trans hx0
        rw [hxreal,zero_mul]
      _ = 0 := by simp
  exact (dyadicUpperInteraction_pow_pos P hP).ne' he

/-- The balanced potential keeps the prescribed point and its exact original coefficient norm. -/
theorem exists_balanced_orderedDyadicSource
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h2p : (2 : ℝ≥0∞) ≤ p)
    (P : ℕ) (hP : 3 ≤ P) :
    ∃ ψ : CoeffPair p, ‖ψ.fst‖ = ‖ψ.snd‖ ∧
      I*(2^P : ℝ) ∈ periodicSpectrum hp (periodOnePotential ψ) ∧
      ‖ψ‖ = (2 : ℝ)^(1/p.toReal)*Real.sqrt
        (‖orderedPeriodicNormalization (orderedDyadicCurve (2*P)) (I*(2^P : ℝ))‖ *
          ‖Coeff.exponentInclusion h2p (dyadicTentSumCoefficients (2*P))‖ *
          ‖Coeff.exponentInclusion h2p (lowerDyadicTentCoefficients (2*P) (by omega))‖) := by
  apply exists_balanced_source_orderedPeriodicNormalization hp h2p _ _
    (physicalBase_orderedDyadicSource (2*P) (by omega)) (orderedDyadicCurve_support (2*P)) _
    (by simpa only [mul_im,I_re,I_im,ofReal_re,ofReal_im,zero_mul,one_mul,zero_add]
      using (pow_pos (by norm_num : (0 : ℝ) < 2) P).ne')
    (orderedDyadicCurve_interaction_ne_zero P hP)
    (dyadicTentSumCoefficients_twice_ne_zero P hP)
  intro hz
  have h := congrArg (fun a : Coeff 2 => a 0) hz
  change lowerDyadicTentCoefficients (2*P) (by omega) 0 = 0 at h
  rw [lowerDyadicTentCoefficients_zero] at h
  exact one_ne_zero h

end NLS.ZakharovShabat
