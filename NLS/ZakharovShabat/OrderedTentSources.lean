import NLS.Fourier.TentProfile
import NLS.ZakharovShabat.OrderedTriangularNormalization

/-! # Concrete ordered tent sources with prescribed imaginary spectral points

Both couplings are continuous compactly supported tents. Their original
unit-period Fourier coefficients reconstruct the physical potential.
Strict positivity of the two real exponential integrals discharges the
normalization's nonzero-interaction assumption for every imaginary point.
-/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Upper tent near the beginning of a period. -/
def upperTent (ε x : ℝ) : ℂ := tentProfile 0 ε x

/-- Lower tent near the end of a period. -/
def lowerTent (ε x : ℝ) : ℂ := tentProfile (1-ε) 1 x

@[fun_prop] theorem continuous_upperTent (ε : ℝ) : Continuous (upperTent ε) := by
  unfold upperTent
  fun_prop

@[fun_prop] theorem continuous_lowerTent (ε : ℝ) : Continuous (lowerTent ε) := by
  unfold lowerTent
  fun_prop

theorem upperTent_endpoints (ε : ℝ) (hε : ε ≤ 1) : upperTent ε 0 = upperTent ε 1 := by
  simp [upperTent, tentProfile_eq_zero_left 0 ε (le_refl 0), tentProfile_eq_zero_right 0 ε hε]

theorem lowerTent_endpoints (ε : ℝ) (hε : ε ≤ 1) : lowerTent ε 0 = lowerTent ε 1 := by
  simp [lowerTent, tentProfile_eq_zero_left (1-ε) 1 (by linarith : (0 : ℝ) ≤ 1-ε),
    tentProfile_eq_zero_right (1-ε) 1 (le_refl 1)]

/-- A genuine continuous physical pair, with the original upper/lower convention. -/
def orderedTentCurve (ε : ℝ) : Curve (ℂ × ℂ) where
  toFun t := (upperTent ε t, lowerTent ε t)
  continuous_toFun := by fun_prop

@[simp] theorem orderedTentCurve_apply (ε : ℝ) (t : Icc (0 : ℝ) 1) :
    orderedTentCurve ε t = (upperTent ε t,lowerTent ε t) := rfl

/-- Original Hilbert source coefficients of the two interval tents. -/
def orderedTentSource (ε : ℝ) (hε : ε ≤ 1) : CoeffPair 2 := WithLp.toLp 2
  (continuousPeriodOneCoefficients (upperTent ε) (continuous_upperTent ε) (upperTent_endpoints ε hε),
   continuousPeriodOneCoefficients (lowerTent ε) (continuous_lowerTent ε) (lowerTent_endpoints ε hε))

@[simp] theorem orderedTentSource_fst_apply (ε : ℝ) (hε : ε ≤ 1) (n : ℤ) :
    (orderedTentSource ε hε).fst n = periodOneCoefficient (upperTent ε) n :=
  continuousPeriodOneCoefficients_apply _ (continuous_upperTent ε) (upperTent_endpoints ε hε) n

@[simp] theorem orderedTentSource_snd_apply (ε : ℝ) (hε : ε ≤ 1) (n : ℤ) :
    (orderedTentSource ε hε).snd n = periodOneCoefficient (lowerTent ε) n :=
  continuousPeriodOneCoefficients_apply _ (continuous_lowerTent ε) (lowerTent_endpoints ε hε) n

/-- The representative assumption in the spectral criterion is now proved for this family. -/
theorem physicalBase_orderedTentSource (ε : ℝ) (hε : ε ≤ 1) :
    physicalBase (periodOnePotential (orderedTentSource ε hε)) =ᵐ[volume.restrict (Ioc 0 1)]
      extend (orderedTentCurve ε) := by
  have hu := circlePullback_continuousPeriodOneCoefficients
    (upperTent ε) (continuous_upperTent ε) (upperTent_endpoints ε hε)
  have hv := circlePullback_continuousPeriodOneCoefficients
    (lowerTent ε) (continuous_lowerTent ε) (lowerTent_endpoints ε hε)
  filter_upwards [hu,hv,ae_restrict_mem measurableSet_Ioc] with x hx hy hmem
  rw [show extend (orderedTentCurve ε) x = orderedTentCurve ε ⟨x,hmem.1.le,hmem.2⟩ from
    extend_coe _ ⟨x,hmem.1.le,hmem.2⟩]
  exact Prod.ext hx hy

/-- Width at most half a period makes the two tents ordered and disjoint. -/
theorem orderedTentCurve_support (ε : ℝ) (hε : ε ≤ 1/2) :
    HasOrderedTriangularSupport (orderedTentCurve ε) (1/2) := by
  intro t
  constructor
  · intro ht
    change (tentProfile (1-ε) 1 t.val : ℂ) = 0
    rw [tentProfile_eq_zero_left (1-ε) 1 (by linarith), ofReal_zero]
  · intro ht
    change (tentProfile 0 ε t.val : ℂ) = 0
    rw [tentProfile_eq_zero_right 0 ε (by linarith), ofReal_zero]

/-- Upper and lower interactions at an imaginary parameter are real positive integrals times ±i. -/
theorem orderedTentCurve_interactions (ε H : ℝ) :
    upperInteractionPrimitive (orderedTentCurve ε) (I*H) 1 =
      I*((∫ x in (0 : ℝ)..1, tentProfile 0 ε x*Real.exp (-2*H*x) : ℝ) : ℂ) ∧
    lowerInteractionPrimitive (orderedTentCurve ε) (I*H) 1 =
      -I*((∫ x in (0 : ℝ)..1, tentProfile (1-ε) 1 x*Real.exp (2*H*x) : ℝ) : ℂ) := by
  constructor
  · unfold upperInteractionPrimitive
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    dsimp only
    rw [show extend (orderedTentCurve ε) x = orderedTentCurve ε ⟨x,hx⟩ from extend_coe _ ⟨x,hx⟩]
    change I*(tentProfile 0 ε x : ℂ)*exp (2*I*(I*H)*x) = _
    rw [show 2*I*(I*H)*(x : ℂ) = ((-2*H*x : ℝ) : ℂ) by push_cast; ring_nf; simp [I_sq],
      ← Complex.ofReal_exp]
    push_cast
    ring
  · unfold lowerInteractionPrimitive
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    dsimp only
    rw [show extend (orderedTentCurve ε) x = orderedTentCurve ε ⟨x,hx⟩ from extend_coe _ ⟨x,hx⟩]
    change -I*(tentProfile (1-ε) 1 x : ℂ)*exp (-2*I*(I*H)*x) = _
    rw [show -2*I*(I*H)*(x : ℂ) = ((2*H*x : ℝ) : ℂ) by push_cast; ring_nf; simp [I_sq],
      ← Complex.ofReal_exp]
    push_cast
    ring

/-- No exceptional imaginary parameter makes the interaction product vanish. -/
theorem orderedTentCurve_interaction_ne_zero (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (H : ℝ) :
    upperInteractionPrimitive (orderedTentCurve ε) (I*H) 1*
      lowerInteractionPrimitive (orderedTentCurve ε) (I*H) 1 ≠ 0 := by
  obtain ⟨hu,hv⟩ := orderedTentCurve_interactions ε H
  rw [hu,hv]
  exact mul_ne_zero
    (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr
      (integral_tentProfile_mul_exp_pos 0 ε (le_refl 0) hε0 hε1 (-2*H)).ne'))
    (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (ofReal_ne_zero.mpr
      (integral_tentProfile_mul_exp_pos (1-ε) 1 (by linarith) (by linarith) (le_refl 1) (2*H)).ne'))

/-- This explicit coefficient family has the prescribed actual spectral point at every finite p>=2. -/
theorem normalized_orderedTentSource_mem_periodicSpectrum
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h2p : (2 : ℝ≥0∞) ≤ p)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1/2) (H : ℝ) :
    I*H ∈ periodicSpectrum hp (periodOnePotential (CoeffPair.exponentInclusion h2p
      (scaleUpperSource (orderedPeriodicNormalization (orderedTentCurve ε) (I*H))
        (orderedTentSource ε (by linarith))))) :=
  source_mem_periodicSpectrum_orderedPeriodicNormalization hp h2p _ _
    (physicalBase_orderedTentSource ε (by linarith)) (orderedTentCurve_support ε hε) _
    (orderedTentCurve_interaction_ne_zero ε hε0 (by linarith) H)

/-- Both source components are nonzero: their means are the positive triangle area. -/
theorem orderedTentSource_components_ne_zero (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (orderedTentSource ε hε1).fst ≠ 0 ∧ (orderedTentSource ε hε1).snd ≠ 0 := by
  have hp : (ε^2/4 : ℝ) ≠ 0 := (div_pos (sq_pos_of_pos hε0) (by norm_num)).ne'
  constructor
  · intro h
    have hz := congrArg (fun a : Coeff 2 => a 0) h
    rw [orderedTentSource_fst_apply] at hz
    change periodOneCoefficient (fun x => (tentProfile 0 ε x : ℂ)) 0 = 0 at hz
    rw [periodOneCoefficient_tentProfile_zero 0 ε (le_refl 0) hε0.le hε1] at hz
    exact hp (by simpa using Complex.ofReal_injective hz)
  · intro h
    have hz := congrArg (fun a : Coeff 2 => a 0) h
    rw [orderedTentSource_snd_apply] at hz
    change periodOneCoefficient (fun x => (tentProfile (1-ε) 1 x : ℂ)) 0 = 0 at hz
    rw [periodOneCoefficient_tentProfile_zero (1-ε) 1 (by linarith) (by linarith) (le_refl 1)] at hz
    exact hp (by simpa using Complex.ofReal_injective hz)

/-- A concrete balanced source at each nonzero imaginary point, with no representative or
nonzero-interaction assumptions left to discharge. The exact norm cost remains visible. -/
theorem exists_balanced_orderedTentSource
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h2p : (2 : ℝ≥0∞) ≤ p)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1/2) (H : ℝ) (hH : H ≠ 0) :
    ∃ ψ : CoeffPair p, ‖ψ.fst‖ = ‖ψ.snd‖ ∧
      I*H ∈ periodicSpectrum hp (periodOnePotential ψ) ∧
      ‖ψ‖ = (2 : ℝ)^(1/p.toReal)*Real.sqrt
        (‖orderedPeriodicNormalization (orderedTentCurve ε) (I*H)‖ *
          ‖(CoeffPair.exponentInclusion h2p (orderedTentSource ε (by linarith))).fst‖ *
          ‖(CoeffPair.exponentInclusion h2p (orderedTentSource ε (by linarith))).snd‖) := by
  obtain ⟨hu,hv⟩ := orderedTentSource_components_ne_zero ε hε0 (by linarith)
  apply exists_balanced_source_orderedPeriodicNormalization hp h2p _ _
    (physicalBase_orderedTentSource ε (by linarith)) (orderedTentCurve_support ε hε) _
    (by simpa using hH) (orderedTentCurve_interaction_ne_zero ε hε0 (by linarith) H) hu hv

end NLS.ZakharovShabat
