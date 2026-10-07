import NLS.SequenceSpaces.PhaseRotation
import NLS.SequenceSpaces.Multiplier
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Constructions

/-! # Analytic phase trajectories on compact parameter spaces

A fixed, possibly unbounded, real frequency sequence is separated from a
bounded complex correction. The correction exponential is taken in the
Banach algebra of continuous bounded-symbol families. Multiplication and
the free phase rotation then give an entire map into the trajectory space.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Bounded symbols act complex bilinearly on coefficient sequences. -/
def multiplierBilinear : Coeff ⊤ →L[ℂ] Coeff p →L[ℂ] Coeff p :=
  (LinearMap.mk₂ ℂ (multiplier (p := p))
    (by intro m k a; ext n; simp [add_mul])
    (by intro c m a; ext n; simp [mul_assoc])
    multiplier_add (fun c m a => multiplier_smul m c a)).mkContinuous₂ 1
      (fun m a => by simpa only [one_mul, LinearMap.mk₂_apply] using norm_multiplier_le m a)

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- A continuous family of bounded symbols acts on a fixed sequence. -/
def trajectoryMultiplier (m : C(K, Coeff ⊤)) (a : Coeff p) : C(K, Coeff p) where
  toFun k := multiplier (m k) a
  continuous_toFun := ((multiplierBilinear (p := p)).continuous.comp m.continuous).clm_apply continuous_const

/-- Multiplication remains bounded bilinear in the uniform trajectory norm. -/
def trajectoryMultiplierBilinear : C(K, Coeff ⊤) →L[ℂ] Coeff p →L[ℂ] C(K, Coeff p) :=
  (LinearMap.mk₂ ℂ (trajectoryMultiplier (p := p) (K := K))
    (by intro m k a; ext t n; change (m t n+k t n)*a n = m t n*a n+k t n*a n; ring)
    (by intro c m a; ext t n; change (c*m t n)*a n = c*(m t n*a n); ring)
    (by intro m a b; ext t n; change m t n*(a n+b n) = m t n*a n+m t n*b n; ring)
    (by intro c m a; ext t n; change m t n*(c*a n) = c*(m t n*a n); ring)).mkContinuous₂ 1
      (fun m a => by
        apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ 1*‖m‖*‖a‖)).mpr
        intro k
        exact (norm_multiplier_le (m k) a).trans
          (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
            (m.norm_coe_le_norm k) (norm_nonneg a))))

/-- Multiplication by imaginary time, uniformly on a compact parameter space. -/
def imaginaryTimeCLM (θ : C(K, ℝ)) : Coeff ⊤ →L[ℂ] C(K, Coeff ⊤) :=
  LinearMap.mkContinuous
    { toFun := fun b => ⟨fun k => ((θ k : ℂ)*I) • b,
        ((Complex.continuous_ofReal.comp θ.continuous).mul continuous_const).smul continuous_const⟩
      map_add' := by intro a b; ext k; simp [smul_add]
      map_smul' := by
        intro c b
        apply ContinuousMap.ext
        intro k
        change ((θ k : ℂ)*I) • (c • b) = c • (((θ k : ℂ)*I) • b)
        exact smul_comm _ _ _ }
    ‖θ‖ (by
      intro b
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      intro k
      change ‖((θ k : ℂ)*I) • b‖ ≤ ‖θ‖*‖b‖
      simp only [norm_smul, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (θ.norm_coe_le_norm k) (norm_nonneg b))

/-- The free rotation acts bounded linearly on continuous trajectories. -/
def freeTrajectoryCLM (hp : p ≠ ⊤) (ω : ℤ → ℝ) (θ : C(K, ℝ)) :
    C(K, Coeff p) →L[ℂ] C(K, Coeff p) :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨fun k => phaseFlow ω (θ k) (a k),
        (continuous_phaseFlow hp ω).comp (θ.continuous.prodMk a.continuous)⟩
      map_add' := by
        intro a b
        apply ContinuousMap.ext
        intro k
        exact (phaseFlow (p := p) ω (θ k)).map_add (a k) (b k)
      map_smul' := by
        intro c a
        apply ContinuousMap.ext
        intro k
        exact (phaseFlow (p := p) ω (θ k)).map_smul c (a k) }
    1 (by
      intro a
      apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ 1*‖a‖)).mpr
      intro k
      change ‖phaseFlow ω (θ k) (a k)‖ ≤ _
      simpa only [(phaseFlow ω (θ k)).norm_map, one_mul] using a.norm_coe_le_norm k)

/-- Trajectories for the full frequency ω+b, allowing complex bounded b. -/
def analyticPhaseTrajectory (hp : p ≠ ⊤) (ω : ℤ → ℝ) (θ : C(K, ℝ))
    (b : Coeff ⊤) (a : Coeff p) : C(K, Coeff p) :=
  freeTrajectoryCLM hp ω θ
    (trajectoryMultiplierBilinear (NormedSpace.exp (imaginaryTimeCLM θ b)) a)

/-- The bounded correction and amplitude enter analytically in the uniform trajectory norm. -/
theorem analyticAt_analyticPhaseTrajectory (hp : p ≠ ⊤) (ω : ℤ → ℝ) (θ : C(K, ℝ))
    (x : Coeff ⊤ × Coeff p) :
    AnalyticAt ℂ (fun y : Coeff ⊤ × Coeff p => analyticPhaseTrajectory hp ω θ y.1 y.2) x := by
  apply ((freeTrajectoryCLM hp ω θ).analyticAt _).comp
  apply ((trajectoryMultiplierBilinear (p := p) (K := K)).analyticAt_bilinear _).comp
    (f := fun y : Coeff ⊤ × Coeff p => (NormedSpace.exp (imaginaryTimeCLM θ y.1),y.2))
  exact ((NormedSpace.exp_analytic _).comp
    (((imaginaryTimeCLM θ).analyticAt _).comp analyticAt_fst)).prod analyticAt_snd

/-- Coordinate evaluation commutes with the exponential of a bounded symbol. -/
theorem infty_exp_apply (b : Coeff ⊤) (n : ℤ) :
    NormedSpace.exp b n = Complex.exp (b n) := by
  let ev : Coeff ⊤ →+* ℂ := (Pi.evalRingHom (fun _ : ℤ => ℂ) n).comp
    (lpInftySubring (fun _ : ℤ => ℂ)).subtype
  have he := NormedSpace.map_exp ev (lp.evalCLM ℂ (fun _ : ℤ => ℂ) ⊤ n).continuous b
  simpa only [ev, RingHom.comp_apply, Pi.evalRingHom_apply, Subring.coe_subtype,
    Complex.exp_eq_exp_ℂ] using! he

/-- The entire trajectory map has precisely the expected scalar phase formula. -/
theorem analyticPhaseTrajectory_apply (hp : p ≠ ⊤) (ω : ℤ → ℝ) (θ : C(K, ℝ))
    (b : Coeff ⊤) (a : Coeff p) (k : K) (n : ℤ) :
    analyticPhaseTrajectory hp ω θ b a k n =
      Complex.exp ((θ k : ℂ)*I*((ω n : ℂ)+b n))*a n := by
  have he := NormedSpace.map_exp (ContinuousMap.evalAlgHom (S := ℂ) (R := Coeff ⊤) k)
    (ContinuousMap.evalCLM ℂ k).continuous (imaginaryTimeCLM θ b)
  change (NormedSpace.exp (imaginaryTimeCLM θ b)) k =
    NormedSpace.exp ((imaginaryTimeCLM θ b) k) at he
  change Complex.exp (((θ k*ω n : ℝ) : ℂ)*I)*
    ((NormedSpace.exp (imaginaryTimeCLM θ b)) k n*a n) = _
  erw [he,infty_exp_apply]
  change Complex.exp (((θ k*ω n : ℝ) : ℂ)*I)*
    (Complex.exp (((θ k : ℂ)*I)*b n)*a n) = _
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end NLS.Coeff
