import NLS.Fourier.CircleHausdorffYoungSynthesis
import NLS.SequenceSpaces.FullDuality
import NLS.SequenceSpaces.Reflection
import Mathlib.MeasureTheory.Function.Holder
/-!
# Hausdorff–Young analysis on the physical circle

Hölder pairing with the continuous synthesis map yields a bounded functional
on ℓᵖ. Full sequence duality, followed by index reflection, recovers the actual
Fourier coefficients in ℓᑫ. This includes L¹ → ℓ∞ and uses normalized Haar measure.
-/

noncomputable section
open Complex Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate
namespace NLS.Fourier
variable {L : ℝ} [Fact (0 < L)]
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Complex bilinear integration pairing at conjugate exponents. -/
def circleLpPairing : Lp ℂ p (AddCircle.haarAddCircle (T := L)) →L[ℂ]
    Lp ℂ q (AddCircle.haarAddCircle (T := L)) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle p q

theorem circleLpPairing_apply (f : Lp ℂ p (AddCircle.haarAddCircle (T := L)))
    (g : Lp ℂ q (AddCircle.haarAddCircle (T := L))) :
    circleLpPairing f g = ∫ x, f x*g x ∂AddCircle.haarAddCircle :=
  ContinuousLinearMap.lpPairing_eq_integral _ _ _

theorem norm_circleLpPairing_apply_le (f : Lp ℂ p (AddCircle.haarAddCircle (T := L)))
    (g : Lp ℂ q (AddCircle.haarAddCircle (T := L))) :
    ‖circleLpPairing f g‖ ≤ ‖f‖*‖g‖ := by
  have hm : ‖ContinuousLinearMap.mul ℂ ℂ‖ ≤ (1:ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa only [one_mul] using ContinuousLinearMap.opNorm_mul_apply_le ℂ ℂ z
  change ‖L1.integralCLM' ℂ ((ContinuousLinearMap.mul ℂ ℂ).holder 1 f g)‖ ≤ _
  rw [← L1.integral_eq']
  exact (L1.norm_integral_le _).trans
    (((ContinuousLinearMap.mul ℂ ℂ).norm_holder_apply_apply_le f g).trans (by
      calc
        _ ≤ 1 * ‖f‖ * ‖g‖ := by gcongr
        _ = _ := by simp))

theorem circleSynthesis_single (hp₂ : p ≤ 2) (n : ℤ) :
    circleSynthesis (L := L) (p := p) (q := q) (lp.single p n 1) =
      ContinuousMap.toLp q AddCircle.haarAddCircle ℂ (fourier n) := by
  have he : lp.single p n (1:ℂ) = Coeff.ofFinsupp (p := p) (Finsupp.single n 1) := by
    ext k
    simp [lp.single_apply,Coeff.ofFinsupp_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [he,circleSynthesis_finite hp₂]
  change (ContinuousMap.toLp q AddCircle.haarAddCircle ℂ)
    ((Finsupp.linearCombination ℂ fourier) (Finsupp.single n 1)) = _
  simp

/-- Recover Fourier coefficients by full ℓᵖ duality and index reflection. -/
def circleAnalysis (hp₂ : p ≤ 2) (f : Lp ℂ p (AddCircle.haarAddCircle (T := L))) : Coeff q :=
  Coeff.reflection (Coeff.fullCotangent (q := q) (ne_top_of_le_ne_top (by norm_num) hp₂)
    ((circleLpPairing f).comp (circleSynthesis (p := p) (q := q))))

theorem circleAnalysis_apply (hp₂ : p ≤ 2) (f : Lp ℂ p (AddCircle.haarAddCircle (T := L))) (n : ℤ) :
    circleAnalysis (q := q) hp₂ f n = fourierCoeff f n := by
  rw [circleAnalysis,Coeff.reflection_apply,Coeff.fullCotangent_apply,ContinuousLinearMap.comp_apply,
    circleSynthesis_single hp₂,circleLpPairing_apply]
  rw [fourierCoeff]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := q) (𝕜 := ℂ) AddCircle.haarAddCircle (fourier (-n) : C(AddCircle L,ℂ))] with x hx
  rw [hx]
  exact mul_comm _ _

theorem norm_circleAnalysis_le (hp₂ : p ≤ 2) (f : Lp ℂ p (AddCircle.haarAddCircle (T := L))) :
    ‖circleAnalysis (q := q) hp₂ f‖ ≤ ‖f‖ := by
  rw [circleAnalysis,LinearIsometryEquiv.norm_map,Coeff.norm_fullCotangent]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro a
  exact (norm_circleLpPairing_apply_le f (circleSynthesis a)).trans
    (mul_le_mul_of_nonneg_left (by
      simpa only [one_mul] using (circleSynthesis (L := L) (p := p) (q := q)).le_of_opNorm_le (norm_circleSynthesis_le hp₂) a) (norm_nonneg f))

/-- Hausdorff–Young analysis as a complex continuous linear map, endpoints included. -/
def circleAnalysisCLM (hp₂ : p ≤ 2) :
    Lp ℂ p (AddCircle.haarAddCircle (T := L)) →L[ℂ] Coeff q :=
  LinearMap.mkContinuous {
    toFun := circleAnalysis (q := q) hp₂
    map_add' := fun f g => by
      ext n
      simp only [circleAnalysis_apply,lp.coeFn_add,Pi.add_apply]
      rw [fourierCoeff_congr_ae (Lp.coeFn_add f g),fourierCoeff.add
        ((Lp.memLp f).integrable (Fact.out : 1 ≤ p))
        ((Lp.memLp g).integrable (Fact.out : 1 ≤ p))]
      rfl
    map_smul' := fun c f => by
      ext n
      simp only [circleAnalysis_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
      rw [fourierCoeff_congr_ae (Lp.coeFn_smul c f),fourierCoeff.const_smul]
      rfl }
    1 (fun f => by
      change ‖circleAnalysis (q := q) hp₂ f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using norm_circleAnalysis_le (q := q) hp₂ f)

theorem circleAnalysisCLM_apply (hp₂ : p ≤ 2)
    (f : Lp ℂ p (AddCircle.haarAddCircle (T := L))) (n : ℤ) :
    circleAnalysisCLM (q := q) hp₂ f n = fourierCoeff f n := circleAnalysis_apply hp₂ f n

theorem norm_circleAnalysisCLM_le (hp₂ : p ≤ 2) :
    ‖circleAnalysisCLM (L := L) (q := q) hp₂‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖circleAnalysis (q := q) hp₂ f‖ ≤ 1 * ‖f‖
  simpa only [one_mul] using norm_circleAnalysis_le (L := L) (q := q) hp₂ f

end NLS.Fourier
