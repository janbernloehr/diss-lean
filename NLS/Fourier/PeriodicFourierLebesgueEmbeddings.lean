import NLS.Fourier.CircleHausdorffYoungAnalysis
import NLS.Fourier.PeriodicL1Uniqueness
/-!
# Appendix A.2 and A.4: the original Fourier–Lebesgue embeddings

For conjugate p and q with 1 ≤ p ≤ 2, `ofLp` embeds the actual physical Lᵖ
quotient into FLᑫ, and `lpRepresentative` embeds original FLᵖ distributions
into physical Lᑫ. Both complex continuous linear maps have norm at most one.
Their actions retain the exact 1/L interval normalization. The representative
is unique modulo almost-everywhere equality, and both endpoints agree with
the earlier L² isometry and the continuous representative of FL¹.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.Fourier
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

namespace PeriodicFourierLebesgue

/-- Lemma A.2: physical Lᵖ embeds continuously in original FLᑫ for conjugate 1 ≤ p ≤ 2. -/
def ofLp (hp₂ : p ≤ 2) :
    Lp ℂ p (AddCircle.haarAddCircle (T := L)) →L[ℂ] PeriodicFourierLebesgue L Weight.one q :=
  (unweightedCoefficients q).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (circleAnalysisCLM hp₂)

theorem ofLp_coefficient (hp₂ : p ≤ 2) (f : Lp ℂ p (AddCircle.haarAddCircle (T := L))) (n : ℤ) :
    (ofLp (q := q) hp₂ f).val (mode (-n)) = fourierCoeff f n := by
  rw [← unweightedCoefficients_apply]
  change unweightedCoefficients q ((unweightedCoefficients q).symm (circleAnalysisCLM hp₂ f)) n = _
  rw [LinearIsometryEquiv.apply_symm_apply,circleAnalysisCLM_apply]

/-- The coefficient-defined image is exactly integration against the original function. -/
theorem ofLp_represents (hp₂ : p ≤ 2) (f : Lp ℂ p (AddCircle.haarAddCircle (T := L))) :
    (ofLp (q := q) hp₂ f).val = Distribution.ofCircleL1 f ((Lp.memLp f).integrable (Fact.out : 1 ≤ p)) := by
  apply Distribution.ext_coefficients
  intro n
  rw [ofLp_coefficient,Distribution.ofCircleL1_coefficient]

theorem ofLp_apply (hp₂ : p ≤ 2) (f : Lp ℂ p (AddCircle.haarAddCircle (T := L))) (t : SmoothPeriodicTest L) :
    (ofLp (q := q) hp₂ f).val t = ∫ x, f x * toContinuousCLM t x ∂AddCircle.haarAddCircle := by
  rw [ofLp_represents,Distribution.ofCircleL1_apply]

theorem ofLp_apply_interval (hp₂ : p ≤ 2) (f : Lp ℂ p (AddCircle.haarAddCircle (T := L))) (t : SmoothPeriodicTest L) :
    (ofLp (q := q) hp₂ f).val t = (L:ℂ)⁻¹ * ∫ x in (0:ℝ)..L, f (x : AddCircle L)*t x := by
  rw [ofLp_represents,Distribution.ofCircleL1_apply_interval]

theorem norm_ofLp_le (hp₂ : p ≤ 2) (f : Lp ℂ p (AddCircle.haarAddCircle (T := L))) :
    ‖ofLp (q := q) hp₂ f‖ ≤ ‖f‖ := by
  change ‖(unweightedCoefficients q).symm (circleAnalysis (q := q) hp₂ f)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact norm_circleAnalysis_le hp₂ f

theorem norm_ofLp (hp₂ : p ≤ 2) : ‖ofLp (L := L) (q := q) hp₂‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_ofLp_le (q := q) hp₂ f

theorem ofLp_injective (hp₂ : p ≤ 2) : Function.Injective (ofLp (L := L) (q := q) hp₂) := by
  intro f g h
  apply Distribution.ofCircleLp_injective
  have he := congrArg Subtype.val h
  simpa only [ofLp_represents] using he

/-- Lemma A.4: original FLᵖ embeds in physical Lᑫ for conjugate 1 ≤ p ≤ 2. -/
def lpRepresentative : PeriodicFourierLebesgue L Weight.one p →L[ℂ]
    Lp ℂ q (AddCircle.haarAddCircle (T := L)) :=
  circleSynthesis.comp (unweightedCoefficients p).toContinuousLinearEquiv.toContinuousLinearMap

theorem lpRepresentative_coefficient (hp₂ : p ≤ 2)
    (u : PeriodicFourierLebesgue L Weight.one p) (n : ℤ) :
    fourierCoeff (lpRepresentative (q := q) u) n = u.val (mode (-n)) := by
  change fourierCoeff (circleSynthesis (q := q) (unweightedCoefficients p u)) n = _
  rw [circleSynthesis_coefficient hp₂,unweightedCoefficients_apply]

theorem lpRepresentative_represents (hp₂ : p ≤ 2) (u : PeriodicFourierLebesgue L Weight.one p) :
    Distribution.ofCircleL1 (lpRepresentative (q := q) u)
      ((Lp.memLp _).integrable (Fact.out : 1 ≤ q)) = u.val := circleSynthesis_represents hp₂ u

theorem lpRepresentative_apply (hp₂ : p ≤ 2) (u : PeriodicFourierLebesgue L Weight.one p) (t : SmoothPeriodicTest L) :
    u.val t = ∫ x, lpRepresentative (q := q) u x * toContinuousCLM t x ∂AddCircle.haarAddCircle := by
  rw [← lpRepresentative_represents (q := q) hp₂ u,Distribution.ofCircleL1_apply]

theorem lpRepresentative_apply_interval (hp₂ : p ≤ 2) (u : PeriodicFourierLebesgue L Weight.one p) (t : SmoothPeriodicTest L) :
    u.val t = (L:ℂ)⁻¹ * ∫ x in (0:ℝ)..L, lpRepresentative (q := q) u (x : AddCircle L)*t x := by
  rw [← lpRepresentative_represents (q := q) hp₂ u,Distribution.ofCircleL1_apply_interval]

theorem norm_lpRepresentative_le (hp₂ : p ≤ 2) (u : PeriodicFourierLebesgue L Weight.one p) :
    ‖lpRepresentative (q := q) u‖ ≤ ‖u‖ := by
  change ‖circleSynthesis (q := q) (unweightedCoefficients p u)‖ ≤ _
  simpa only [one_mul,LinearIsometryEquiv.norm_map] using
    (circleSynthesis (L := L) (p := p) (q := q)).le_of_opNorm_le (norm_circleSynthesis_le hp₂) (unweightedCoefficients p u)

theorem norm_lpRepresentative (hp₂ : p ≤ 2) :
    ‖lpRepresentative (L := L) (p := p) (q := q)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using norm_lpRepresentative_le (q := q) hp₂ u

theorem lpRepresentative_injective (hp₂ : p ≤ 2) :
    Function.Injective (lpRepresentative (L := L) (p := p) (q := q)) := by
  intro u v h
  apply Subtype.ext
  rw [← lpRepresentative_represents (q := q) hp₂ u,← lpRepresentative_represents (q := q) hp₂ v,h]

/-- Every FLᵖ distribution in the Hausdorff–Young range has one Lᑫ equivalence class representing it. -/
theorem existsUnique_lpRepresentative (hp₂ : p ≤ 2) (u : PeriodicFourierLebesgue L Weight.one p) :
    ∃! f : Lp ℂ q (AddCircle.haarAddCircle (T := L)),
      Distribution.ofCircleL1 f ((Lp.memLp f).integrable (Fact.out : 1 ≤ q)) = u.val :=
  ⟨lpRepresentative u,lpRepresentative_represents hp₂ u,fun _f hf =>
    Distribution.ofCircleLp_injective (hf.trans (lpRepresentative_represents hp₂ u).symm)⟩

/-- The Hilbert endpoint agrees with the previously constructed Parseval isometry. -/
theorem lpRepresentative_two (u : PeriodicFourierLebesgue L Weight.one 2) :
    lpRepresentative (q := 2) u = l2Isometry u := by
  apply Distribution.ofCircleLp_injective
  dsimp only
  rw [lpRepresentative_represents (by norm_num),l2Isometry_represents]

/-- The infinity endpoint is the L∞ class of the uniformly convergent Fourier series. -/
theorem lpRepresentative_one (u : PeriodicFourierLebesgue L Weight.one 1) :
    lpRepresentative (q := ⊤) u = ContinuousMap.toLp ⊤ AddCircle.haarAddCircle ℂ (continuousRepresentative u) := by
  apply circleLp_fourierCoeff_injective
  funext n
  dsimp only
  rw [lpRepresentative_coefficient (by norm_num),
    fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp _ _),continuousRepresentative_coefficient]

theorem ofLp_two (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := L))) :
    ofLp (q := 2) (by norm_num) f = l2Isometry.symm f := by
  apply Subtype.ext
  rw [ofLp_represents,← l2Isometry_represents,LinearIsometryEquiv.apply_symm_apply]

end PeriodicFourierLebesgue
end NLS.Fourier
