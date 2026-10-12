import NLS.Fourier.IntervalCoefficientScaling
import NLS.Fourier.IntervalBilinearParseval

/-! # Bilinear Parseval with the source's arbitrary-period normalization

Scalar unconjugated pairing reverses one Fourier frequency. These identities
retain the factor 1/L for every positive period, with L² interval hypotheses.
-/
noncomputable section
open Complex MeasureTheory Set
open scoped ComplexConjugate
namespace NLS.Fourier

/-- Physical conjugation reverses the Fourier index on every interval. -/
theorem intervalFourierCoefficient_conj {L : ℝ} (f : ℝ → ℂ) (n : ℤ) :
    intervalFourierCoefficient L (fun x => conj (f x)) n =
      conj (intervalFourierCoefficient L f (-n)) := by
  rw [intervalFourierCoefficient,intervalFourierCoefficient,map_mul]
  simp only [Complex.conj_ofReal]
  congr 1
  rw [← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [map_mul,← wave_neg,neg_neg]

/-- Corrected Section 2 bilinear pairing on any positive period. -/
theorem hasSum_bilinear_intervalFourierCoefficient {L : ℝ} (hL : 0 < L) {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hg : MemLp g 2 (volume.restrict (Ioc 0 L))) :
    HasSum (fun n : ℤ => intervalFourierCoefficient L f (-n)*intervalFourierCoefficient L g n)
      ((L : ℂ)⁻¹ * ∫ x in (0 : ℝ)..L, f x*g x) := by
  let : Fact (0 < L) := ⟨hL⟩
  have hfc : MemLp (AddCircle.liftIoc L 0 (fun x => conj (f x))) 2
      (AddCircle.haarAddCircle (T := L)) := by
    have hi : MemLp (fun x => conj (f x)) 2 (volume.restrict (Ioc (0 : ℝ) (0+L))) := by
      simpa only [zero_add,Pi.star_apply,Complex.star_def] using! hf.star
    exact hi.memLp_liftIoc.haarAddCircle
  have hgc : MemLp (AddCircle.liftIoc L 0 g) 2 (AddCircle.haarAddCircle (T := L)) := by
    have hi : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) (0+L))) := by simpa only [zero_add] using hg
    exact hi.memLp_liftIoc.haarAddCircle
  have hs := lp.hasSum_inner (𝕜 := ℂ) (fourierBasis.repr hfc.toLp) (fourierBasis.repr hgc.toLp)
  rw [fourierBasis.repr.inner_map_map] at hs
  simp only [RCLike.inner_apply',fourierBasis_repr] at hs
  have hcf (n : ℤ) : fourierCoeff hfc.toLp n = intervalFourierCoefficient L (fun x => conj (f x)) n := by
    rw [fourierCoeff_congr_ae hfc.coeFn_toLp,fourierCoeff_liftIoc_eq]
    simpa only [zero_add] using (intervalFourierCoefficient_eq_fourierCoeffOn hL (fun x => conj (f x)) n).symm
  have hcg (n : ℤ) : fourierCoeff hgc.toLp n = intervalFourierCoefficient L g n := by
    rw [fourierCoeff_congr_ae hgc.coeFn_toLp,fourierCoeff_liftIoc_eq]
    simpa only [zero_add] using (intervalFourierCoefficient_eq_fourierCoeffOn hL g n).symm
  simp only [hcf,hcg,intervalFourierCoefficient_conj,starRingEnd_self_apply] at hs
  have he : inner ℂ hfc.toLp hgc.toLp = (L : ℂ)⁻¹ * ∫ x in (0 : ℝ)..L, f x*g x := by
    rw [MeasureTheory.L2.inner_def]
    calc
      _ = ∫ x : AddCircle L, AddCircle.liftIoc L 0 (fun s => f s*g s) x ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [hfc.coeFn_toLp,hgc.coeFn_toLp] with x hx hy
        rw [RCLike.inner_apply',hx,hy]
        simp only [AddCircle.liftIoc,Function.comp_apply,Set.domRestrict_apply,starRingEnd_self_apply]
      _ = _ := by
        rw [AddCircle.integral_haarAddCircle,AddCircle.integral_liftIoc_eq_intervalIntegral]
        simp [Complex.real_smul]
  rw [he] at hs
  exact hs

/-- The original same-index sesquilinear formula remains valid on every positive period. -/
theorem hasSum_sesquilinear_intervalFourierCoefficient {L : ℝ} (hL : 0 < L) {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hg : MemLp g 2 (volume.restrict (Ioc 0 L))) :
    HasSum (fun n : ℤ => intervalFourierCoefficient L f n*conj (intervalFourierCoefficient L g n))
      ((L : ℂ)⁻¹ * ∫ x in (0 : ℝ)..L, f x*conj (g x)) := by
  have hgc : MemLp (fun x => conj (g x)) 2 (volume.restrict (Ioc 0 L)) := by
    simpa only [Pi.star_apply,Complex.star_def] using! hg.star
  have hs := hasSum_bilinear_intervalFourierCoefficient hL hf hgc
  simp only [intervalFourierCoefficient_conj] at hs
  simpa only [Function.comp_def,Equiv.neg_apply,neg_neg] using (Equiv.neg ℤ).hasSum_iff.mpr hs

end NLS.Fourier
