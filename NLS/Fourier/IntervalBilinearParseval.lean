import NLS.Fourier.IntervalParseval

/-! # Unconjugated bilinear Parseval on the unit interval

The differential and Poisson conventions use bilinear complex duality.
Conjugating the first Hilbert argument converts ordinary Parseval to this
pairing, with the required reversed frequency in one factor.
-/

noncomputable section
open Complex MeasureTheory Set
open scoped ComplexConjugate
namespace NLS.Fourier

/-- Unit-period physical Fourier coefficients in the original raw convention. -/
def unitFourierCoefficient (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, f x*wave (-(2*n)) x

theorem unitFourierCoefficient_eq_fourierCoeffOn (f : ℝ → ℂ) (n : ℤ) :
    unitFourierCoefficient f n = fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n := by
  rw [fourierCoeffOn_one]
  unfold unitFourierCoefficient halfCoefficient
  ring

theorem unitFourierCoefficient_conj (f : ℝ → ℂ) (n : ℤ) :
    unitFourierCoefficient (fun x => conj (f x)) n = conj (unitFourierCoefficient f (-n)) := by
  unfold unitFourierCoefficient
  rw [← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [map_mul,← wave_neg]
  congr 1
  congr 1
  omega

/-- The bilinear physical pairing is the absolutely convergent Hilbert
Fourier pairing, with frequency reversed in the first factor. -/
theorem hasSum_bilinear_unitFourierCoefficient {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    HasSum (fun n : ℤ => unitFourierCoefficient f (-n)*unitFourierCoefficient g n)
      (∫ x in (0 : ℝ)..1, f x*g x) := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hfc : MemLp (AddCircle.liftIoc (1 : ℝ) 0 (fun x => conj (f x))) 2
      (AddCircle.haarAddCircle (T := (1 : ℝ))) := by
    have hi : MemLp (fun x => conj (f x)) 2 (volume.restrict (Ioc (0 : ℝ) (0+1))) := by
      simpa only [zero_add,Function.comp_def] using! memLp_two_interval (continuous_conj.comp hf) 0 1 (by norm_num)
    exact hi.memLp_liftIoc.haarAddCircle
  have hgc : MemLp (AddCircle.liftIoc (1 : ℝ) 0 g) 2
      (AddCircle.haarAddCircle (T := (1 : ℝ))) := by
    have hi : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) (0+1))) := by
      simpa only [zero_add] using memLp_two_interval hg 0 1 (by norm_num)
    exact hi.memLp_liftIoc.haarAddCircle
  have hs := lp.hasSum_inner (𝕜 := ℂ) (fourierBasis.repr hfc.toLp) (fourierBasis.repr hgc.toLp)
  rw [fourierBasis.repr.inner_map_map] at hs
  simp only [RCLike.inner_apply',fourierBasis_repr] at hs
  have hcf (n : ℤ) : fourierCoeff hfc.toLp n = unitFourierCoefficient (fun x => conj (f x)) n := by
    rw [fourierCoeff_congr_ae hfc.coeFn_toLp,fourierCoeff_liftIoc_eq]
    simpa only [zero_add] using (unitFourierCoefficient_eq_fourierCoeffOn (fun x => conj (f x)) n).symm
  have hcg (n : ℤ) : fourierCoeff hgc.toLp n = unitFourierCoefficient g n := by
    rw [fourierCoeff_congr_ae hgc.coeFn_toLp,fourierCoeff_liftIoc_eq]
    simpa only [zero_add] using (unitFourierCoefficient_eq_fourierCoeffOn g n).symm
  simp only [hcf,hcg,unitFourierCoefficient_conj,starRingEnd_self_apply] at hs
  have he : inner ℂ hfc.toLp hgc.toLp = ∫ x in (0 : ℝ)..1, f x*g x := by
    rw [MeasureTheory.L2.inner_def]
    calc
      _ = ∫ x : AddCircle (1 : ℝ),
          AddCircle.liftIoc (1 : ℝ) 0 (fun s => f s*g s) x ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [hfc.coeFn_toLp,hgc.coeFn_toLp] with x hx hy
        rw [RCLike.inner_apply',hx,hy]
        simp only [AddCircle.liftIoc,Function.comp_apply,Set.domRestrict_apply,starRingEnd_self_apply]
      _ = ∫ x in (0 : ℝ)..1, f x*g x := by
        rw [AddCircle.integral_haarAddCircle,AddCircle.integral_liftIoc_eq_intervalIntegral]
        simp
  rw [he] at hs
  exact hs

theorem tsum_bilinear_unitFourierCoefficient {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    (∑' n : ℤ, unitFourierCoefficient f (-n)*unitFourierCoefficient g n) =
      ∫ x in (0 : ℝ)..1, f x*g x :=
  (hasSum_bilinear_unitFourierCoefficient hf hg).tsum_eq

end NLS.Fourier
