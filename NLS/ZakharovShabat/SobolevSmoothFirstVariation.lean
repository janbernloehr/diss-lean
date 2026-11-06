import NLS.ZakharovShabat.SobolevSourceSmoothDensity
import Mathlib.Analysis.Analytic.Constructions

/-! # Transferring actual smooth first variations to Sobolev differentials -/
noncomputable section
open NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

theorem sobolev_affine_coefficients (s : ℕ) (a h : ScalarSobolev s) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (ha : ∀ j, a.val j = periodOneCoefficient f j)
    (hh : ∀ j, h.val j = periodOneCoefficient g j) (z : ℂ) (j : ℤ) :
    (a+z • h).val j = periodOneCoefficient (fun t => f t+z*g t) j := by
  change a.val j+z*h.val j = periodOneCoefficient (f+z • g) j
  rw [periodOneCoefficient_add f (z • g) hf (hg.const_smul z)]
  have he : periodOneCoefficient (z • g) j = z*periodOneCoefficient g j := by
    rw [periodOneCoefficient, fourierCoeffOn.const_smul]
    rfl
  rw [he, ha, hh]

theorem fderiv_scalarSobolev_eq_smooth_variation (s : ℕ) (F : ScalarSobolev s → ℂ)
    (I : (ℝ → ℂ) → ℂ) (u h : ScalarSobolev s) (f g : ℝ → ℂ)
    (hF : AnalyticAt ℂ F u)
    (hagree : ∀ (a : ScalarSobolev s) (v : ℝ → ℂ), ContDiff ℝ ∞ v → Function.Periodic v 1 →
      (∀ j, a.val j = periodOneCoefficient v j) → F a = I v)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (huc : ∀ j, u.val j = periodOneCoefficient f j)
    (hhc : ∀ j, h.val j = periodOneCoefficient g j) (d : ℂ)
    (hd : HasDerivAt (fun z : ℂ => I (fun x => f x+z*g x)) d 0) :
    fderiv ℂ F u h = d := by
  have he (z : ℂ) : F (u+z • h) = I (fun x => f x+z*g x) :=
    hagree (u+z • h) _ (hf.add (contDiff_const.mul hg))
      (fun x => by rw [hpf x,hpg x])
      (sobolev_affine_coefficients s u h f g hf.continuous hg.continuous huc hhc z)
  have hline : HasDerivAt (fun z : ℂ => u+z • h) h 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const h |>.const_add u
  have hzero : u+(0 : ℂ) • h = u := by simp
  have hdF := (hzero ▸ hF.differentiableAt.hasFDerivAt).comp_hasDerivAt 0 hline
  simp only [Function.comp_def, he, hzero] at hdF
  exact hdF.unique hd

theorem fderiv_sobolevSource_eq_smooth_variation (s : ℕ) (F : SobolevSource s → ℂ)
    (I : (ℝ → ℂ) → (ℝ → ℂ) → ℂ) (ab cd : SobolevSource s) (a b h l : ℝ → ℂ)
    (hF : AnalyticAt ℂ F ab)
    (hagree : ∀ (ef : SobolevSource s) (v w : ℝ → ℂ), ContDiff ℝ ∞ v → ContDiff ℝ ∞ w →
      Function.Periodic v 1 → Function.Periodic w 1 →
      (∀ j, ef.1.val j = periodOneCoefficient v j) →
      (∀ j, ef.2.val j = periodOneCoefficient w j) → F ef = I v w)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hh : ContDiff ℝ ∞ h) (hl : ContDiff ℝ ∞ l)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) (hpl : Function.Periodic l 1)
    (hac : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbc : ∀ j, ab.2.val j = periodOneCoefficient b j)
    (hhc : ∀ j, cd.1.val j = periodOneCoefficient h j)
    (hlc : ∀ j, cd.2.val j = periodOneCoefficient l j) (d : ℂ)
    (hd : HasDerivAt (fun z : ℂ => I (fun x => a x+z*h x) (fun x => b x+z*l x)) d 0) :
    fderiv ℂ F ab cd = d := by
  have he (z : ℂ) : F (ab+z • cd) = I (fun x => a x+z*h x) (fun x => b x+z*l x) :=
    hagree (ab+z • cd) _ _ (ha.add (contDiff_const.mul hh)) (hb.add (contDiff_const.mul hl))
      (fun x => by rw [hpa x,hph x]) (fun x => by rw [hpb x,hpl x])
      (sobolev_affine_coefficients s ab.1 cd.1 a h ha.continuous hh.continuous hac hhc z)
      (sobolev_affine_coefficients s ab.2 cd.2 b l hb.continuous hl.continuous hbc hlc z)
  have hline : HasDerivAt (fun z : ℂ => ab+z • cd) cd 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const cd |>.const_add ab
  have hzero : ab+(0 : ℂ) • cd = ab := by simp
  have hdF := (hzero ▸ hF.differentiableAt.hasFDerivAt).comp_hasDerivAt 0 hline
  simp only [Function.comp_def, he, hzero] at hdF
  exact hdF.unique hd

end NLS.ZakharovShabat
