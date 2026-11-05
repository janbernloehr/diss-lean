import NLS.Poisson.SobolevGardnerGradient

/-! # Scalar composition of actual H¹ Gardner gradients -/
noncomputable section
open Complex NLS.ZakharovShabat
namespace NLS.Poisson.SobolevGardnerGradientAt
variable {F G : ScalarDomain 2 → ℂ} {a : ScalarDomain 2}

def comp (P : SobolevGardnerGradientAt F a) (g : ℂ → ℂ) (dg : ℂ)
    (hg : HasDerivAt g dg (F a)) : SobolevGardnerGradientAt (fun b => g (F b)) a where
  gradient := dg • P.gradient
  hasFDerivAt := by
    have hd := hg.comp_hasFDerivAt a P.hasFDerivAt
    have he : dg • ((reflectedHilbertPairing (scalarInclusion P.gradient)).comp scalarInclusion) =
        (reflectedHilbertPairing (scalarInclusion (dg • P.gradient))).comp scalarInclusion := by
      ext h
      simp only [map_smul,ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul]
    simpa only [he,Function.comp_def] using! hd

theorem comp_bracket (P : SobolevGardnerGradientAt F a) (Q : SobolevGardnerGradientAt G a)
    (g : ℂ → ℂ) (dg : ℂ) (hg : HasDerivAt g dg (F a)) :
    (P.comp g dg hg).bracket Q = dg*P.bracket Q := by
  simp only [bracket,comp,map_smul,smul_apply,smul_eq_mul]

theorem bracket_comp (P : SobolevGardnerGradientAt F a) (Q : SobolevGardnerGradientAt G a)
    (g : ℂ → ℂ) (dg : ℂ) (hg : HasDerivAt g dg (G a)) :
    P.bracket (Q.comp g dg hg) = dg*P.bracket Q := by
  simp only [bracket,comp,map_smul,smul_eq_mul]

end NLS.Poisson.SobolevGardnerGradientAt
