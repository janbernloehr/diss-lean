import NLS.ZakharovShabat.ClassicalFundamentalSolution

/-! # Division-free spatial algebra for discriminant gradients

The adjugate polynomial works at every spectral parameter, including zeros
of every monodromy entry. Its scalar transport equation is proved directly
from the physical ODE, so no generic-eigenvector division is needed.
-/
noncomputable section
open Complex Matrix
namespace NLS.ZakharovShabat

def discriminantGradientState (T : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ × ℂ) : ℂ × ℂ :=
  (I*((T 0 0-T 1 1)*a.2*b.2-T 0 1*a.2^2+T 1 0*b.2^2),
   I*((T 0 0-T 1 1)*a.1*b.1-T 0 1*a.1^2+T 1 0*b.1^2))

def discriminantXiState (T : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ × ℂ) : ℂ :=
  (T 0 0-T 1 1)*(a.1*b.2+a.2*b.1)-2*T 0 1*a.1*a.2+2*T 1 0*b.1*b.2

theorem hasDerivAt_discriminantGradientState
    (T : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℝ → ℂ × ℂ) (φ : ℂ × ℂ) (z : ℂ) (x : ℝ)
    (ha : HasDerivAt a (classicalODECoefficient φ z (a x)) x)
    (hb : HasDerivAt b (classicalODECoefficient φ z (b x)) x) :
    HasDerivAt (fun y => discriminantGradientState T (a y) (b y))
      (2*I*z*(discriminantGradientState T (a x) (b x)).1+discriminantXiState T (a x) (b x)*φ.2,
       -2*I*z*(discriminantGradientState T (a x) (b x)).2-discriminantXiState T (a x) (b x)*φ.1) x := by
  have ha1 := HasFDerivAt.hasDerivAt ha.fst
  have ha2 := HasFDerivAt.hasDerivAt ha.snd
  have hb1 := HasFDerivAt.hasDerivAt hb.fst
  have hb2 := HasFDerivAt.hasDerivAt hb.snd
  have h1 := ((((ha2.mul hb2).const_mul (T 0 0-T 1 1)).sub
    ((ha2.pow 2).const_mul (T 0 1))).add ((hb2.pow 2).const_mul (T 1 0))).const_mul I
  have h2 := ((((ha1.mul hb1).const_mul (T 0 0-T 1 1)).sub
    ((ha1.pow 2).const_mul (T 0 1))).add ((hb1.pow 2).const_mul (T 1 0))).const_mul I
  convert! h1.prodMk h2 using 1
  · funext y
    apply Prod.ext <;> dsimp [discriminantGradientState] <;> ring
  · apply Prod.ext <;>
      simp only [discriminantGradientState,discriminantXiState,classicalODECoefficient_apply,
        ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul] <;>
      dsimp <;> ring_nf <;> simp only [I_sq] <;> ring

theorem hasDerivAt_discriminantXiState
    (T : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℝ → ℂ × ℂ) (φ : ℂ × ℂ) (z : ℂ) (x : ℝ)
    (ha : HasDerivAt a (classicalODECoefficient φ z (a x)) x)
    (hb : HasDerivAt b (classicalODECoefficient φ z (b x)) x) :
    HasDerivAt (fun y => discriminantXiState T (a y) (b y))
      (2*φ.1*(discriminantGradientState T (a x) (b x)).1-
        2*φ.2*(discriminantGradientState T (a x) (b x)).2) x := by
  have ha1 := HasFDerivAt.hasDerivAt ha.fst
  have ha2 := HasFDerivAt.hasDerivAt ha.snd
  have hb1 := HasFDerivAt.hasDerivAt hb.fst
  have hb2 := HasFDerivAt.hasDerivAt hb.snd
  have h := ((((ha1.mul hb2).add (ha2.mul hb1)).const_mul (T 0 0-T 1 1)).sub
    ((ha1.mul ha2).const_mul (2*T 0 1))).add ((hb1.mul hb2).const_mul (2*T 1 0))
  convert! h using 1
  · funext y
    dsimp [discriminantXiState]
    ring
  · simp only [discriminantGradientState,classicalODECoefficient_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
    dsimp
    ring

end NLS.ZakharovShabat
