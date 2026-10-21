import NLS.Fourier.LineGalileanFourier
import NLS.ZakharovShabat.ClassicalNLSDifferenceEstimate
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.RealDeriv

/-! # Galilean covariance of the classical scalar NLS equation

This implements the Galilean statement from the introduction, printed p. 10.
-/

noncomputable section
open Complex
open scoped ContDiff ComplexConjugate
namespace NLS.ZakharovShabat

/-- The exact derivative of an arbitrary real angular phase. -/
theorem hasDerivAt_lineAngularPhase (ν θ x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp ((ν*y+θ:ℝ)*Complex.I))
      (Complex.exp ((ν*x+θ:ℝ)*Complex.I)*(ν:ℂ)*Complex.I) x := by
  have h := ((((hasDerivAt_id x).const_mul ν).add_const θ).ofReal_comp.mul_const Complex.I).cexp
  convert! h using 1
  simp [mul_assoc]

/-- The first spatial derivative of a translated and modulated profile. -/
theorem deriv_lineModulationTranslation (ν a θ : ℝ) (f : ℝ → ℂ)
    (hf : Differentiable ℝ f) (x : ℝ) :
    deriv (Fourier.lineModulationTranslation ν a θ f) x =
      Complex.exp ((ν*x+θ:ℝ)*Complex.I)*((ν:ℂ)*Complex.I*f (x-a)+deriv f (x-a)) := by
  have h := (hasDerivAt_lineAngularPhase ν θ x).mul
    ((hf (x-a)).hasDerivAt.scomp x ((hasDerivAt_id x).sub_const a))
  change deriv (fun y : ℝ => Complex.exp ((ν*y+θ:ℝ)*Complex.I)*f (y-a)) x = _
  have he := h.deriv
  change deriv (fun y : ℝ => Complex.exp ((ν*y+θ:ℝ)*Complex.I)*f (y-a)) x = _ at he
  rw [he]
  dsimp only [Function.comp_apply,id_eq]
  simp only [one_smul]
  ring

/-- The second spatial derivative retains all three physical modulation terms. -/
theorem deriv2_lineModulationTranslation (ν a θ : ℝ) (f : ℝ → ℂ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f)) (x : ℝ) :
    deriv (deriv (Fourier.lineModulationTranslation ν a θ f)) x =
      Complex.exp ((ν*x+θ:ℝ)*Complex.I)*
        (-(ν:ℂ)^2*f (x-a)+2*(ν:ℂ)*Complex.I*deriv f (x-a)+deriv (deriv f) (x-a)) := by
  have hd : deriv (Fourier.lineModulationTranslation ν a θ f) =
      fun y : ℝ => Complex.exp ((ν*y+θ:ℝ)*Complex.I)*
        ((ν:ℂ)*Complex.I*f (y-a)+deriv f (y-a)) :=
    funext (deriv_lineModulationTranslation ν a θ f hf)
  have h0 := (hf (x-a)).hasDerivAt.scomp x ((hasDerivAt_id x).sub_const a)
  have h1 := (hf' (x-a)).hasDerivAt.scomp x ((hasDerivAt_id x).sub_const a)
  have h := (hasDerivAt_lineAngularPhase ν θ x).mul
    ((h0.const_mul ((ν:ℂ)*Complex.I)).add h1)
  have he := h.deriv
  change deriv (fun y : ℝ => Complex.exp ((ν*y+θ:ℝ)*Complex.I)*
    ((ν:ℂ)*Complex.I*f (y-a)+deriv f (y-a))) x = _ at he
  rw [hd,he]
  dsimp only [Pi.add_apply,Function.comp_apply,id_eq]
  simp only [one_smul]
  ring_nf
  (simp only [Complex.I_sq]; ring)

/-- A unit complex phase factors out of the actual cubic nonlinearity. -/
theorem classicalNLSCubic_unit_mul (c z : ℂ) (hc : ‖c‖ = 1) :
    classicalNLSCubic (c*z) = c*classicalNLSCubic z := by
  have he : c*conj c = 1 := by
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hc]
    norm_num
  unfold classicalNLSCubic
  rw [map_mul]
  calc
    _ = (c*conj c)*c*(2*z^2*conj z) := by ring
    _ = _ := by rw [he,one_mul]

/-- The actual scalar NLS vector field under full-line modulation and translation. -/
theorem scalarClassicalNLSVectorField_lineModulationTranslation
    (ν a θ : ℝ) (f : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) (x : ℝ) :
    scalarClassicalNLSVectorField (Fourier.lineModulationTranslation ν a θ f) x =
      Complex.exp ((ν*x+θ:ℝ)*Complex.I)*
        (scalarClassicalNLSVectorField f (x-a)-2*(ν:ℂ)*deriv f (x-a)-
          Complex.I*(ν:ℂ)^2*f (x-a)) := by
  rw [scalarClassicalNLSVectorField,deriv2_lineModulationTranslation ν a θ f hf hf']
  rw [Fourier.lineModulationTranslation,
    classicalNLSCubic_unit_mul _ _ (norm_exp_ofReal_mul_I _)]
  unfold scalarClassicalNLSVectorField
  ring_nf
  (simp only [Complex.I_sq]; ring)

/-- The time derivative along the actual moving frame is the time derivative
minus twice the boost parameter times the spatial derivative. -/
theorem hasDerivAt_scalarNLS_movingFrame (U : ℝ × ℝ → ℂ)
    (hU : Differentiable ℝ U) (ν t x : ℝ) :
    HasDerivAt (fun τ : ℝ => U (τ,x-2*ν*τ))
      (deriv (fun τ : ℝ => U (τ,x-2*ν*t)) t -
        2*(ν:ℂ)*deriv (fun y : ℝ => U (t,y)) (x-2*ν*t)) t := by
  let F := fderiv ℝ U (t,x-2*ν*t)
  have hd : HasFDerivAt U F (t,x-2*ν*t) := (hU _).hasFDerivAt
  have ht := hd.comp_hasDerivAt t ((hasDerivAt_id t).prodMk
    (hasDerivAt_const t (x-2*ν*t)))
  have hx := hd.comp_hasDerivAt (x-2*ν*t)
    ((hasDerivAt_const (x-2*ν*t) t).prodMk (hasDerivAt_id (x-2*ν*t)))
  have hm := hd.comp_hasDerivAt t ((hasDerivAt_id t).prodMk
    ((hasDerivAt_const t x).sub ((hasDerivAt_id t).const_mul (2*ν))))
  have ht' := ht.deriv
  have hx' := hx.deriv
  change deriv (fun τ : ℝ => U (τ,x-2*ν*t)) t = F (1,0) at ht'
  change deriv (fun y : ℝ => U (t,y)) (x-2*ν*t) = F (0,1) at hx'
  rw [ht',hx']
  convert! hm using 1
  simp only [mul_one,zero_sub]
  have he : ((1:ℝ),-(2*ν)) = ((1:ℝ),0)+(-(2*ν)) • ((0:ℝ),1) := by ext <;> simp
  rw [he,map_add,map_smul]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The literal full-line Galilean transformation preserves the physical scalar
NLS equation for a jointly differentiable solution with two spatial derivatives. -/
theorem hasDerivAt_scalarNLS_galilean (U : ℝ × ℝ → ℂ)
    (hU : Differentiable ℝ U)
    (hxx : ∀ t : ℝ, Differentiable ℝ (deriv (fun y : ℝ => U (t,y))))
    (hUt : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => U (τ,x))
      (scalarClassicalNLSVectorField (fun y : ℝ => U (t,y)) x) t)
    (ν t x : ℝ) :
    HasDerivAt (fun τ : ℝ => Fourier.lineGalileanSlice ν τ (fun y : ℝ => U (τ,y)) x)
      (scalarClassicalNLSVectorField
        (Fourier.lineGalileanSlice ν t (fun y : ℝ => U (t,y))) x) t := by
  have hx : Differentiable ℝ (fun y : ℝ => U (t,y)) :=
    hU.comp ((differentiable_const (c := t)).prodMk differentiable_id)
  have hp := ((((hasDerivAt_id t).const_mul (-(ν^2))).const_add (ν*x)).ofReal_comp.mul_const
    Complex.I).cexp
  have h := hp.mul (hasDerivAt_scalarNLS_movingFrame U hU ν t x)
  change HasDerivAt (fun τ : ℝ =>
    Complex.exp ((ν*x+(-(ν^2))*τ:ℝ)*Complex.I)*U (τ,x-2*ν*τ)) _ t
  convert! h using 1
  rw [Fourier.lineGalileanSlice,
    scalarClassicalNLSVectorField_lineModulationTranslation ν (2*ν*t) (-(ν^2)*t)
      (fun y : ℝ => U (t,y)) hx (hxx t) x,
    (hUt t (x-2*ν*t)).deriv]
  simp only [mul_one,id_eq]
  push_cast
  ring

/-- The physical Galilean transformation retains joint differentiability. -/
theorem differentiable_scalarNLS_galilean (U : ℝ × ℝ → ℂ)
    (hU : Differentiable ℝ U) (ν : ℝ) :
    Differentiable ℝ (fun z : ℝ × ℝ =>
      Fourier.lineGalileanSlice ν z.1 (fun y : ℝ => U (z.1,y)) z.2) := by
  unfold Fourier.lineGalileanSlice Fourier.lineModulationTranslation
  fun_prop

/-- Every smooth spatial slice remains smooth under the literal Galilean transformation. -/
theorem contDiff_scalarNLS_galilean (U : ℝ × ℝ → ℂ)
    (hU : ∀ t : ℝ, ContDiff ℝ ∞ (fun y : ℝ => U (t,y))) (ν t : ℝ) :
    ContDiff ℝ ∞ (Fourier.lineGalileanSlice ν t (fun y : ℝ => U (t,y))) := by
  unfold Fourier.lineGalileanSlice Fourier.lineModulationTranslation
  have hr : ContDiff ℝ ∞ (fun x : ℝ => ν*x+(-(ν^2))*t) := by fun_prop
  have hc : ContDiff ℝ ∞ (fun x : ℝ => Complex.exp ((ν*x+(-(ν^2))*t:ℝ)*Complex.I)) :=
    ((Complex.ofRealCLM.contDiff.comp hr).mul contDiff_const).cexp
  exact hc.mul ((hU t).comp (by fun_prop))

end NLS.ZakharovShabat
