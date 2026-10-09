import NLS.ZakharovShabat.SourceAntiDiscriminantIdentity
import NLS.ZakharovShabat.ExponentSourcePotentials
import NLS.Fourier.SobolevDerivative

/-! # An exact triangular Fourier boundary equation

For the finite source (u,0), the Dirichlet equation at iH is a finite
reciprocal Fourier sum. This concerns the actual boundary spectrum, not a
sufficient resolvent estimate. No norm or counterexample claim is made here.
-/
noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The finite Fourier functional at positive imaginary height. -/
def triangularBoundarySum (a : ℤ →₀ ℂ) (H : ℝ) : ℂ :=
  ∑ n ∈ a.support, a n / ((H : ℂ)-(Real.pi : ℂ)*n*I)

/-- An explicit primitive for the integrating-factor equation. -/
def triangularBoundaryPrimitive (a : ℤ →₀ ℂ) (H t : ℝ) : ℂ :=
  ∑ n ∈ a.support, a n / ((H : ℂ)-(Real.pi : ℂ)*n*I) *
    (exp (-2*(H : ℂ)*t)*wave (2*n) t-1)

theorem triangular_denominator_ne_zero {H : ℝ} (hH : 0 < H) (n : ℤ) :
    (H : ℂ)-(Real.pi : ℂ)*n*I ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [sub_re,mul_re,mul_im,I_re,I_im,ofReal_re,ofReal_im,intCast_re,intCast_im,
    mul_zero,zero_mul,sub_zero,add_zero,zero_re] at hr
  linarith

@[simp] theorem triangularBoundaryPrimitive_zero (a : ℤ →₀ ℂ) (H : ℝ) :
    triangularBoundaryPrimitive a H 0 = 0 := by simp [triangularBoundaryPrimitive]

/-- The endpoint primitive has the same scalar factor at every integer mode. -/
theorem triangularBoundaryPrimitive_one (a : ℤ →₀ ℂ) (H : ℝ) :
    triangularBoundaryPrimitive a H 1 = triangularBoundarySum a H * (exp (-2*(H : ℂ))-1) := by
  simp only [triangularBoundaryPrimitive,Complex.ofReal_one,mul_one,wave_even_at_one]
  rw [← Finset.sum_mul]
  rfl

/-- Differentiating the finite primitive recovers the exact source polynomial. -/
theorem hasDerivAt_triangularBoundaryPrimitive (a : ℤ →₀ ℂ) {H : ℝ} (hH : 0 < H) (t : ℝ) :
    HasDerivAt (triangularBoundaryPrimitive a H)
      (-2*exp (-2*(H : ℂ)*t)*polynomial a t) t := by
  have he : HasDerivAt (fun s : ℝ => exp (-2*(H : ℂ)*s))
      (exp (-2*(H : ℂ)*t)*(-2*(H : ℂ))) t := by
    simpa using (Complex.ofRealCLM.hasDerivAt.const_mul (-2*(H : ℂ))).cexp
  have hd (n : ℤ) : HasDerivAt (fun s : ℝ => a n / ((H : ℂ)-(Real.pi : ℂ)*n*I) *
      (exp (-2*(H : ℂ)*s)*wave (2*n) s-1))
      (-2*exp (-2*(H : ℂ)*t)*(a n*wave (2*n) t)) t := by
    convert! ((he.mul (hasDerivAt_wave (2*n) t)).sub_const 1).const_mul
      (a n / ((H : ℂ)-(Real.pi : ℂ)*n*I)) using 1
    push_cast
    field_simp [triangular_denominator_ne_zero hH n]
    ring
  have hs := HasDerivAt.sum (u := a.support) (fun n _ => hd n)
  convert! hs using 1
  · funext s
    simp only [triangularBoundaryPrimitive,Finset.sum_apply]
  · simp only [polynomial,Finsupp.sum,Finset.mul_sum]

/-- The explicit solution with initial vector (1,1), whose endpoints test Dirichlet boundary conditions. -/
def triangularBoundarySolution (a : ℤ →₀ ℂ) (H t : ℝ) : ℂ × ℂ :=
  (exp ((H : ℂ)*t)*(1-I/2*triangularBoundaryPrimitive a H t),exp (-(H : ℂ)*t))

/-- The explicit expression solves the original triangular spectral problem on the unit interval. -/
theorem classicalSolution_triangularFourier (a : ℤ →₀ ℂ) {H : ℝ} (hH : 0 < H)
    (t : Icc (0 : ℝ) 1) :
    classicalSolution (finiteSourceCurve (a,0)) ((H : ℂ)*I) (1,1) t =
      triangularBoundarySolution a H t := by
  have he (c : ℂ) (s : ℝ) : HasDerivAt (fun x : ℝ => exp (c*x)) (exp (c*s)*c) s := by
    simpa using (Complex.ofRealCLM.hasDerivAt.const_mul c).cexp
  have hd (s : ℝ) := ((he H s).mul
    ((hasDerivAt_const s (1 : ℂ)).sub ((hasDerivAt_triangularBoundaryPrimitive a hH s).const_mul (I/2)))).prodMk
      (he (-H) s)
  have h := classicalSolution_unique (finiteSourceCurve (a,0)) ((H : ℂ)*I) (1,1)
    (triangularBoundarySolution a H)
    (fun s _ => (hd s).continuousAt.continuousWithinAt)
    (by simp [triangularBoundarySolution]) (by
      intro s _
      convert! hd s.val using 1
      simp only [classicalODECoefficient_apply,finiteSourceCurve,ContinuousMap.coe_mk,
        BoundaryCondition.periodOnePair,polynomial,Finsupp.sum, Finsupp.support_zero,Finset.sum_empty,
        triangularBoundarySolution]
      apply Prod.ext
      · dsimp
        have hx : exp ((H : ℂ)*s.val)*exp (-2*(H : ℂ)*s.val) = exp (-(H : ℂ)*s.val) := by
          rw [← exp_add]; congr 1; ring
        linear_combination (norm := ring_nf) (-I*(∑ n ∈ a.support, a n*wave (2*n) s.val))*hx
        simp [I_sq]
      · dsimp
        ring_nf
        simp [I_sq])
  exact (h t.property).symm

/-- The exact finite Fourier equation yields an actual classical Dirichlet root. -/
theorem classicalDirichlet_triangularFourier_root (a : ℤ →₀ ℂ) {H : ℝ} (hH : 0 < H)
    (ha : triangularBoundarySum a H = 2*I) :
    classicalSeparatedCharacteristic .dirichlet (finiteSourceCurve (a,0)) ((H : ℂ)*I) = 0 := by
  apply (classicalSeparatedCharacteristic_eq_zero_iff .dirichlet _ _).mpr
  rw [show BoundaryCondition.extensionSign .dirichlet = 1 from rfl]
  rw [classicalSolution_triangularFourier a hH ⟨1,by constructor <;> norm_num⟩]
  simp only [triangularBoundarySolution,Complex.ofReal_one,mul_one,triangularBoundaryPrimitive_one,ha]
  have he : 1-I/2*(2*I*(exp (-2*(H : ℂ))-1)) = exp (-2*(H : ℂ)) := by
    ring_nf
    simp [I_sq]
  rw [he,← exp_add]
  rw [one_mul]
  congr 1
  ring


/-- Finite ordinary characteristics have the classical normalization at every finite exponent. -/
theorem periodOneBoundaryCharacteristic_finite_eq_classical_all
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    periodOneBoundaryCharacteristic hp hp1 b (CoeffPair.ofFinsupp (p := p) a) z =
      classicalSeparatedCharacteristic b (finiteSourceCurve a) z := by
  by_cases hp2 : p ≤ 2
  · have he := congrFun (periodOneBoundaryCharacteristic_exponent hp (by norm_num) hp1
      (by norm_num) hp2 b (CoeffPair.ofFinsupp a)) z
    simpa only [CoeffPair.exponentInclusion_ofFinsupp,
      periodOneBoundaryCharacteristic_finite_eq_classical] using he
  · have he := congrFun (periodOneBoundaryCharacteristic_exponent (by norm_num) hp
      (by norm_num) hp1 (le_of_not_ge hp2) b (CoeffPair.ofFinsupp a)) z
    simpa only [CoeffPair.exponentInclusion_ofFinsupp,
      periodOneBoundaryCharacteristic_finite_eq_classical] using he.symm

/-- The triangular Fourier equation gives an eigenvalue of the actual source Dirichlet operator. -/
theorem mem_sourceDirichletSpectrum_of_triangularBoundarySum
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : ℤ →₀ ℂ) {H : ℝ} (hH : 0 < H) (ha : triangularBoundarySum a H = 2*I) :
    (H : ℂ)*I ∈ BoundaryCondition.spectrum .dirichlet hp
      (periodOneBoundaryPotential hp hp1 (CoeffPair.ofFinsupp (a,0))).val
      (periodOneBoundaryPotential hp hp1 (CoeffPair.ofFinsupp (a,0))).property := by
  apply (periodOneBoundaryCharacteristic_eq_zero_iff hp hp1 .dirichlet _ _).mp
  rw [periodOneBoundaryCharacteristic_finite_eq_classical_all]
  exact classicalDirichlet_triangularFourier_root a hH ha

end NLS.ZakharovShabat
