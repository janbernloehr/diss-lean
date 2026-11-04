import NLS.KdV.ClassicalHillGardnerTraceInvolution
import NLS.KdV.ClassicalTraceAsymptotics
import NLS.DifferentialPolynomial.EulerLagrange

/-! # Physical Hill trace pairing with the Lenard differential expression

An explicit concomitant of the actual trace kernel and any evaluated
periodic differential polynomial has derivative equal to their Lenard
pairing. This proves the vanishing period integral directly from the
constructed scalar Hill solutions, without an isospectral hypothesis.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory MvPolynomial
open scoped ContDiff
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.DifferentialPolynomial
namespace NLS.KdV

/-- The scalar Hill Lenard expression, retaining its spectral parameter. -/
def hillLenardPolynomial (b : ℂ) (p : DifferentialPolynomial.Polynomial) :
    DifferentialPolynomial.Polynomial :=
  -((spatialDerivative : DifferentialPolynomial.Polynomial → DifferentialPolynomial.Polynomial)^[3]) p+
    4*(X (false,0)-C b)*spatialDerivative p+2*X (false,1)*p

/-- The actual trace kernel pairs to zero with every periodic polynomial
Lenard direction, at every complex energy and smooth complex potential. -/
theorem integral_classicalHillTracePairingKernel_lenard_eq_zero
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (b : ℂ) (p : DifferentialPolynomial.Polynomial) :
    (∫ x in (0:ℝ)..1, classicalHillTracePairingKernel (scalarPotentialCurve f hf.continuous) b x*
      evaluate f 0 (hillLenardPolynomial b p) x)=0 := by
  let q := scalarPotentialCurve f hf.continuous
  let g := classicalHillTracePairingKernel q b
  let h := classicalHillTracePairingKernelDx q b
  let j := classicalHillTracePairingKernelFlux q b
  let a (n : ℕ) := evaluate f 0
    (((spatialDerivative : DifferentialPolynomial.Polynomial → DifferentialPolynomial.Polynomial)^[n]) p)
  have ha (n : ℕ) (x : ℝ) : HasDerivAt (a n) (a (n+1) x) x := by
    simpa only [a,Function.iterate_succ_apply'] using
      hasDerivAt_evaluate f 0 hf contDiff_const
        (((spatialDerivative : DifferentialPolynomial.Polynomial → DifferentialPolynomial.Polynomial)^[n]) p) x
  have hca (n : ℕ) : Continuous (a n) :=
    continuous_iff_continuousAt.mpr (fun x => (ha n x).continuousAt)
  let U (x : ℝ) : ℂ := -a 2 x*g x+a 1 x*h x-2*a 0 x*j x+2*a 0 x*(f x-b)*g x
  have hd (t : Icc (0:ℝ) 1) : HasDerivAt U
      (g t*evaluate f 0 (hillLenardPolynomial b p) t) t.val := by
    have hg := hasDerivAt_classicalHillTracePairingKernel q b t
    have hh := hasDerivAt_classicalHillTracePairingKernelDx q b t
    have hj := hasDerivAt_classicalHillTracePairingKernelFlux q b t
    have hf0 : HasDerivAt f (iteratedDeriv 1 f t) t.val := by
      rw [iteratedDeriv_one]
      exact (hf.differentiable (by simp) t).hasDerivAt
    convert! (((((ha 2 t).neg.mul hg).add ((ha 1 t).mul hh)).sub
      (((ha 0 t).const_mul 2).mul hj)).add
        (((((ha 0 t).const_mul 2).mul (hf0.sub_const b))).mul hg)) using 1
    simp [q,scalarPotentialCurve,g,a,hillLenardPolynomial,evaluate]
    ring
  have hc : Continuous U := by
    have hg := continuous_classicalHillTracePairingKernel q b
    have hh := continuous_classicalHillTracePairingKernelDx q b
    have hj := continuous_classicalHillTracePairingKernelFlux q b
    have hc0 := hca 0
    have hc1 := hca 1
    have hc2 := hca 2
    dsimp only [U,g,h,j]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1)
    hc.continuousOn (fun x (hx : x∈Ioo (0:ℝ) 1) => hd ⟨x,hx.1.le,hx.2.le⟩)
    (((continuous_classicalHillTracePairingKernel q b).mul
      (continuous_evaluate f 0 hf contDiff_const (hillLenardPolynomial b p))).intervalIntegrable 0 1)
  have he (n : ℕ) : a n 1=a n 0 := by
    simpa only [zero_add] using periodic_evaluate f 0 1 hp (fun _ => rfl)
      (((spatialDerivative : DifferentialPolynomial.Polynomial → DifferentialPolynomial.Polynomial)^[n]) p) 0
  have hU : U 1=U 0 := by
    dsimp only [U,g,h,j]
    rw [he 0,he 1,he 2,show f 1=f 0 by simpa using hp 0,
      classicalHillTracePairingKernel_endpoints q b,
      classicalHillTracePairingKernelDx_endpoints q b,
      classicalHillTracePairingKernelFlux_endpoints q b]
  exact hi.trans (by rw [hU,sub_self])

end NLS.KdV
