import NLS.Poisson.SourceHamiltonianDirection
import NLS.ZakharovShabat.SourceRealTypeConvex
import NLS.ComplexAnalysis.LocalRealAxisDerivative

/-! # Real cotangents and actual Hamiltonian directions

A complex cotangent that is real on real-type directions has conjugate
reflected Fourier coefficients. The actual Poisson signs therefore give
a real-type Hamiltonian direction. Two such cotangents have a real
bracket. Local real values of a differentiable functional supply this
cotangent property without an additional gradient assumption.
-/

noncomputable section
open Set Complex Filter Topology NLS.Poisson
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A complex cotangent preserves reality on the source real form. -/
def IsSourceRealCotangent (L : CoeffPair p →L[ℂ] ℂ) : Prop :=
  ∀ h : CoeffPair p, IsRealType (CoeffPair.toMax p h) → (L h).im = 0

/-- Local real values imply that the actual complex derivative is
real on every real-type source direction. -/
theorem isSourceRealCotangent_fderiv_of_eventually_real
    (F : CoeffPair p → ℂ) (φ : realTypeSourceLocus p)
    (hF : DifferentiableAt ℂ F φ.val)
    (hreal : ∀ᶠ ψ : CoeffPair p in 𝓝 φ.val,
      IsRealType (CoeffPair.toMax p ψ) → (F ψ).im = 0) :
    IsSourceRealCotangent (fderiv ℂ F φ.val) := by
  intro h hh
  let g : ℂ → ℂ := fun t => F (φ.val+t • h)
  have hline : HasDerivAt (fun t : ℂ => φ.val+t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const h).const_add φ.val
  have hg : HasDerivAt g ((fderiv ℂ F φ.val) h) 0 :=
    hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hcont : Tendsto (fun t : ℝ => φ.val+(t:ℂ) • h) (𝓝 0) (𝓝 φ.val) := by
    have hc : Continuous (fun t : ℝ => φ.val+(t:ℂ) • h) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hr : ∀ᶠ t : ℝ in 𝓝 0, (g (t:ℂ)).im = 0 := by
    filter_upwards [hcont.eventually hreal] with t ht
    exact ht (by simpa only [map_add,map_smul] using φ.property.add (hh.ofReal_smul t))
  exact NLS.ComplexAnalysis.HasDerivAt.im_eq_zero_of_eventually_real g _ 0 hg hr

/-- Real cotangents have the conjugate-reflected component relation
forced by the two real Fourier directions at each index. -/
theorem IsSourceRealCotangent.coordinate_conj
    {L : CoeffPair p →L[ℂ] ℂ} (hL : IsSourceRealCotangent L) (n : ℤ) :
    L (CoeffPair.inrCLM (lp.single p (-n) 1)) =
      conj (L (CoeffPair.inlCLM (lp.single p n 1))) := by
  let a := L (CoeffPair.inlCLM (lp.single p n 1))
  let b := L (CoeffPair.inrCLM (lp.single p (-n) 1))
  have hsource (z : ℂ) : IsRealType (CoeffPair.toMax p
      (z • CoeffPair.inlCLM (lp.single p n 1)+
        conj z • CoeffPair.inrCLM (lp.single p (-n) 1))) := by
    simpa [CoeffPair.inlCLM,CoeffPair.inrCLM,← lp.single_smul] using isRealType_single (p := p) n z
  have h₁ := hL _ (hsource 1)
  have h₂ := hL _ (hsource I)
  change b = conj a
  simp only [map_add,map_smul,smul_eq_mul,map_one,one_mul] at h₁
  change (a+b).im = 0 at h₁
  simp only [map_add,map_smul,smul_eq_mul,Complex.conj_I] at h₂
  change (I*a+(-I)*b).im = 0 at h₂
  apply Complex.ext
  · simp only [Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.neg_re,Complex.neg_im,zero_mul,one_mul,neg_one_mul] at h₂
    simp only [Complex.conj_re]
    linarith
  · simp only [Complex.add_im] at h₁
    simp only [Complex.conj_im]
    linarith

/-- The actual Hamiltonian direction of a real cotangent is real type. -/
theorem IsSourceRealCotangent.hamiltonianDirection_realType
    {L : CoeffPair p →L[ℂ] ℂ} (hL : IsSourceRealCotangent L)
    (h2p : (2 : ℝ≥0∞) ≤ p) :
    IsRealType (CoeffPair.toMax p (sourceHamiltonianDirection h2p L)) := by
  intro n
  change (sourceHamiltonianDirection h2p L).snd n =
    conj ((sourceHamiltonianDirection h2p L).fst (-n))
  simp only [sourceHamiltonianDirection,ContinuousLinearMap.comp_apply,
    CoeffPair.exponentInclusion_snd,CoeffPair.exponentInclusion_fst,
    Coeff.exponentInclusion_apply,hilbertPairHamiltonianDirection_snd,
    hilbertPairHamiltonianDirection_fst,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    Coeff.reflection_apply,CoeffPair.cotangentCoefficients_fst,
    CoeffPair.cotangentCoefficients_snd,neg_neg]
  have hc := hL.coordinate_conj (-n)
  simp only [neg_neg] at hc
  rw [hc]
  simp [map_mul]

/-- The actual bivector of two real cotangents is real. -/
theorem sourceBivector_im_eq_zero_of_real_cotangents
    (h2p : (2 : ℝ≥0∞) ≤ p) (L M : CoeffPair p →L[ℂ] ℂ)
    (hL : IsSourceRealCotangent L) (hM : IsSourceRealCotangent M) :
    (sourceBivector h2p L M).im = 0 := by
  rw [← apply_sourceHamiltonianDirection]
  exact hL _ (hM.hamiltonianDirection_realType h2p)

end NLS.ZakharovShabat
