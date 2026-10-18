import NLS.ZakharovShabat.PhysicalPoissonBracket
import NLS.Poisson.SourceHamiltonianDirection
import NLS.ZakharovShabat.SourceRealCotangent
import NLS.ZakharovShabat.SourcePhysicalRealL2

/-! # Hamiltonian directions on the physical Hilbert space

The physical direction has components minus i times the second gradient
and i times the first gradient. Every cotangent evaluates on it to the
literal Poisson integral. It equals the exact Fourier realization of the
source direction and preserves the physical real form for real cotangents
and real differentiable functionals. No flow existence is asserted here.
-/

noncomputable section
open Set Metric MeasureTheory Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- The physical Hamiltonian direction has the actual cross-gradient components. -/
def physicalHamiltonianDirection (L : IntervalPairL2 →L[ℂ] ℂ) : IntervalPairL2 :=
  WithLp.toLp 2 ((-I) • (physicalCotangentGradient L).snd,I • (physicalCotangentGradient L).fst)

/-- The zero physical cotangent has zero Hamiltonian direction. -/
@[simp] theorem physicalHamiltonianDirection_zero : physicalHamiltonianDirection 0 = 0 := by
  have hg : physicalCotangentGradient (0 : IntervalPairL2 →L[ℂ] ℂ) = 0 := by
    simp only [physicalCotangentGradient,ContinuousLinearMap.zero_comp,map_zero]
    change sourcePhysicalL2Equiv (0 : CoeffPair 2) = 0
    exact map_zero _
  rw [physicalHamiltonianDirection,hg]
  change WithLp.toLp 2 ((-I) • (0 : IntervalL2),I • (0 : IntervalL2)) = 0
  simp only [smul_zero]
  rfl

/-- Every physical cotangent evaluates on this direction to its literal Poisson integral. -/
theorem apply_physicalHamiltonianDirection (L M : IntervalPairL2 →L[ℂ] ℂ) :
    L (physicalHamiltonianDirection M) = physicalCotangentBivector L M := by
  rw [← physicalCotangentGradient_pairing L,physicalCotangentBivector,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  filter_upwards [Lp.coeFn_smul (-I) (physicalCotangentGradient M).snd,
    Lp.coeFn_smul I (physicalCotangentGradient M).fst] with x hx hy
  change (physicalCotangentGradient L).fst x*((-I) • (physicalCotangentGradient M).snd) x+
    (physicalCotangentGradient L).snd x*(I • (physicalCotangentGradient M).fst) x = _
  rw [hx,hy]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

/-- The actual physical cross-gradient field equals the Fourier realization of the source field. -/
theorem physicalHamiltonianDirection_eq_source (L : IntervalPairL2 →L[ℂ] ℂ) :
    physicalHamiltonianDirection L =
      sourcePhysicalL2 (sourceHamiltonianDirection le_rfl (L.comp sourcePhysicalL2)) := by
  let a := CoeffPair.cotangentCoefficients le_rfl (L.comp sourcePhysicalL2)
  have hi : CoeffPair.exponentInclusion le_rfl (hilbertPairHamiltonianDirection a) =
      hilbertPairHamiltonianDirection a := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> ext n <;> rfl
  rw [← sourcePhysicalL2Equiv_apply]
  change physicalHamiltonianDirection L = sourcePhysicalL2Equiv
    (CoeffPair.exponentInclusion le_rfl (hilbertPairHamiltonianDirection a))
  rw [hi]
  apply WithLp.ofLp_injective
  apply Prod.ext
  · change (-I) • NLS.Fourier.unitL2SynthesisEquiv (Coeff.reflection a.2) =
      NLS.Fourier.unitL2SynthesisEquiv ((-I) • Coeff.reflection a.2)
    exact (NLS.Fourier.unitL2SynthesisEquiv.map_smul (-I) (Coeff.reflection a.2)).symm
  · change I • NLS.Fourier.unitL2SynthesisEquiv (Coeff.reflection a.1) =
      NLS.Fourier.unitL2SynthesisEquiv (I • Coeff.reflection a.1)
    exact (NLS.Fourier.unitL2SynthesisEquiv.map_smul I (Coeff.reflection a.1)).symm

/-- Real physical cotangents produce directions in the same physical real form. -/
theorem physicalHamiltonianDirection_mem_real (L : IntervalPairL2 →L[ℂ] ℂ)
    (hL : ∀ h : physicalRealSubmodule, (L h.val).im = 0) :
    physicalHamiltonianDirection L ∈ physicalRealSubmodule := by
  have hsource : IsSourceRealCotangent (L.comp sourcePhysicalL2) := by
    intro φ hφ
    have h := hL (realSourcePhysicalL2Equiv ⟨φ,hφ⟩)
    change (L (sourcePhysicalL2Equiv φ)).im = 0 at h
    simpa only [ContinuousLinearMap.comp_apply,sourcePhysicalL2Equiv_apply] using h
  rw [physicalHamiltonianDirection_eq_source,← sourcePhysicalL2Equiv_apply]
  change sourcePhysicalL2Equiv.symm
    (sourcePhysicalL2Equiv (sourceHamiltonianDirection le_rfl (L.comp sourcePhysicalL2))) ∈
      realTypeSourceSubmodule 2
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact hsource.hamiltonianDirection_realType le_rfl

/-- The physical Hamiltonian vector field of an actual scalar functional. -/
def physicalHamiltonianVector (H : IntervalPairL2 → ℂ) (u : IntervalPairL2) : IntervalPairL2 :=
  physicalHamiltonianDirection (fderiv ℂ H u)

/-- The literal bracket is the full differential evaluated on the physical Hamiltonian field. -/
theorem fderiv_apply_physicalHamiltonianVector (F G : IntervalPairL2 → ℂ) (u : IntervalPairL2) :
    (fderiv ℂ F u) (physicalHamiltonianVector G u) = physicalBracket F G u :=
  apply_physicalHamiltonianDirection _ _

/-- A differentiable functional that is real on physical real inputs has a real Hamiltonian field. -/
theorem physicalHamiltonianVector_mem_real (H : IntervalPairL2 → ℂ) (u : physicalRealSubmodule)
    (hH : DifferentiableAt ℂ H u.val)
    (hreal : ∀ v : physicalRealSubmodule, (H v.val).im = 0) :
    physicalHamiltonianVector H u.val ∈ physicalRealSubmodule := by
  have hh : HasFDerivAt H (fderiv ℂ H u.val)
      (sourcePhysicalL2 (sourcePhysicalL2Equiv.symm u.val)) := by
    simpa only [sourcePhysicalL2_equiv_symm] using hH.hasFDerivAt
  have hd := hh.comp (sourcePhysicalL2Equiv.symm u.val)
    (sourcePhysicalL2.hasFDerivAt (x := sourcePhysicalL2Equiv.symm u.val))
  have hreal' : ∀ᶠ φ : CoeffPair 2 in 𝓝 (sourcePhysicalL2Equiv.symm u.val),
      IsRealType (CoeffPair.toMax 2 φ) → ((H ∘ sourcePhysicalL2) φ).im = 0 := by
    filter_upwards [] with φ hφ
    have h := hreal (realSourcePhysicalL2Equiv ⟨φ,hφ⟩)
    change (H (sourcePhysicalL2Equiv φ)).im = 0 at h
    simpa only [Function.comp_apply,sourcePhysicalL2Equiv_apply] using h
  have hc := isSourceRealCotangent_fderiv_of_eventually_real (H ∘ sourcePhysicalL2)
    ⟨sourcePhysicalL2Equiv.symm u.val,u.property⟩ hd.differentiableAt hreal'
  rw [hd.fderiv] at hc
  rw [physicalHamiltonianVector,physicalHamiltonianDirection_eq_source,← sourcePhysicalL2Equiv_apply]
  change sourcePhysicalL2Equiv.symm
    (sourcePhysicalL2Equiv (sourceHamiltonianDirection le_rfl ((fderiv ℂ H u.val).comp sourcePhysicalL2))) ∈
      realTypeSourceSubmodule 2
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact hc.hamiltonianDirection_realType le_rfl

end NLS.ZakharovShabat
