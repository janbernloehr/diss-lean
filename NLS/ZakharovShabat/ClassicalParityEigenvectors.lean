import NLS.Fourier.SignedSobolevExtension
import NLS.ZakharovShabat.PhysicalBaseParity
import NLS.ZakharovShabat.PhysicalParityMonodromy

/-!
# Classical endpoint solutions give original parity eigenvectors

Signed translation lifts a classical solution with multiplier `±1` to the
original weighted Fourier domain. Parity lets the physical eigen-equation on
the unit interval determine the full original coefficient equation.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The constructed solution is continuously differentiable in the physical variable on the real line. -/
theorem contDiff_classicalSolution (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    ContDiff ℝ 1 (classicalSolution Φ z v) := by
  apply contDiff_one_iff_deriv.mpr
  have hd := hasDerivAt_solution (classicalODECurve Φ z) v
  refine ⟨fun t => (hd t).differentiableAt,?_⟩
  have he : deriv (classicalSolution Φ z v) =
      integrand (classicalODECurve Φ z) (solutionCurve (classicalODECurve Φ z) v) := by
    funext t
    exact (hd t).deriv
  rw [he]
  exact continuous_integrand _ _

/-- Signed extension provides a parity-domain representative of every classical endpoint solution. -/
theorem exists_parity_domain_classicalSolution (Φ : Curve (ℂ × ℂ)) (z : ℂ) (r : ℤ)
    (v : ℂ × ℂ) (hend : classicalSolution Φ z v 1 = wave r 1 • v) :
    ∃ a : Domain 2, a ∈ domainParitySubspace r ∧
      EqOn (physicalDomain a) (classicalSolution Φ z v) (Icc 0 1) := by
  have hf := contDiff_classicalSolution Φ z v
  obtain ⟨a₁,ha₁,hs₁⟩ := exists_parity_sobolev_extension r hf.fst (by
    simpa only [classicalSolution_zero,Prod.smul_fst,smul_eq_mul] using congrArg Prod.fst hend)
  obtain ⟨a₂,ha₂,hs₂⟩ := exists_parity_sobolev_extension r hf.snd (by
    simpa only [classicalSolution_zero,Prod.smul_snd,smul_eq_mul] using congrArg Prod.snd hend)
  refine ⟨(a₁,a₂),fun n hn => ⟨ha₁ n hn,ha₂ n hn⟩,?_⟩
  intro x hx
  have hx2 : x ∈ Icc (0 : ℝ) 2 := ⟨hx.1,hx.2.trans (by norm_num)⟩
  apply Prod.ext
  · change sobolevSynthesis (by simp) a₁ (x : AddCircle (2 : ℝ)) = _
    rw [hs₁ x hx2,signedDouble_left _ _ hx.2]
  · change sobolevSynthesis (by simp) a₂ (x : AddCircle (2 : ℝ)) = _
    rw [hs₂ x hx2,signedDouble_left _ _ hx.2]

/-- Agreement with a classical solution transfers its physical eigen-equation on the unit interval. -/
theorem physical_unit_equation_of_eq_classicalSolution
    (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (a : Domain 2) (z : ℂ) (v : ℂ × ℂ)
    (ha : EqOn (physicalDomain a) (classicalSolution Φ z v) (Icc 0 1)) :
    physicalOperator (physicalBase φ) (physicalDomain a)
      =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • physicalDomain a x) := by
  simp only [Filter.EventuallyEq,ae_restrict_iff' measurableSet_Ioc] at hΦ ⊢
  filter_upwards [hΦ,(show ∀ᵐ x : ℝ, x ≠ (1 : ℝ) from by simp [ae_iff,measure_singleton])]
    with x hxΦ hx1
  intro hx
  have hxi : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1,lt_of_le_of_ne hx.2 hx1⟩
  have he : physicalDomain a =ᶠ[nhds x] classicalSolution Φ z v := by
    filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with t ht
    exact ha ⟨ht.1.le,ht.2.le⟩
  have h₁ := (he.fun_comp Prod.fst).deriv_eq
  have h₂ := (he.fun_comp Prod.snd).deriv_eq
  simp only [Function.comp_def] at h₁ h₂
  have hc := physicalOperator_classicalSolution Φ z v ⟨x,⟨hx.1.le,hx.2⟩⟩
  simp only [physicalOperator] at hc ⊢
  rw [h₁,h₂,hxΦ hx,ha ⟨hx.1.le,hx.2⟩]
  exact hc

/-- Every nonzero classical parity solution gives a nonzero original weighted-domain eigenvector. -/
theorem exists_parity_eigenvector_of_classicalSolution
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) (v : ℂ × ℂ) (hv : v ≠ 0)
    (hend : classicalSolution Φ z v 1 = wave r 1 • v) :
    ∃ a : Domain 2, a ≠ 0 ∧ a ∈ domainParitySubspace r ∧ spectralPencil (by simp) φ z a = 0 := by
  obtain ⟨a,ha,hs⟩ := exists_parity_domain_classicalSolution Φ z r v hend
  refine ⟨a,?_,ha,?_⟩
  · intro hz
    have h0 := hs (show (0 : ℝ) ∈ Icc 0 1 by simp)
    rw [hz] at h0
    apply hv
    simpa [physicalDomain] using! h0.symm
  · rw [spectralPencil_apply,
      operator_eq_smul_of_physical_unit_parity φ hφ a r ha z
        (physical_unit_equation_of_eq_classicalSolution φ Φ hΦ a z v hs),sub_self]

end NLS.ZakharovShabat
