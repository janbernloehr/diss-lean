import NLS.ZakharovShabat.SourceFiniteGapHigherActionExterior
import NLS.ZakharovShabat.SourceFullAbelianPhysicalContourLocal
import NLS.ZakharovShabat.SourcePrimitivePowerIsospectral

/-! # Action dependence of the physical finite-gap hierarchy

The all-order physical exterior trace and the actual isospectral primitive
identify independently defined Riccati Hamiltonians. One common admissible
circle avoids every periodic segment, including the collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The physical hierarchy is isospectral at every order and every real
finite-gap source, independently of any Birkhoff realization. -/
theorem sourceFiniteGapNLSHamiltonian_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (hg : ψ ∈ sourceFiniteGapLocus hp hp1)
    (h : ψ ∈ sourceIsospectralSet hp φ) (k : ℕ) :
    sourceFiniteGapNLSHamiltonian hp hp1 ψ hg k = sourceFiniteGapNLSHamiltonian hp hp1 φ hf k := by
  cases k with
  | zero => rfl
  | succ k =>
    obtain ⟨V,_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
    obtain ⟨C,hC⟩ := hfamilies φ
    obtain ⟨E,hE⟩ := hfamilies ψ
    have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
      rw [hC]
      exact mem_ball_self C.discs.sourceRadius_pos
    have hψ : ψ.val ∈ ball E.discs.source.val E.discs.sourceRadius := by
      rw [hE]
      exact mem_ball_self E.discs.sourceRadius_pos
    obtain ⟨Dφ⟩ := C.charts φ.val hφ
    obtain ⟨Dψ⟩ := E.charts ψ.val hψ
    obtain ⟨Tφ,_,hTφ⟩ := exists_sourceFiniteGap_higherAction_exterior C φ hφ hf
    obtain ⟨Tψ,_,hTψ⟩ := exists_sourceFiniteGap_higherAction_exterior E ψ hψ hg
    obtain ⟨R,hR,hlarge,hcircle,_⟩ := exists_sourceCanonicalRoot_circle_enclosing_finite_gaps
      hp hp1 ψ.val ∅ (max Tφ Tψ)
    have hcontour : (∮ z in C(0,R), z^k*sourceFullAbelianPrimitive hp hp1 V 0 (z,ψ.val)) =
        ∮ z in C(0,R), z^k*sourceFullAbelianPrimitive hp hp1 V 0 (z,φ.val) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      exact congrArg (fun a : ℂ => z^k*a)
        (sourceFullAbelianPrimitive_real_eq_of_isospectral hp hp1 V V φ ψ h Dψ Dφ 0 z (hcircle hz))
    have heq : sourceFiniteGapNLSHamiltonian hp hp1 ψ hg (k+1)/(2:ℂ)^k =
        sourceFiniteGapNLSHamiltonian hp hp1 φ hf (k+1)/(2:ℂ)^k := by
      rw [← hTψ R ((le_max_right _ _).trans hlarge) k,
        ← hTφ R ((le_max_left _ _).trans hlarge) k,hcontour]
    exact (div_left_inj' (pow_ne_zero k (by norm_num : (2:ℂ) ≠ 0))).mp heq

/-- Equal actual actions determine every independently defined physical
finite-gap Hamiltonian, at all finite exponents greater than one. -/
theorem sourceFiniteGapNLSHamiltonian_eq_of_actions
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (hg : ψ ∈ sourceFiniteGapLocus hp hp1)
    (h : ψ ∈ sourceRealActionLevelSet hp hp1 φ) (k : ℕ) :
    sourceFiniteGapNLSHamiltonian hp hp1 ψ hg k = sourceFiniteGapNLSHamiltonian hp hp1 φ hf k := by
  apply sourceFiniteGapNLSHamiltonian_eq_of_isospectral hp hp1 φ ψ hf hg _ k
  rwa [sourceIsospectralSet_eq_actionLevelSet_all_exponents hp hp1 φ]

end NLS.ZakharovShabat
