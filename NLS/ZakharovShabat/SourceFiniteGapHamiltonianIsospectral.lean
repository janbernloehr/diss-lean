import NLS.ZakharovShabat.SourceFullAbelianHamiltonianInversion
import NLS.ZakharovShabat.SourceAbelianPrimitiveIsospectral
import NLS.ZakharovShabat.SourceFiniteGapHigherActionExterior
import NLS.ZakharovShabat.SourceFullAbelianPhysicalContourLocal
import NLS.ZakharovShabat.SourcePrimitivePowerIsospectral

/-! ALL actual physical Hamiltonians at finite-gap sources are determined
by the ACTUAL entire discriminant. Taylor coefficients come from the
proved analytic inversion phase, with their original factorials and powers. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceFiniteGapNLSHamiltonian_eq_of_discriminant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (hg : ψ ∈ sourceFiniteGapLocus hp hp1)
    (heq : ∀ z : ℂ, canonicalDiscriminant hp (periodOnePotential ψ.val) z=
      canonicalDiscriminant hp (periodOnePotential φ.val) z) (k : ℕ) :
    sourceFiniteGapNLSHamiltonian hp hp1 ψ hg k=sourceFiniteGapNLSHamiltonian hp hp1 φ hf k := by
  cases k with
  | zero => rfl
  | succ k =>
    obtain ⟨W,_,_,hC⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
    obtain ⟨C,hcenter⟩ := hC φ
    have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
      rw [hcenter]
      exact mem_ball_self C.discs.sourceRadius_pos
    obtain ⟨R,hR,A,hA,hA0,hcoeff,hval⟩ :=
      exists_sourceFullAbelian_finiteGap_hamiltonian_inversion C φ hφ hf
    obtain ⟨T,_,hT⟩ := exists_exterior_subset_sourceOpenGapComplement_finiteGap hp hp1 φ hf
    obtain ⟨D⟩ := C.charts φ.val hφ
    let a := (sourceFiniteGapPhysicalPair hp hp1 ψ hg).1
    let b := (sourceFiniteGapPhysicalPair hp hp1 ψ hg).2
    have hs := contDiff_sourceFiniteGapPhysicalPair hp hp1 ψ hg
    have hper := periodic_sourceFiniteGapPhysicalPair hp hp1 ψ hg
    have he : ∀ᶠ x : ℝ in atTop,
        2*cosh (-I*(x:ℂ)+A (x:ℂ)⁻¹)=
          classicalDiscriminant (classicalPotentialOfFunctions a b hs.1.continuous hs.2.continuous) x := by
      filter_upwards [eventually_gt_atTop (max R T)] with x hx
      have hxpos := hR.trans ((le_max_left R T).trans_lt hx)
      have hnorm : ‖(x:ℂ)‖=x := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxpos]
      have hF := hval 0 x (by rw [hnorm]; exact (le_max_left R T).trans_lt hx)
      simp only [Int.cast_zero,mul_zero,add_zero] at hF
      rw [← hF,← sourceFiniteGap_discriminant_eq_smooth hp hp1 ψ hg x,heq]
      exact two_cosh_sourceFullAbelianPrimitive_zero φ D x
        (hT (by change T < ‖(x:ℂ)‖; rw [hnorm]; exact (le_max_right R T).trans_lt hx))
    have hψ := iteratedDeriv_nlsHamiltonian_of_discriminant a b hs.1 hs.2 hper.1 hper.2 A hA hA0 he k
    have hc := (hcoeff k).symm.trans hψ
    have hfac : ((k+1).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k+1)
    have hpow : (2:ℂ)^(k+1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have heH := (div_left_inj' hpow).mp (mul_left_cancel₀ hfac hc)
    exact (mul_left_cancel₀ I_ne_zero heH).symm

theorem sourceFiniteGapNLSHamiltonian_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (hg : ψ ∈ sourceFiniteGapLocus hp hp1)
    (h : ψ ∈ sourceIsospectralSet hp φ) (k : ℕ) :
    sourceFiniteGapNLSHamiltonian hp hp1 ψ hg k=sourceFiniteGapNLSHamiltonian hp hp1 φ hf k :=
  sourceFiniteGapNLSHamiltonian_eq_of_discriminant hp hp1 φ ψ hf hg
    (congrFun ((mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ ψ).mp h)) k

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
