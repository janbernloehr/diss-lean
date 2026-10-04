import NLS.ZakharovShabat.SourceFullAbelianHamiltonianLaurent

/-! # The analytic inversion phase with all physical Taylor coefficients

This records the normalized analytic remainder and the Hamiltonian Taylor
jet together, so nonlinear Laurent expansions can reuse the actual phase.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- One analytic inversion phase represents every normalization index and
has the complete physical Hamiltonian Taylor jet. -/
theorem exists_sourceFullAbelian_finiteGap_hamiltonian_inversion
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧ ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧ A 0 = 0 ∧
      (∀ k : ℕ, iteratedDeriv (k+1) A 0 =
        ((k+1).factorial : ℂ)*(I*sourceFiniteGapNLSHamiltonian hp hp1 φ hf (k+1)/2^(k+1))) ∧
      ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
        sourceFullAbelianPrimitive hp hp1 W n (z,φ.val) = -I*z+I*(Real.pi : ℂ)*n+A z⁻¹ := by
  obtain ⟨R,hR,r,hr,_,A,hA,hA0,hval⟩ :=
    exists_sourceFullAbelian_finiteGap_inversion_remainder_all_indices C φ hφ hf
  obtain ⟨T,_,hT⟩ := exists_exterior_subset_sourceOpenGapComplement_finiteGap hp hp1 φ hf
  obtain ⟨D⟩ := C.charts φ.val hφ
  let a := (sourceFiniteGapPhysicalPair hp hp1 φ hf).1
  let b := (sourceFiniteGapPhysicalPair hp hp1 φ hf).2
  have hs := contDiff_sourceFiniteGapPhysicalPair hp hp1 φ hf
  have hper := periodic_sourceFiniteGapPhysicalPair hp hp1 φ hf
  have he : ∀ᶠ x : ℝ in atTop,
      2*cosh (-I*(x : ℂ)+A (x : ℂ)⁻¹) =
        classicalDiscriminant (classicalPotentialOfFunctions a b hs.1.continuous hs.2.continuous) x := by
    filter_upwards [eventually_gt_atTop (max R T)] with x hx
    have hxpos : 0 < x := hR.trans ((le_max_left R T).trans_lt hx)
    have hnorm : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxpos]
    have hF := hval 0 x (by rw [hnorm]; exact (le_max_left R T).trans_lt hx)
    simp only [Int.cast_zero,mul_zero,add_zero] at hF
    rw [← hF,← sourceFiniteGap_discriminant_eq_smooth hp hp1 φ hf x]
    exact two_cosh_sourceFullAbelianPrimitive_zero φ D x
      (hT (by change T < ‖(x : ℂ)‖; rw [hnorm]; exact (le_max_right R T).trans_lt hx))
  refine ⟨R,hR,A,hA 0 (mem_ball_self hr),hA0,?_,hval⟩
  intro k
  exact iteratedDeriv_nlsHamiltonian_of_discriminant a b hs.1 hs.2 hper.1 hper.2 A
    (hA 0 (mem_ball_self hr)) hA0 he k

end NLS.ZakharovShabat
