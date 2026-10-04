import NLS.ZakharovShabat.NLSHamiltonianPrimitiveCoefficients
import NLS.ZakharovShabat.SourceFullAbelianFiniteGapLaurent

/-! # Reducing finite-gap Hamiltonian coefficients to a smooth realization

The actual source primitive satisfies the discriminant identity, including
filled collapsed gaps. Its established normalized inversion remainder thus
has Hamiltonian coefficients whenever a smooth periodic classical potential
realizes the same discriminant.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The zero-index full primitive recovers the discriminant on the entire
open-gap complement, including the filled collapsed endpoints. -/
theorem two_cosh_sourceFullAbelianPrimitive_zero (φ : realTypeSourceSubmodule p)
    (D : SourceAbelianSpectralChart hp hp1 W φ.val) :
    ∀ z ∈ sourceOpenGapComplement hp hp1 φ.val,
      2*cosh (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val)) =
        canonicalDiscriminant hp (periodOnePotential φ.val) z := by
  apply continuous_eqOn_of_dense_on_open (sourceCanonicalRootDomain hp hp1 φ.val) _
    (dense_sourceCanonicalRootDomain_complex hp hp1 φ.val)
    (isOpen_sourceOpenGapComplement_of_realType hp hp1 φ.val φ.property) _ _
    (continuousOn_const.mul (continuous_cosh.comp_continuousOn
      (sourceFullAbelianPrimitive_spectral_analytic D 0).continuousOn))
    ((analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem φ.val)).continuousOn.mono (subset_univ _))
  intro z hz
  change 2*cosh (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val)) = _
  have he := sourceAbelianPrimitive_exp hp hp1 φ.val φ.property z hz.1
  have hmul := sourceFloquetMultiplier_mul_companion hp hp1 φ.val z hz.2
  have hinv : (sourceFloquetMultiplier hp hp1 φ.val z)⁻¹ =
      (canonicalDiscriminant hp (periodOnePotential φ.val) z-sourceCanonicalRoot hp hp1 φ.val z)/2 :=
    inv_eq_of_mul_eq_one_right hmul
  rw [sourceFullAbelianPrimitive_eq_real φ D 0 z hz.1]
  simp only [Int.cast_zero,mul_zero,add_zero]
  rw [two_cosh,exp_neg,he,hinv,sourceFloquetMultiplier]
  ring

/-- The actual finite-gap primitive has the Hamiltonian Laurent series as
soon as a smooth periodic realization of its discriminant is available.
No primitive asymptotic or Hamiltonian coefficient is assumed. -/
theorem exists_sourceFullAbelian_hamiltonian_laurent_of_classical_discriminant
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (htrace : ∀ z : ℂ, canonicalDiscriminant hp (periodOnePotential φ.val) z =
      classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z) :
    ∃ R : ℝ, 0 < R ∧ ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
      HasSum (fun k : ℕ => I*classicalNLSHamiltonian a b (k+1)/(2*z)^(k+1))
        (sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)+I*z-I*(Real.pi : ℂ)*n) := by
  obtain ⟨R,hR,r,hr,_,A,hA,hA0,hval⟩ :=
    exists_sourceFullAbelian_finiteGap_inversion_remainder_all_indices C φ hφ hf
  obtain ⟨T,_,hT⟩ := exists_exterior_subset_sourceOpenGapComplement_finiteGap hp hp1 φ hf
  obtain ⟨D⟩ := C.charts φ.val hφ
  have he : ∀ᶠ x : ℝ in atTop,
      2*cosh (-I*(x : ℂ)+A (x : ℂ)⁻¹) =
        classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) x := by
    filter_upwards [eventually_gt_atTop (max R T)] with x hx
    have hxpos : 0 < x := hR.trans ((le_max_left R T).trans_lt hx)
    have hnorm : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxpos]
    have hF := hval 0 x (by rw [hnorm]; exact (le_max_left R T).trans_lt hx)
    simp only [Int.cast_zero,mul_zero,add_zero] at hF
    rw [← hF,← htrace]
    exact two_cosh_sourceFullAbelianPrimitive_zero φ D x
      (hT (by change T < ‖(x : ℂ)‖; rw [hnorm]; exact (le_max_right R T).trans_lt hx))
  obtain ⟨S,hS,hs⟩ := exists_nlsHamiltonian_laurent_of_discriminant a b ha hb hpa hpb A
    (hA 0 (mem_ball_self hr)) hA0 he
  refine ⟨max R S,hR.trans_le (le_max_left _ _),?_⟩
  intro n z hz
  have hv : sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)+I*z-I*(Real.pi : ℂ)*n = A z⁻¹ := by
    rw [hval n z ((le_max_left _ _).trans_lt hz)]
    ring
  rw [hv]
  exact hs z ((le_max_right _ _).trans_lt hz)

end NLS.ZakharovShabat
