import NLS.ZakharovShabat.SourceFullAbelianHamiltonianReduction
import NLS.ZakharovShabat.SourceFiniteGapNLSHamiltonians

/-! # Lemma 19.2: the convergent physical Hamiltonian Laurent expansion

Every real finite-gap source at a finite exponent greater than one has
an exterior analytic primitive whose convergent Laurent coefficients are
the Appendix H Hamiltonians of its actual smooth Fourier representative.
Smoothness, the discriminant identity, and every coefficient are proved;
none is an additional hypothesis.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- Lemma 19.2, with exterior analyticity, actual physical Hamiltonians,
and a convergent series valid in every complex direction and for every index. -/
theorem exists_sourceFullAbelian_finiteGap_hamiltonian_laurent
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,φ.val))
        {z : ℂ | R < ‖z‖}) ∧
      ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
        HasSum (fun k : ℕ => I*sourceFiniteGapNLSHamiltonian hp hp1 φ hf (k+1)/(2*z)^(k+1))
          (sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)+I*z-I*(Real.pi : ℂ)*n) := by
  have hs := contDiff_sourceFiniteGapPhysicalPair hp hp1 φ hf
  have hper := periodic_sourceFiniteGapPhysicalPair hp hp1 φ hf
  obtain ⟨R,hR,hseries⟩ := exists_sourceFullAbelian_hamiltonian_laurent_of_classical_discriminant
    C φ hφ hf (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 (sourceFiniteGapPhysicalPair hp hp1 φ hf).2
    hs.1 hs.2 hper.1 hper.2 (sourceFiniteGap_discriminant_eq_smooth hp hp1 φ hf)
  obtain ⟨T,_,hT⟩ := exists_exterior_subset_sourceOpenGapComplement_finiteGap hp hp1 φ hf
  obtain ⟨D⟩ := C.charts φ.val hφ
  refine ⟨max R T,hR.trans_le (le_max_left _ _),?_,?_⟩
  · intro n
    exact (sourceFullAbelianPrimitive_spectral_analytic D n).mono
      (fun z hz => hT (show T < ‖z‖ from (le_max_right R T).trans_lt hz))
  · intro n z hz
    exact hseries n z ((le_max_left _ _).trans_lt hz)

/-- One ambient neighborhood supports Lemma 19.2 at every real finite-gap
source. No chart, smooth representative, or coefficient formula is supplied. -/
theorem exists_sourceFullAbelian_finiteGap_hamiltonian_laurent_neighborhood
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1),
        ∃ R : ℝ, 0 < R ∧
          (∀ n : ℤ, AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,φ.val))
            {z : ℂ | R < ‖z‖}) ∧
          ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
            HasSum (fun k : ℕ => I*sourceFiniteGapNLSHamiltonian hp hp1 φ hf (k+1)/(2*z)^(k+1))
              (sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)+I*z-I*(Real.pi : ℂ)*n) := by
  obtain ⟨W,hW,hreal,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro φ hf
  obtain ⟨C,hC⟩ := hfamilies φ
  exact exists_sourceFullAbelian_finiteGap_hamiltonian_laurent C φ
    (by rw [hC]; exact mem_ball_self C.discs.sourceRadius_pos) hf

end NLS.ZakharovShabat
