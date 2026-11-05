import NLS.KdV.HillRealSpectrum
import NLS.SequenceSpaces.ConjugateReflection
import NLS.SequenceSpaces.Parity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Every even complex Hill direction is the complexification of two
actual real period-one directions, in the original weighted space. -/
theorem exists_hillRealPeriodOne_complex_decomposition
    (h : WeightedCoeff SpectralWeight.one.toWeight 2)
    (heven : SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0) :
    ∃ a b : WeightedCoeff SpectralWeight.one.toWeight 2,
      SpectralWeight.one.toCoeff a∈Coeff.paritySubspace 0 ∧ IsRealHillPotential (SpectralWeight.one.toCoeff a) ∧
      SpectralWeight.one.toCoeff b∈Coeff.paritySubspace 0 ∧ IsRealHillPotential (SpectralWeight.one.toCoeff b) ∧
      h=a+I • b := by
  let J := WeightedCoeff.conjugateReflection SpectralWeight.one.toWeight (by intro k;rfl) h
  let a := (1/2 : ℂ) • (h+J)
  let b := (-I/2 : ℂ) • (h-J)
  have hJ (k : ℤ) : J.val k=conj (h.val (-k)) := WeightedCoeff.conjugateReflection_apply _ _ h k
  have hJeven : SpectralWeight.one.toCoeff J∈Coeff.paritySubspace 0 := by
    rw [Coeff.mem_paritySubspace]
    intro k hk
    have hk' : (-k)%2≠(0 : ℤ)%2 := by omega
    have hz := (Coeff.mem_paritySubspace 0 _).mp heven (-k) hk'
    simp only [SpectralWeight.toCoeff_apply] at hz ⊢
    rw [hJ,hz,map_zero]
  have haeven : SpectralWeight.one.toCoeff a∈Coeff.paritySubspace 0 := by
    simpa only [a,map_smul,map_add] using (Coeff.paritySubspace (p := 2) 0).smul_mem (1/2 : ℂ)
      ((Coeff.paritySubspace 0).add_mem heven hJeven)
  have hbeven : SpectralWeight.one.toCoeff b∈Coeff.paritySubspace 0 := by
    simpa only [b,map_smul,map_sub] using (Coeff.paritySubspace (p := 2) 0).smul_mem (-I/2 : ℂ)
      ((Coeff.paritySubspace 0).sub_mem heven hJeven)
  have htwo : conj (2 : ℂ)=(2 : ℂ) := by exact Complex.conj_ofReal (2 : ℝ)
  refine ⟨a,b,haeven,?_,hbeven,?_,?_⟩
  · intro k
    simp only [a,SpectralWeight.toCoeff_apply,WeightedCoeff.smul_val,WeightedCoeff.add_val,hJ,
      neg_neg,map_mul,map_add,Complex.conj_conj]
    norm_num [htwo]
    ring
  · intro k
    simp only [b,SpectralWeight.toCoeff_apply,WeightedCoeff.smul_val,WeightedCoeff.sub_val,hJ,
      neg_neg,map_mul,map_sub,Complex.conj_conj]
    norm_num [htwo]
    ring
  · apply Subtype.ext
    funext k
    simp only [a,b,WeightedCoeff.add_val,WeightedCoeff.smul_val,WeightedCoeff.sub_val]
    ring_nf
    simp only [I_sq]
    ring

end NLS.KdV
