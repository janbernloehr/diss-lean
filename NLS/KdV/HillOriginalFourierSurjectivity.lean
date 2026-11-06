import NLS.KdV.HillOriginalFourierDerivative

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate ENNReal
namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- Every complex sequence basis vector is attained by an actual original
real mean-zero Fourier direction. -/
theorem hillOriginalMeanZeroDerivativeAtZero_fourierDirection (n : ℕ+) (z : ℂ) :
    hillOriginalMeanZeroDerivativeAtZero (hillOriginalFourierDirection n z) =
      lp.single 2 ((n : ℕ)-1) ((Real.sqrt 2 : ℂ)*z) := by
  ext k
  rw [hillOriginalMeanZeroDerivativeAtZero_fourier h0q h0r,hillOriginalFourierDirection_apply]
  have hneg : -(2*(n : ℤ)) ≠ 2*((k+1 : ℕ) : ℤ) := by have := n.pos; omega
  have he : 2*(n : ℤ) = 2*((k+1 : ℕ) : ℤ) ↔ k = (n : ℕ)-1 := by have := n.pos; omega
  simp only [if_neg hneg,add_zero,he,lp.single_apply,Pi.single_apply]
  split_ifs <;> simp only [mul_zero]

include h0q h0r in
/-- The ACTUAL original zero-source spectral derivative is onto. The proof
uses original Fourier directions and convergence of finite-coordinate sums
inside its already proved closed range. -/
theorem surjective_hillOriginalMeanZeroDerivativeAtZero :
    Function.Surjective hillOriginalMeanZeroDerivativeAtZero := by
  let R := hillOriginalMeanZeroDerivativeAtZero.toLinearMap.range
  have hsingle (k : ℕ) (z : ℂ) : lp.single 2 k z ∈ R := by
    let n : ℕ+ := ⟨k+1,by omega⟩
    refine ⟨hillOriginalFourierDirection n (z/(Real.sqrt 2 : ℂ)),?_⟩
    change hillOriginalMeanZeroDerivativeAtZero _ = _
    rw [hillOriginalMeanZeroDerivativeAtZero_fourierDirection h0q h0r]
    have hs : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hk : (n : ℕ)-1 = k := by change (k+1)-1 = k; omega
    rw [hk,mul_div_cancel₀ _ hs]
  intro z
  have hc : IsClosed (R : Set (lp (fun _ : ℕ => ℂ) 2)) :=
    isClosed_range_hillOriginalMeanZeroDerivativeAtZero
  have hz : z ∈ R := hc.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z)
    (Eventually.of_forall (fun s : Finset ℕ => R.sum_mem (fun k _ => hsingle k (z k))))
  exact hz

include h0q h0r in
/-- The actual original Fourier derivative, promoted to an isometric
equivalence only after its surjectivity has been proved. -/
def hillOriginalMeanZeroDerivativeAtZeroEquiv :
    hillRealMeanZeroSourceSubmodule ≃ₗᵢ[ℝ] lp (fun _ : ℕ => ℂ) 2 :=
  LinearIsometryEquiv.ofSurjective hillOriginalMeanZeroDerivativeAtZeroIsometry
    (surjective_hillOriginalMeanZeroDerivativeAtZero h0q h0r)

include h0q h0r in
@[simp] theorem hillOriginalMeanZeroDerivativeAtZeroEquiv_apply (h : hillRealMeanZeroSourceSubmodule) :
    hillOriginalMeanZeroDerivativeAtZeroEquiv h0q h0r h = hillOriginalMeanZeroDerivativeAtZero h := rfl

end NLS.KdV
