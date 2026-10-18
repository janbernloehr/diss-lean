import NLS.ZakharovShabat.SourceWeightedTerminalComplexBound

/-! # Weighted complex spectral terms

The two terminal signs reconstruct the actual Dirichlet-minus-midpoint displacement and sine numerator. Both have bounded native weighted realizations.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The two terminal signs reconstruct the actual Dirichlet-to-midpoint displacement. -/
theorem sourceDirichletMidpointDisplacement_eq_terminals (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) :
    sourceDirichletMidpointDisplacement hp hp1 ψ n =
      -(1/4:ℂ)*(sourceGapWeightedEtaTerminalCoordinate hp hp1 n 1 ψ+
        sourceGapWeightedEtaTerminalCoordinate hp hp1 n (-1) ψ) := by
  simp only [sourceDirichletMidpointDisplacement_apply,sourceStandardRootMidpoint,
    sourceGapWeightedEtaTerminalCoordinate]
  ring

/-- The two terminal signs reconstruct the actual sine numerator. -/
theorem sourceDirichletEtaSineNumerator_eq_terminals (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) :
    sourceDirichletEtaSineNumerator hp hp1 n ψ =
      (I/4)*(sourceGapWeightedEtaTerminalCoordinate hp hp1 n 1 ψ-
        sourceGapWeightedEtaTerminalCoordinate hp hp1 n (-1) ψ) := by
  simp only [sourceGapWeightedEtaTerminalCoordinate]
  ring_nf
  simp [I_sq]

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
include D

/-- Both actual terminal spectral terms admit bounded native weighted realizations on one complex neighborhood. -/
theorem exists_local_normalizedWeightedSpectralTerms_bound
    (w : SpectralWeight) (φ : realTypeSourceLocus p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧
      (∀ ψ ∈ U, normalizedWeightedSource w ψ ∈ W) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ U, ∃ A B : Coeff p,
        (∀ n, A n = (w (2*n):ℂ)*sourceDirichletMidpointDisplacement hp hp1 (normalizedWeightedSource w ψ) n) ∧
        (∀ n, B n = (w (2*n):ℂ)*sourceDirichletEtaSineNumerator hp hp1 n (normalizedWeightedSource w ψ)) ∧
        ‖A‖ ≤ M ∧ ‖B‖ ≤ M := by
  obtain ⟨U,hU,hφ,hUW,M₀,hM₀,h⟩ := D.exists_local_normalizedWeightedTerminal_bound w φ
  refine ⟨U,hU,hφ,hUW,2*M₀,by positivity,?_⟩
  intro ψ hψ
  let u := Coeff.ofFunctionOrZero p (fun n => (w (2*n):ℂ)*
    sourceGapWeightedEtaTerminalCoordinate hp hp1 n 1 (normalizedWeightedSource w ψ))
  let v := Coeff.ofFunctionOrZero p (fun n => (w (2*n):ℂ)*
    sourceGapWeightedEtaTerminalCoordinate hp hp1 n (-1) (normalizedWeightedSource w ψ))
  have hu := h ψ hψ 1 (Or.inl rfl)
  have hv := h ψ hψ (-1) (Or.inr rfl)
  have huc n : u n = (w (2*n):ℂ)*sourceGapWeightedEtaTerminalCoordinate hp hp1 n 1
      (normalizedWeightedSource w ψ) := Coeff.ofFunctionOrZero_apply_of_mem p _ hu.1 n
  have hvc n : v n = (w (2*n):ℂ)*sourceGapWeightedEtaTerminalCoordinate hp hp1 n (-1)
      (normalizedWeightedSource w ψ) := Coeff.ofFunctionOrZero_apply_of_mem p _ hv.1 n
  have hun : ‖u‖ ≤ M₀ := hu.2
  have hvn : ‖v‖ ≤ M₀ := hv.2
  have hsmall (z : ℂ) (hz : ‖z‖ ≤ 1) (a : Coeff p) (ha : ‖a‖ ≤ 2*M₀) :
      ‖z • a‖ ≤ 2*M₀ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right hz (norm_nonneg a)).trans (by simpa only [one_mul] using ha)
  refine ⟨(-(1/4):ℂ) • (u+v),(I/4) • (u-v),?_,?_,?_,?_⟩
  · intro n
    rw [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.coeFn_add,Pi.add_apply,huc,hvc,
      sourceDirichletMidpointDisplacement_eq_terminals]
    ring
  · intro n
    rw [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.coeFn_sub,Pi.sub_apply,huc,hvc,
      sourceDirichletEtaSineNumerator_eq_terminals]
    ring
  · apply hsmall _ (by norm_num) _
    exact (norm_add_le u v).trans (by linarith)
  · apply hsmall _ (by norm_num [norm_div]) _
    exact (norm_sub_le u v).trans (by linarith)

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
