import NLS.ZakharovShabat.SourcePsiOriginalZetaAsymptotic

/-!
# Auxiliary product identities and lattice spacing in Section 12

These are the literal single- and double-omitted product relations in
(2.24)–(2.25), with the cross-multiplied identity valid at the filled root.
The direct ratio estimate preceding (2.26) has error constant `A + B`;
its local version chooses one bound before all signed indices.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source relation to its negative single auxiliary product, away from the filled root. -/
theorem sourcePsiZeta_eq_negative_single_quotient
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : Coeff p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m) (hzn : z ≠ displacedRoots a n) :
    sourcePsiZeta hp hp1 n m a ψ z =
      (1/Complex.I) * (1/(displacedRoots a n-z)) *
        (-sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ))) := by
  rw [← sourcePsiGapRegularFactor_eq_zeta hp hp1 n m hmn a ψ z hz hzn]
  simp only [sourcePsiGapRegularFactor,one_div,Complex.inv_I]
  ring

/-- Cross multiplication removes the unused-root denominator, including at its zero. -/
theorem sourcePsiZeta_mul_filled_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : Coeff p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m) :
    (displacedRoots a n-z)*sourcePsiZeta hp hp1 n m a ψ z =
      Complex.I*sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)) := by
  rw [sourceSingleRootQuotient_eq_doubleOmitted hp hp1 n m hmn a ψ z hz]
  unfold sourcePsiZeta
  ring

/-- The direct lattice-spacing expansion has constant A+B and needs no root separation. -/
theorem sourcePsi_forwardIndexRatio_error_bound
    (n m : ℤ) (hmn : m ≠ n) (ξ z : ℂ) (A B : ℝ)
    (hz : ‖z-(Real.pi:ℂ)*m‖ ≤ A) (hξ : ‖ξ-(Real.pi:ℂ)*n‖ ≤ B) :
    ‖(ξ-z)/((n-m:ℤ):ℂ)-(Real.pi:ℂ)‖ ≤ (A+B)/‖((n-m:ℤ):ℂ)‖ := by
  have hnm : ((n-m:ℤ):ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hmn.symm
  have he : (ξ-z)/((n-m:ℤ):ℂ)-(Real.pi:ℂ) =
      (ξ-(Real.pi:ℂ)*n-(z-(Real.pi:ℂ)*m))/((n-m:ℤ):ℂ) := by
    field_simp [hnm]
    push_cast
    ring
  rw [he,norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  exact (norm_sub_le _ _).trans (by simpa only [add_comm] using add_le_add hξ hz)

/-- The printed direct expansion is locally uniform in every full lp root input and all indices. -/
theorem SourceIsolatingNeighborhoods.forwardIndexRatio_locally_uniform
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (a₀ : Coeff p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ ball a₀ 1, ∀ n m : ℤ, m ≠ n → ∀ z ∈ D m,
      ‖(displacedRoots a n-z)/((n-m:ℤ):ℂ)-(Real.pi:ℂ)‖ ≤ C/‖((n-m:ℤ):ℂ)‖ := by
  obtain ⟨A,hA,hbound⟩ := hD.exists_uniform_lattice_bound
  refine ⟨A+(‖a₀‖+1),by positivity,?_⟩
  intro a ha n m hmn z hz
  have hd : ‖a-a₀‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using ha
  have hnorm : ‖a‖ ≤ ‖a₀‖+1 := (norm_le_norm_sub_add a a₀).trans (by linarith)
  apply sourcePsi_forwardIndexRatio_error_bound n m hmn _ _ A (‖a₀‖+1) (hbound m z hz)
  simp only [displacedRoots,add_sub_cancel_left]
  exact (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' a n).trans hnorm

end NLS.ZakharovShabat
