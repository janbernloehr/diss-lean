import NLS.ZakharovShabat.SourceBoundaryRegularCotangent

/-! # Separation relations for all finite source exponents

Within each boundary family, the actual roots commute, the actual
moving Floquet logarithms commute, and their mixed physical bracket
is `-δnm/2`. Hilbert restriction proves these relations below two;
the established source brackets prove them above two. The regular
cotangents ensure absolute convergence of the literal Fourier pairing.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceBoundaryRootRegularCotangent_bivector_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (n m : ℤ) (φ : realTypeSourceLocus p) :
    (sourceBoundaryRootRegularCotangent hp hp1 b n φ).bivector
      (sourceBoundaryRootRegularCotangent hp hp1 b m φ) = 0 := by
  unfold sourceBoundaryRootRegularCotangent
  split
  · exact sourceBracket_boundaryRoots_eq_zero hp hp1 _ b φ.val φ.property n m
  · exact sourceBracket_boundaryRoots_eq_zero (by simp) (by norm_num) (by norm_num) b _
      (realTypeSourceExponentInclusion _ φ).property n m

theorem sourceBoundaryFloquetRegularCotangent_bivector_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (n m : ℤ) (φ : realTypeSourceLocus p) :
    (sourceBoundaryFloquetRegularCotangent hp hp1 b n φ).bivector
      (sourceBoundaryFloquetRegularCotangent hp hp1 b m φ) = 0 := by
  unfold sourceBoundaryFloquetRegularCotangent
  split
  · exact sourceBracket_boundaryFloquetMultipliers_eq_zero hp hp1 _ b φ.val φ.property n m
  · exact sourceBracket_boundaryFloquetMultipliers_eq_zero (by simp) (by norm_num) (by norm_num) b _
      (realTypeSourceExponentInclusion _ φ).property n m

theorem sourceBoundaryRootRegularCotangent_bivector_floquet_diagonal
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (n : ℤ) (φ : realTypeSourceLocus p) :
    (sourceBoundaryRootRegularCotangent hp hp1 b n φ).bivector
      (sourceBoundaryFloquetRegularCotangent hp hp1 b n φ) =
        -sourceBoundaryFloquetMultiplier hp hp1 b n φ.val / 2 := by
  unfold sourceBoundaryRootRegularCotangent sourceBoundaryFloquetRegularCotangent
  split
  · exact sourceBracket_boundaryRoot_floquet_diagonal hp hp1 _ b φ.val φ.property n
  · rename_i h2p
    rw [sourceBoundaryFloquetMultiplier_exponent hp (by simp) hp1 (by norm_num)
      (le_of_not_ge h2p) b n φ.val]
    exact sourceBracket_boundaryRoot_floquet_diagonal (by simp) (by norm_num) (by norm_num) b _
      (realTypeSourceExponentInclusion (le_of_not_ge h2p) φ).property n

theorem sourceBoundaryRootRegularCotangent_bivector_floquet_off_diagonal
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (n m : ℤ) (φ : realTypeSourceLocus p) (hnm : n ≠ m) :
    (sourceBoundaryRootRegularCotangent hp hp1 b n φ).bivector
      (sourceBoundaryFloquetRegularCotangent hp hp1 b m φ) = 0 := by
  unfold sourceBoundaryRootRegularCotangent sourceBoundaryFloquetRegularCotangent
  split
  · exact sourceBracket_boundaryRoot_floquet_off_diagonal hp hp1 _ b φ.val φ.property n m hnm
  · exact sourceBracket_boundaryRoot_floquet_off_diagonal (by simp) (by norm_num) (by norm_num) b _
      (realTypeSourceExponentInclusion _ φ).property n m hnm

theorem sourceBoundaryFloquetLogRegularCotangent_bivector_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (n m : ℤ) (φ : realTypeSourceLocus p) :
    (sourceBoundaryFloquetLogRegularCotangent hp hp1 b n φ).bivector
      (sourceBoundaryFloquetLogRegularCotangent hp hp1 b m φ) = 0 := by
  simp only [sourceBoundaryFloquetLogRegularCotangent,
    RegularSourceCotangent.bivector_smul_left, RegularSourceCotangent.bivector_smul_right,
    sourceBoundaryFloquetRegularCotangent_bivector_eq_zero, mul_zero]

/-- The exact mixed normalization holds for either ordinary boundary
condition, all signed indices, and all finite exponents above one. -/
theorem sourceBoundaryRootRegularCotangent_bivector_floquetLog_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (n m : ℤ) (φ : realTypeSourceLocus p) :
    (sourceBoundaryRootRegularCotangent hp hp1 b n φ).bivector
      (sourceBoundaryFloquetLogRegularCotangent hp hp1 b m φ) =
        if n = m then -(1 : ℂ)/2 else 0 := by
  rw [sourceBoundaryFloquetLogRegularCotangent, RegularSourceCotangent.bivector_smul_right]
  by_cases hnm : n = m
  · subst m
    rw [if_pos rfl, sourceBoundaryRootRegularCotangent_bivector_floquet_diagonal]
    have hne := sourceBoundaryFloquetMultiplier_ne_zero hp hp1 b n φ.val
    field_simp
  · rw [if_neg hnm, sourceBoundaryRootRegularCotangent_bivector_floquet_off_diagonal hp hp1 b n m φ hnm,
      mul_zero]

/-- All three separation relations use the actual root and local
logarithm derivatives on the same real source. -/
theorem sourceBoundaryRegular_separation_relations
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (n m : ℤ) (φ : realTypeSourceLocus p) :
    (sourceBoundaryRootRegularCotangent hp hp1 b n φ).bivector
      (sourceBoundaryRootRegularCotangent hp hp1 b m φ) = 0 ∧
    (sourceBoundaryFloquetLogRegularCotangent hp hp1 b n φ).bivector
      (sourceBoundaryFloquetLogRegularCotangent hp hp1 b m φ) = 0 ∧
    (sourceBoundaryRootRegularCotangent hp hp1 b n φ).bivector
      (sourceBoundaryFloquetLogRegularCotangent hp hp1 b m φ) = if n = m then -(1 : ℂ)/2 else 0 :=
  ⟨sourceBoundaryRootRegularCotangent_bivector_eq_zero hp hp1 b n m φ,
    sourceBoundaryFloquetLogRegularCotangent_bivector_eq_zero hp hp1 b n m φ,
    sourceBoundaryRootRegularCotangent_bivector_floquetLog_eq hp hp1 b n m φ⟩

/-- Absolute convergence of the mixed Fourier expression in the
original actual derivatives, throughout the full exponent range. -/
theorem sourceBoundaryRootFloquetLog_pairing_summable_norm
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (n m : ℤ) (φ : realTypeSourceLocus p) :
    let L := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ.val;
    let M := fderiv ℂ (sourceBoundaryFloquetLogAt hp hp1 b m φ.val) φ.val
    Summable (fun k : ℤ => ‖
      L (CoeffPair.inlCLM (lp.single p k 1)) * M (CoeffPair.inrCLM (lp.single p (-k) 1)) -
      L (CoeffPair.inrCLM (lp.single p k 1)) * M (CoeffPair.inlCLM (lp.single p (-k) 1))‖) := by
  simpa only [sourceBoundaryRootRegularCotangent_toCotangent,
    sourceBoundaryFloquetLogRegularCotangent_toCotangent] using
      (sourceBoundaryRootRegularCotangent hp hp1 b n φ).summable_norm
        (sourceBoundaryFloquetLogRegularCotangent hp hp1 b m φ)

/-- The mixed separation relation as the literal physical Fourier
bracket, retaining the dissertation's frequency reversal and sign. -/
theorem sourceBoundaryRootFloquetLog_fourier_bracket_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (n m : ℤ) (φ : realTypeSourceLocus p) :
    let L := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ.val;
    let M := fderiv ℂ (sourceBoundaryFloquetLogAt hp hp1 b m φ.val) φ.val;
    -I * (∑' k : ℤ,
      (L (CoeffPair.inlCLM (lp.single p k 1)) * M (CoeffPair.inrCLM (lp.single p (-k) 1)) -
      L (CoeffPair.inrCLM (lp.single p k 1)) * M (CoeffPair.inlCLM (lp.single p (-k) 1)))) =
        if n = m then -(1 : ℂ)/2 else 0 := by
  have h := (sourceBoundaryRootRegularCotangent hp hp1 b n φ).bivector_eq_tsum
    (sourceBoundaryFloquetLogRegularCotangent hp hp1 b m φ)
  rw [sourceBoundaryRootRegularCotangent_bivector_floquetLog_eq hp hp1 b n m φ] at h
  simpa only [sourceBoundaryRootRegularCotangent_toCotangent,
    sourceBoundaryFloquetLogRegularCotangent_toCotangent] using h.symm

end NLS.ZakharovShabat
