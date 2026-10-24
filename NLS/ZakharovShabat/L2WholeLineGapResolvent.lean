import NLS.ZakharovShabat.L2WholeLineFloquetInverse
import NLS.ZakharovShabat.L2WholeLinePencilInverse
import NLS.ZakharovShabat.L2FloquetGapBasis
import NLS.ZakharovShabat.L2WholeLineBandSpectrum

/-! # Real-gap resolvents and the original whole-line Floquet spectrum -/
noncomputable section
set_option autoImplicit false
open Set Matrix Module Complex
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- A physical Floquet basis with logarithmic exponents off the imaginary
axis gives an actual bounded two-sided inverse at a real parameter. -/
theorem mem_wholeLineResolventSet_of_floquet_basis (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im = 0)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ)
    (hμ : ∀ j, μ j ≠ 0) (hM : ∀ j, l2Monodromy u z *ᵥ b j = μ j • b j)
    (h0 : (Complex.log (μ 0)).re ≠ 0) (h1 : (Complex.log (μ 1)).re ≠ 0) :
    z ∈ wholeLineResolventSet u := by
  obtain ⟨C,_,hC⟩ := bounded_l2FloquetPeriodicMatrix_and_inverse u z b μ hμ hM
  exact mem_wholeLineResolventSet_of_bounded_AC_rightInverse u hu z hz
    (wholeLineFloquetInverse u z b μ h0 h1 C hC)
    (wholeLineFloquetInverse_exists_AC_solution u z b μ h0 h1 C hC)

/-- Every real point outside the full closed source bands belongs to the
independently defined resolvent set of the original physical operator. -/
theorem source_gap_mem_wholeLineResolventSet (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (x : ℝ)
    (hx : x ∉ sourceFloquetBandSet (by simp) (by norm_num) φ) :
    (x : ℂ) ∈ wholeLineResolventSet (sourcePhysicalL2 φ) := by
  obtain ⟨μ,ν,b,_,hμpos,hμlt,hνgt,hM0,hM1⟩ :=
    source_gap_exists_stable_unstable_eigenbasis φ hφ x hx
  have hμ : μ ≠ 0 := norm_pos_iff.mp hμpos
  have hν : ν ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hνgt)
  have h0 : (Complex.log μ).re ≠ 0 := by
    simpa only [Complex.log_re] using ne_of_lt (Real.log_neg hμpos hμlt)
  have h1 : (Complex.log ν).re ≠ 0 := by
    simpa only [Complex.log_re] using ne_of_gt (Real.log_pos hνgt)
  apply mem_wholeLineResolventSet_of_floquet_basis _ ((sourcePhysicalL2_realType_iff φ).mpr hφ)
    x (by simp) b ![μ,ν] ?_ ?_ h0 h1
  · intro j
    fin_cases j <;> simpa
  · intro j
    fin_cases j
    · exact hM0
    · exact hM1

/-- The actual whole-line operator spectrum equals the full closed Floquet
band set, including every endpoint and collapsed gap. This concerns the
spectral set; pure absolute continuity requires a separate measure theorem. -/
theorem source_wholeLineSpectrum_eq_floquetBands (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    wholeLineSpectrum (sourcePhysicalL2 φ) =
      Complex.ofReal '' sourceFloquetBandSet (by simp) (by norm_num) φ := by
  apply Set.Subset.antisymm ?_ (sourceFloquetBandSet_subset_wholeLineSpectrum φ hφ)
  intro z hz
  have him : z.im = 0 := wholeLineSpectrum_subset_real _
    ((sourcePhysicalL2_realType_iff φ).mpr hφ) hz
  have hre : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [him]
  refine ⟨z.re,?_,hre⟩
  by_contra hnot
  have hres := source_gap_mem_wholeLineResolventSet φ hφ z.re hnot
  rw [hre] at hres
  exact hz hres

end NLS.ZakharovShabat
