import NLS.ZakharovShabat.AppendixDSineProducts
import NLS.ZakharovShabat.LocallyUniformExteriorResolvent
import NLS.ComplexAnalysis.SmallAbsoluteProducts

/-! # The locally uniform exterior sine asymptotic in Lemma D.5

The source exterior is the complement of all open quarter-pi free discs.
The product error is bounded by the exponential of the absolute relative
displacement sum. Locally uniform resolvent decay makes this error small
on a whole displacement neighborhood with one spectral threshold.
-/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exterior Pi used in D.5, including the boundaries of the free discs. -/
def appendixDExterior : Set ℂ := {z | ∀ n : ℤ, Real.pi/4 ≤ ‖z-(Real.pi:ℂ)*n‖}

/-- This is exactly the complement of the union of the source's open discs. -/
theorem appendixDExterior_eq_compl_iUnion_ball : appendixDExterior =
    (⋃ n : ℤ, ball ((Real.pi:ℂ)*n) (Real.pi/4))ᶜ := by
  ext z
  simp [appendixDExterior, mem_ball, dist_eq_norm]

/-- The sine-normalized source product is its absolute-convergent relative product. -/
theorem appendixDProduct_div_sin_eq_tprod (hp : p ≠ ⊤) (a : Coeff p)
    (z : ℂ) (hz : z ∉ freeLattice) :
    appendixDProduct (z,a)/Complex.sin z =
      ∏' n : ℤ, (1 + -(a n/(z-(Real.pi:ℂ)*n))) := by
  have he : appendixDProduct (z,a)/Complex.sin z =
      entireSingleSpectralProduct (displacedRoots a) z/(-2*Complex.sin z) := by
    simp only [appendixDProduct, jointSingleSpectralProduct, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, entireSingleSpectralProduct_div_free hp _ (memℓp_displacedRoots a) z hz]
  congr 1
  funext n
  rw [spectralRelativeFactor_eq _ z hz]
  simp [displacedRoots]

/-- D.2 bounds the sine quotient by the scalar resolvent's absolute-summability norm. -/
theorem norm_appendixDProduct_div_sin_sub_one_le (hp : p ≠ ⊤) (a : Coeff p)
    (z : ℂ) (hz : z ∉ freeLattice) :
    ‖appendixDProduct (z,a)/Complex.sin z-1‖ ≤
      Real.exp ‖scalarResolventToL1 hp z hz a‖-1 := by
  let u : ℤ → ℂ := fun n => -(a n/(z-(Real.pi:ℂ)*n))
  have hu : Summable (fun n => ‖u n‖) := by
    simpa [u, displacedRoots] using
      summable_norm_spectralRelativeDisplacement hp (displacedRoots a) (memℓp_displacedRoots a) z hz
  have hs : (∑' n, ‖u n‖) = ‖scalarResolventToL1 hp z hz a‖ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : (0:ℝ) < (1:ℝ≥0∞).toReal)]
    simp only [ENNReal.toReal_one, one_div, inv_one, Real.rpow_one,
      scalarResolventToL1_apply, u, norm_neg]
  rw [appendixDProduct_div_sin_eq_tprod hp a z hz]
  simpa only [hs] using NLS.ComplexAnalysis.norm_tprod_one_add_sub_one_le_exp u hu

/-- D.5's exterior error is uniformly small for every displacement in one neighborhood. -/
theorem exists_local_appendixDProduct_div_sin_bound (hp : p ≠ ⊤) (a : Coeff p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, 0 < R ∧
      ∀ b : Coeff p, ‖b-a‖ < η → ∀ z ∈ appendixDExterior, R ≤ ‖z‖ →
        ‖appendixDProduct (z,b)/Complex.sin z-1‖ < ε := by
  let δ := Real.log (1+ε)
  have hδ : 0 < δ := Real.log_pos (by linarith)
  have hr : 0 < Real.pi/4 := by positivity
  obtain ⟨η,hη,R,hR,hbound⟩ := exists_local_threshold_scalarResolvent_small hp a hδ hr le_rfl
  refine ⟨η,hη,R,hR,fun b hb z hz hRz => ?_⟩
  have hzfree := notMem_freeLattice_of_separated hr hz
  calc
    _ ≤ Real.exp ‖scalarResolventToL1 hp z hzfree b‖-1 :=
      norm_appendixDProduct_div_sin_sub_one_le hp b z hzfree
    _ < Real.exp δ-1 := sub_lt_sub_right (Real.exp_lt_exp.mpr (hbound b hb z hRz hz)) _
    _ = ε := by dsimp [δ]; rw [Real.exp_log (by linarith)]; ring

/-- The literal supremum formulation of D.5. The same positive radius threshold
works for all displacements in a neighborhood of the specified sequence. -/
theorem exists_local_appendixDProduct_div_sin_sup_lt (hp : p ≠ ⊤) (a : Coeff p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, 0 < R ∧ ∀ b : Coeff p, ‖b-a‖ < η →
      sSup ((fun z : ℂ => ‖appendixDProduct (z,b)/Complex.sin z-1‖) ''
        (appendixDExterior ∩ {z | R < ‖z‖})) < ε := by
  obtain ⟨η,hη,R,hR,hbound⟩ := exists_local_appendixDProduct_div_sin_bound hp a (half_pos hε)
  refine ⟨η,hη,R,hR,fun b hb => ?_⟩
  let S := (fun z : ℂ => ‖appendixDProduct (z,b)/Complex.sin z-1‖) ''
    (appendixDExterior ∩ {z | R < ‖z‖})
  change sSup S < ε
  by_cases hS : S.Nonempty
  · apply lt_of_le_of_lt (csSup_le hS ?_) (half_lt_self hε)
    rintro x ⟨z,hz,rfl⟩
    exact (hbound b hb z hz.1 hz.2.le).le
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, Real.sSup_empty]
    exact hε

end NLS.ZakharovShabat
