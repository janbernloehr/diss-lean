import NLS.ZakharovShabat.VerticalStrips
import NLS.SequenceSpaces.Truncation
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Strong decay of the free resolvent outside fixed free spectral discs

The punctured-strip estimate gives a common operator bound, and each finite
Fourier sequence decays as the spectral norm tends to infinity. Density then
gives convergence in the absolute-summability norm at every finite exponent.
-/

noncomputable section
open Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem notMem_freeLattice_of_separated {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) : z ∉ freeLattice := by
  rintro ⟨n, rfl⟩
  have h := hz n
  simp only [sub_self, norm_zero] at h
  exact (not_le_of_gt hr) h

/-- A common norm bound on the complement of all fixed-radius free discs. -/
theorem norm_scalarResolventToL1_le_of_separated (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) (a : Coeff p) :
    ‖scalarResolventToL1 hp z hz a‖ ≤ (WeightedCoeff.sobolevEmbeddingConstant p hp / r) * ‖a‖ := by
  obtain ⟨n, hn⟩ := exists_centered_real_part z
  exact (norm_scalarResolventToL1_le hp z hz a).trans
    (mul_le_mul_of_nonneg_right
      (scalarFreeL1Bound_le_verticalStrip hp z hz hr hrπ ⟨hn, hsep n⟩) (norm_nonneg _))

@[simp] theorem scalarResolventToL1_single (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (n : ℤ) (c : ℂ) :
    scalarResolventToL1 hp z hz (lp.single p n c) = lp.single 1 n (c/(z-(Real.pi : ℂ)*n)) := by
  ext m
  by_cases hm : m = n
  · subst m
    simp [scalarResolventToL1_apply, lp.single_apply]
  · simp [scalarResolventToL1_apply, lp.single_apply, hm]

theorem tendsto_norm_free_denominator_atTop {α : Type*} {l : Filter α} (z : α → ℂ)
    (hz : Tendsto (fun i => ‖z i‖) l atTop) (n : ℤ) :
    Tendsto (fun i => ‖z i-(Real.pi : ℂ)*n‖) l atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [hz.eventually_ge_atTop (B+‖(Real.pi : ℂ)*n‖)] with i hi
  have h := norm_sub_norm_le (z i) ((Real.pi : ℂ)*n)
  linarith

/-- Every fixed coordinate tends to zero, in the target sequence norm. -/
theorem tendsto_scalarResolventToL1_single {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (z : α → ℂ) (hz : ∀ i, z i ∉ freeLattice)
    (hescape : Tendsto (fun i => ‖z i‖) l atTop) (n : ℤ) (c : ℂ) :
    Tendsto (fun i => scalarResolventToL1 hp (z i) (hz i) (lp.single p n c)) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [scalarResolventToL1_single, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1), norm_div]
    using (tendsto_norm_free_denominator_atTop z hescape n).const_div_atTop ‖c‖

/-- Outside fixed discs, the scalar free resolvent tends strongly to zero into `ℓ¹`. -/
theorem tendsto_scalarResolventToL1_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (z : α → ℂ) (hz : ∀ i, z i ∉ freeLattice)
    (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*n‖) (a : Coeff p) :
    Tendsto (fun i => scalarResolventToL1 hp (z i) (hz i) a) l (𝓝 0) := by
  let R := fun i => scalarResolventToL1 hp (z i) (hz i)
  have hbound : ∃ C : ℝ, ∀ i (b : Coeff p), ‖R i b‖ ≤ C * ‖b‖ :=
    ⟨WeightedCoeff.sobolevEmbeddingConstant p hp/r, fun i b =>
      norm_scalarResolventToL1_le_of_separated hp (z i) (hz i) hr hrπ (hsep i) b⟩
  have heq : Equicontinuous ((↑) ∘ R) :=
    ((NormedSpace.equicontinuous_TFAE R).out 3 1).mp hbound
  apply (heq a).tendsto_of_mem_closure (f := fun _ => (0 : Coeff 1)) tendsto_const_nhds _
    (Coeff.dense_finiteSupport hp a)
  intro b hb
  obtain ⟨s, hs⟩ := hb
  have hb' : b = Coeff.truncate s b := by
    ext n
    by_cases hn : n ∈ s <;> simp [Coeff.truncate_apply, hn, hs]
  rw [hb', Coeff.truncate]
  simp only [R, Function.comp_apply, map_sum]
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum s (fun n _ => tendsto_scalarResolventToL1_single hp z hz hescape n (b n))

end NLS.ZakharovShabat
