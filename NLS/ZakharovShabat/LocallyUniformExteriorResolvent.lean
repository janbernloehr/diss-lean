import NLS.ZakharovShabat.FreeResolventExteriorLimit
import NLS.ZakharovShabat.UniformThresholds

/-! # Locally uniform exterior decay in the displacement parameter

The scalar resolvent tends strongly to zero at spectral infinity and has
a common operator bound outside fixed free discs. A small input ball
therefore shares one exterior threshold for any prescribed tolerance.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One exterior threshold controls a whole neighborhood of a fixed displacement. -/
theorem exists_local_threshold_scalarResolvent_small (hp : p ≠ ⊤) (a : Coeff p)
    {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, 0 < R ∧
      ∀ b : Coeff p, ‖b-a‖ < η → ∀ z : ℂ, R ≤ ‖z‖ →
      ∀ hsep : ∀ n : ℤ, r ≤ ‖z-(Real.pi:ℂ)*n‖,
        ‖scalarResolventToL1 hp z (notMem_freeLattice_of_separated hr hsep) b‖ < ε := by
  let E := {z : ℂ // ∀ n : ℤ, r ≤ ‖z-(Real.pi:ℂ)*n‖}
  have hlim := tendsto_scalarResolventToL1_of_separated hp (fun z : E => z.val)
    (fun z => notMem_freeLattice_of_separated hr z.property) tendsto_comap hr hrπ
    (fun z => z.property) a
  have he : ∀ᶠ z : E in comap (fun z : E => ‖z.val‖) atTop,
      ‖scalarResolventToL1 hp z.val (notMem_freeLattice_of_separated hr z.property) a‖ < ε/2 := by
    have h := hlim.norm.eventually (gt_mem_nhds
      (show ‖(0:Coeff 1)‖ < ε/2 by simpa only [norm_zero] using half_pos hε))
    simpa only [norm_zero] using h
  obtain ⟨R,hR⟩ := exists_threshold_of_eventually_comap_atTop (fun z : E => ‖z.val‖) he
  let C := WeightedCoeff.sobolevEmbeddingConstant p hp/r
  have hC : 0 ≤ C := div_nonneg (WeightedCoeff.sobolevEmbeddingConstant_nonneg p hp) hr.le
  have hC1 : 0 < C+1 := by linarith
  let η := (ε/2)/(C+1)
  have hη : 0 < η := div_pos (half_pos hε) hC1
  refine ⟨η,hη,max R 1,lt_of_lt_of_le (by norm_num) (le_max_right _ _),?_⟩
  intro b hb z hz hsep
  let T := scalarResolventToL1 hp z (notMem_freeLattice_of_separated hr hsep)
  have hbase : ‖T a‖ < ε/2 := hR ⟨z,hsep⟩ ((le_max_left _ _).trans hz)
  have hdiff : ‖T (b-a)‖ ≤ C*‖b-a‖ :=
    norm_scalarResolventToL1_le_of_separated hp z _ hr hrπ hsep (b-a)
  have hsmall : C*‖b-a‖ < ε/2 := by
    calc
      _ ≤ (C+1)*‖b-a‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (C+1)*η := mul_lt_mul_of_pos_left hb hC1
      _ = ε/2 := by dsimp [η]; field_simp
  have heq : T b = T a+T (b-a) := by
    rw [← map_add, show a+(b-a)=b from by abel]
  rw [heq]
  exact (norm_add_le _ _).trans_lt (by linarith)

end NLS.ZakharovShabat
