import NLS.SequenceSpaces.RealActionPairLifting

/-! # Quantitative real lifting of nonnegative action sequences

Coordinatewise real radial lifts assemble into a lift in the full Birkhoff
sequence space. The square-root bound holds in the sequence norm, uniformly
at zero coordinates and without finite-support assumptions.
-/
noncomputable section
open Set Metric Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- Nearby nonnegative actions admit nearby real Birkhoff lifts. Both
coordinate sequences may change; the estimate is uniform at every real base. -/
theorem exists_nearby_real_quadraticActions (hp : p ≠ ⊤)
    (z : Coeff p × Coeff p) (hz : z ∈ realPairLocus p)
    (b : Coeff q) (hb : b ∈ nonnegativeLocus q) :
    ∃ w : Coeff p × Coeff p, w ∈ realPairLocus p ∧ quadraticActionsExponent w = b ∧
      ‖w-z‖^2 ≤ 2*‖b-quadraticActionsExponent z‖ := by
  classical
  choose u v hu hv he hdu hdv using
    fun n => exists_nearby_real_action_pair (z.1 n) (z.2 n) (b n) (hz.1 n) (hz.2 n) (hb n)
  let e : Coeff q := (2 : ℂ) • (b-quadraticActionsExponent z)
  have hen (n : ℤ) : ‖e n‖ = 2*‖b n-(z.1 n^2+z.2 n^2)/2‖ := by
    change ‖(2 : ℂ)*(b n-quadraticActionsExponent z n)‖ = _
    simp [quadraticActionsExponent_apply]
  have hmu : Memℓp (fun n => u n-z.1 n) p :=
    memℓp_of_norm_sq_le hp e _ (fun n => (hdu n).trans_eq (hen n).symm)
  have hmv : Memℓp (fun n => v n-z.2 n) p :=
    memℓp_of_norm_sq_le hp e _ (fun n => (hdv n).trans_eq (hen n).symm)
  let du : Coeff p := ⟨fun n => u n-z.1 n, hmu⟩
  let dv : Coeff p := ⟨fun n => v n-z.2 n, hmv⟩
  have hud : ‖du‖^2 ≤ 2*‖b-quadraticActionsExponent z‖ := by
    have h := norm_sq_le_of_norm_sq_le hp du e (fun n => (hdu n).trans_eq (hen n).symm)
    simpa [e, norm_smul] using h
  have hvd : ‖dv‖^2 ≤ 2*‖b-quadraticActionsExponent z‖ := by
    have h := norm_sq_le_of_norm_sq_le hp dv e (fun n => (hdv n).trans_eq (hen n).symm)
    simpa [e, norm_smul] using h
  refine ⟨(z.1+du, z.2+dv), ⟨?_, ?_⟩, ?_, ?_⟩
  · intro n
    change (z.1 n+(u n-z.1 n)).im = 0
    simpa only [add_sub_cancel] using hu n
  · intro n
    change (z.2 n+(v n-z.2 n)).im = 0
    simpa only [add_sub_cancel] using hv n
  · ext n
    rw [quadraticActionsExponent_apply]
    change ((z.1 n+(u n-z.1 n))^2+(z.2 n+(v n-z.2 n))^2)/2 = b n
    simpa only [add_sub_cancel] using he n
  · have hw : (z.1+du, z.2+dv)-z = (du,dv) := by ext <;> simp
    rw [hw, Prod.norm_def]
    rcases le_total ‖du‖ ‖dv‖ with h | h
    · rw [max_eq_right h]
      exact hvd
    · rw [max_eq_left h]
      exact hud

/-- The nonnegative part of a radius-squared action ball has real lifts
in the original coordinate ball. -/
theorem nonnegative_ball_subset_real_quadraticActions_image (hp : p ≠ ⊤)
    (z : Coeff p × Coeff p) (hz : z ∈ realPairLocus p) {r : ℝ} (hr : 0 < r) :
    ball (quadraticActionsExponent (q := q) z) (r^2/2) ∩ nonnegativeLocus q ⊆
      quadraticActionsExponent '' (ball z r ∩ realPairLocus p) := by
  intro b hb
  obtain ⟨w, hwr, hw, hd⟩ := exists_nearby_real_quadraticActions hp z hz b hb.2
  refine ⟨w, ⟨?_, hwr⟩, hw⟩
  have hdist : ‖b-quadraticActionsExponent z‖ < r^2/2 := by
    simpa only [mem_ball, dist_eq_norm] using hb.1
  have hnorm : ‖w-z‖ < r := (sq_lt_sq₀ (norm_nonneg _) hr.le).mp (by linarith)
  simpa only [mem_ball, dist_eq_norm] using hnorm

/-- Every open neighborhood of a real Birkhoff point realizes a relative
neighborhood of its action in the nonnegative locus, using real lifts. -/
theorem exists_ball_real_quadraticActions_lifts (hp : p ≠ ⊤)
    (z : Coeff p × Coeff p) (hz : z ∈ realPairLocus p)
    (U : Set (Coeff p × Coeff p)) (hU : IsOpen U) (hzU : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧
      ball (quadraticActionsExponent (q := q) z) r ∩ nonnegativeLocus q ⊆
        quadraticActionsExponent '' (U ∩ realPairLocus p) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hzU
  refine ⟨r^2/2, by positivity, ?_⟩
  exact (nonnegative_ball_subset_real_quadraticActions_image hp z hz hr).trans
    (image_mono (inter_subset_inter_left _ hball))

end NLS.Coeff
