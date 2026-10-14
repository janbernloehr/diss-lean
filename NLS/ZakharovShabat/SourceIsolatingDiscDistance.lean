import NLS.ZakharovShabat.SpectralSetDistance
import NLS.ZakharovShabat.SourceIsolatingContourGeometry
import NLS.ZakharovShabat.SourceStandardRootMixedUpper

/-!
# Quantitative distance between the actual isolating discs

Halving the central enlargement of an existing disjoint family leaves a
positive margin even when the original boundaries touch. A uniform bound
on lattice offsets then gives the literal two-sided set-distance estimate
of (2.7), including central, mixed, and tail pairs.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every positive-margin isolating disc is nonempty. -/
theorem sourceIsolatingDisc_nonempty (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) (hε : 0 < ε) (n : ℤ) :
    (sourceIsolatingDisc hp hp1 φ N ε n).Nonempty := by
  rw [sourceIsolatingDisc_eq_ball]
  exact ⟨_,mem_ball_self (sourceIsolatingRadius_pos hp hp1 φ N ε hε n)⟩

/-- All points in the isolating discs have a common bound on their lattice offsets. -/
theorem exists_source_isolating_lattice_offset_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (N : ℕ) (ε : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ n : ℤ, ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε n,
      ‖z-(Real.pi : ℂ)*n‖ ≤ R := by
  obtain ⟨R,hR,h⟩ := exists_central_disc_lattice_offset_bound hp hp1 φ N ε
  refine ⟨max R (Real.pi/4),hR.trans (le_max_left _ _),?_⟩
  intro n z hz
  by_cases hn : n.natAbs ≤ N
  · simp only [sourceIsolatingDisc,if_pos hn] at hz
    exact (h n hn z hz).trans (le_max_left _ _)
  · simp only [sourceIsolatingDisc,if_neg hn,refinedResonantDisk,mem_ball,dist_eq_norm] at hz
    exact hz.le.trans (le_max_right _ _)

/-- Shrinking only the central margins gives a positive uniform separation. -/
theorem source_shrunk_isolating_pointwise_separation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (N : ℕ)
    (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ Real.pi/4)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (i j : ℤ) (hij : i ≠ j)
    (z w : ℂ) (hz : z ∈ sourceIsolatingDisc hp hp1 φ N (ε/2) i)
    (hw : w ∈ sourceIsolatingDisc hp hp1 φ N (ε/2) j) :
    ε/2 ≤ dist z w := by
  let d : ℤ → ℝ := fun n => if n.natAbs ≤ N then ε/2 else 0
  have hr (n : ℤ) : sourceIsolatingRadius hp hp1 φ N (ε/2) n =
      sourceIsolatingRadius hp hp1 φ N ε n-d n := by
    by_cases hn : n.natAbs ≤ N
    · simp only [sourceIsolatingRadius,d,if_pos hn]
      ring
    · simp only [sourceIsolatingRadius,d,if_neg hn,sub_zero]
  have hd := hdisjoint i j hij
  rw [sourceIsolatingDisc_eq_ball,sourceIsolatingDisc_eq_ball] at hd
  rw [sourceIsolatingDisc_eq_ball,hr i] at hz
  rw [sourceIsolatingDisc_eq_ball,hr j] at hw
  have hsep := shrunk_disjoint_balls_pointwise_separation _ _ z w _ _ (d i) (d j)
    (sourceIsolatingRadius_pos hp hp1 φ N ε hε i)
    (sourceIsolatingRadius_pos hp hp1 φ N ε hε j) hd hz hw
  by_cases hi : i.natAbs ≤ N
  · have hdi : d i = ε/2 := if_pos hi
    have hdj : 0 ≤ d j := by dsimp [d]; split_ifs <;> positivity
    rw [hdi] at hsep
    linarith
  · by_cases hj : j.natAbs ≤ N
    · simpa only [d,if_neg hi,if_pos hj,zero_add] using hsep
    · have hzi : z ∈ refinedResonantDisk i := by
        simpa only [sourceIsolatingCenter,sourceIsolatingRadius,d,if_neg hi,
          sub_zero,refinedResonantDisk] using hz
      have hwj : w ∈ refinedResonantDisk j := by
        simpa only [sourceIsolatingCenter,sourceIsolatingRadius,d,if_neg hj,
          sub_zero,refinedResonantDisk] using hw
      have hfree := (refinedResonantDisk_pointwise_separation hij hzi hwj).1
      have hk : (1 : ℝ) ≤ |((i-j : ℤ) : ℝ)| := by
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hij)
      nlinarith [Real.pi_pos]

/-- One constant bounds every pointwise distance in the smaller family at index scale. -/
theorem exists_source_shrunk_isolating_pointwise_comparison
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (N : ℕ)
    (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ Real.pi/4)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j)) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ i j : ℤ, i ≠ j →
      ∀ z ∈ sourceIsolatingDisc hp hp1 φ N (ε/2) i,
      ∀ w ∈ sourceIsolatingDisc hp hp1 φ N (ε/2) j,
        c⁻¹*|((i-j : ℤ) : ℝ)| ≤ dist z w ∧ dist z w ≤ c*|((i-j : ℤ) : ℝ)| := by
  obtain ⟨R,hR,hoffset⟩ := exists_source_isolating_lattice_offset_bound hp hp1 φ N (ε/2)
  obtain ⟨c,hc,hbound⟩ := exists_index_comparison_constant R (ε/2) hR (by positivity)
  refine ⟨c,hc,?_⟩
  intro i j hij z hz w hw
  have hk : (1 : ℝ) ≤ |((i-j : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hij)
  have hsep := source_shrunk_isolating_pointwise_separation hp hp1 φ N ε hε hεmax
    hdisjoint i j hij z w hz hw
  have hz' : dist z ((Real.pi : ℂ)*i) ≤ R := by
    simpa only [dist_eq_norm] using hoffset i z hz
  have hw' : dist w ((Real.pi : ℂ)*j) ≤ R := by
    simpa only [dist_eq_norm] using hoffset j w hw
  have hcenter : dist ((Real.pi : ℂ)*i) ((Real.pi : ℂ)*j) =
      Real.pi*|((i-j : ℤ) : ℝ)| := by
    simpa only [dist_eq_norm] using norm_free_center_sub i j
  have hlow := dist_triangle4 ((Real.pi : ℂ)*i) z w ((Real.pi : ℂ)*j)
  have hupp := dist_triangle4 z ((Real.pi : ℂ)*i) ((Real.pi : ℂ)*j) w
  rw [dist_comm ((Real.pi : ℂ)*i) z,hcenter] at hlow
  rw [dist_comm ((Real.pi : ℂ)*j) w,hcenter] at hupp
  exact hbound _ _ hk hsep (by linarith) (by linarith)

/-- The same pointwise comparison implies the literal infimum-distance bounds. -/
theorem spectralSetDistance_comparison_of_pointwise
    (D : ℤ → Set ℂ) (hne : ∀ n, (D n).Nonempty) (c : ℝ)
    (h : ∀ i j : ℤ, i ≠ j → ∀ z ∈ D i, ∀ w ∈ D j,
      c⁻¹*|((i-j : ℤ) : ℝ)| ≤ dist z w ∧ dist z w ≤ c*|((i-j : ℤ) : ℝ)|)
    (i j : ℤ) (hij : i ≠ j) :
    c⁻¹*|((i-j : ℤ) : ℝ)| ≤ spectralSetDistance (D i) (D j) ∧
      spectralSetDistance (D i) (D j) ≤ c*|((i-j : ℤ) : ℝ)| := by
  constructor
  · exact le_spectralSetDistance (hne i) (hne j) (fun z hz w hw => (h i j hij z hz w hw).1)
  · obtain ⟨z,hz⟩ := hne i
    obtain ⟨w,hw⟩ := hne j
    exact (spectralSetDistance_le_dist hz hw).trans (h i j hij z hz w hw).2

end NLS.ZakharovShabat
