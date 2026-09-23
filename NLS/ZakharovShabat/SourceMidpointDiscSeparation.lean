import NLS.ZakharovShabat.SourceStandardRootMixedBounds
import NLS.ZakharovShabat.SourceStandardRootCentralBounded
import NLS.ZakharovShabat.SourceIsolatingContourGeometry
import NLS.ZakharovShabat.SourceClusterDiscsLocal
import NLS.ZakharovShabat.SourceTailIsolation
import NLS.ZakharovShabat.SourceSquaredGapReciprocalRows
import NLS.ZakharovShabat.SourceSingleRootAsymptoticFactors

/-!
# Index-scale separation of periodic midpoints from other source discs

The denominator in Lemma 10.8 uses `τₘ-λ`, rather than the standard
root. The finite central block needs a half-margin location for `τₘ`;
the distant blocks use the fixed free quarter-π discs. Combining the
three index ranges gives one lower bound proportional to `|m-n|`.
-/

noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A common constant controls distances from one isolating disc to
the midpoint indexed by any other disc, given half-margin central
localization and the usual tail localization. -/
theorem exists_source_midpoint_index_separation_of_disc_data
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ Real.pi/4)
    (houterL : canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (-(N : ℤ)) ∈ refinedResonantDisk (-(N : ℤ)))
    (houterR : canonicalPeriodicRight hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (N : ℤ) ∈ refinedResonantDisk (N : ℤ))
    (hgap : ∀ i j : ℤ, i.natAbs ≤ N → j.natAbs ≤ N → i < j →
      2*ε ≤
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) j).re -
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) i).re)
    (V : Set (CoeffPair p))
    (hmidCentral : ∀ ψ ∈ V, ∀ j : ℤ, j.natAbs ≤ N →
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) j ∈
          sourceClusterDisc hp hp1 φ (fun _ => ε/2) j)
    (hmidTail : ∀ ψ ∈ V, ∀ j : ℤ, N < j.natAbs →
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) j ∈ refinedResonantDisk j) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ ψ ∈ V, ∀ i j : ℤ, i ≠ j →
        ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
          |((i-j : ℤ) : ℝ)| ≤ C *
            ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) j-z‖ := by
  obtain ⟨R,hR,hcenter⟩ :=
    exists_central_disc_lattice_offset_bound hp hp1 φ N ε
  let B : ℝ := 1+4*R+Real.pi
  let C : ℝ := max 1 (max ((4*(N:ℝ)+2)/ε) B)
  have hC : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := by linarith
  have hCB : B ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hCc : (4*(N:ℝ)+2)/ε ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hscale : 4*(N:ℝ)+2 ≤ C*ε := by
    exact (div_le_iff₀ hε).mp hCc
  refine ⟨C,hC,?_⟩
  intro ψ hψ i j hij z hz
  let w := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) j
  have hdist : dist z w = ‖w-z‖ := by simp only [dist_eq_norm, norm_sub_rev]
  have hd : 0 ≤ |((i-j : ℤ) : ℝ)| := abs_nonneg _
  by_cases hi : i.natAbs ≤ N
  · have hzi : z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i := by
      simpa only [sourceIsolatingDisc, if_pos hi] using hz
    by_cases hj : j.natAbs ≤ N
    · have hw : w ∈ sourceClusterDisc hp hp1 φ (fun _ => ε/2) j :=
        hmidCentral ψ hψ j hj
      have hsep : ε/2 ≤ dist z w := by
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · exact sourceCentralDisc_pointwise_separation hp hp1 φ ε hε
            (hgap i j hi hj hlt) hzi hw
        · exact sourceCentralDisc_pointwise_separation_rev hp hp1 φ ε hε
            (hgap j i hj hi hgt) hzi hw
      have hdmax : |((i-j : ℤ) : ℝ)| ≤ 2*(N:ℝ) := by
        have hii : -(N:ℤ) ≤ i ∧ i ≤ (N:ℤ) := by omega
        have hjj : -(N:ℤ) ≤ j ∧ j ≤ (N:ℤ) := by omega
        have hreal1 : -(2*(N:ℝ)) ≤ ((i-j:ℤ):ℝ) := by exact_mod_cast (show -(2*(N:ℤ)) ≤ i-j by omega)
        have hreal2 : ((i-j:ℤ):ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast (show i-j ≤ 2*(N:ℤ) by omega)
        exact abs_le.mpr ⟨hreal1,hreal2⟩
      rw [← hdist]
      nlinarith [mul_nonneg hC0 (sub_nonneg.mpr hsep)]
    · have hj' : N < j.natAbs := by omega
      have hw : w ∈ refinedResonantDisk j := hmidTail ψ hψ j hj'
      obtain ⟨_,hpoint⟩ := source_central_tail_pointwise_geometry
        hp hp1 φ hφ N ε hε.le hεmax houterL houterR i j hi hj'
      have hsep : Real.pi/4 ≤ dist z w := hpoint z hzi w hw
      have hb : |((i-j : ℤ) : ℝ)| ≤ B*dist z w :=
        central_tail_pointwise_index_lower i j R hR
          (hcenter i hi z hzi) hw hsep
      rw [← hdist]
      exact hb.trans (mul_le_mul_of_nonneg_right hCB (dist_nonneg))
  · have hi' : N < i.natAbs := by omega
    have hzi : z ∈ refinedResonantDisk i := by
      simpa only [sourceIsolatingDisc, if_neg hi] using hz
    by_cases hj : j.natAbs ≤ N
    · have hwSmall : w ∈ sourceClusterDisc hp hp1 φ (fun _ => ε/2) j :=
        hmidCentral ψ hψ j hj
      have hw : w ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) j :=
        sourceClusterDisc_mono_constant_margin hp hp1 φ (ε/2) ε (by linarith) j hwSmall
      obtain ⟨_,hpoint⟩ := source_central_tail_pointwise_geometry
        hp hp1 φ hφ N ε hε.le hεmax houterL houterR j i hj hi'
      have hsep : Real.pi/4 ≤ dist w z := hpoint w hw z hzi
      have hb : |((j-i : ℤ) : ℝ)| ≤ B*dist w z :=
        central_tail_pointwise_index_lower j i R hR
          (hcenter j hj w hw) hzi hsep
      have habs : |((j-i : ℤ) : ℝ)| = |((i-j : ℤ) : ℝ)| := by
        rw [show j-i = -(i-j) by ring, Int.cast_neg, abs_neg]
      rw [habs, dist_comm] at hb
      rw [← hdist]
      exact hb.trans (mul_le_mul_of_nonneg_right hCB (dist_nonneg))
    · have hj' : N < j.natAbs := by omega
      have hw : w ∈ refinedResonantDisk j := hmidTail ψ hψ j hj'
      have ht := (refinedResonantDisk_pointwise_separation hij hzi hw).1
      have hπ : (1:ℝ) ≤ Real.pi/2 := by linarith [Real.pi_gt_three]
      rw [← hdist]
      nlinarith [mul_nonneg (sub_nonneg.mpr hπ) hd,
        mul_nonneg (sub_nonneg.mpr hC) (dist_nonneg : 0 ≤ dist z w)]

/-- Around every real-type source, a single open connected neighborhood
and one isolating-disc family give the midpoint denominator bound needed
for the squared-gap factor in Lemma 10.8. -/
theorem exists_local_source_midpoint_index_separation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C : ℝ, 1 ≤ C ∧
          ∀ ψ ∈ V, ∀ i j : ℤ, i ≠ j →
            ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
              |((i-j : ℤ) : ℝ)| ≤ C *
                ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
                  (periodOnePotential_mem ψ) j-z‖ := by
  obtain ⟨N₀,Ut,hUtopen,hφUt,htail⟩ :=
    exists_uniform_source_tail_isolation hp hp1 φ
  let N := N₀+1
  have hN₀ : N₀ < N := by dsimp [N]; omega
  have hpos : N₀ < (N:ℤ).natAbs := by simpa using hN₀
  have hneg : N₀ < (-(N:ℤ)).natAbs := by simpa using hN₀
  have houterR := (htail φ hφUt (N:ℤ) hpos).2.1
  have houterL := (htail φ hφUt (-(N:ℤ)) hneg).1
  let s : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ)
  obtain ⟨ε,hε,hεmax,hgap⟩ :=
    exists_bounded_positive_margin_for_finite_pairs s
      (fun i j =>
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) j).re -
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) i).re)
      (by
        intro i hi j hj hij
        exact sub_pos.mpr (canonicalPeriodicRight_re_lt_left_of_lt hp hp1
          (periodOnePotential φ) (periodOnePotential_mem φ)
          (isRealType_periodOnePotential φ hφ) hij))
      (by positivity : 0 < Real.pi/4)
  have hgap' : ∀ i j : ℤ, i.natAbs ≤ N → j.natAbs ≤ N → i < j →
      2*ε ≤
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) j).re -
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) i).re := by
    intro i j hi hj hij
    have hiS : i ∈ s := by simp only [s, Finset.mem_Icc]; omega
    have hjS : j ∈ s := by simp only [s, Finset.mem_Icc]; omega
    exact hgap i hiS j hjS hij
  have hevent : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, ∀ j ∈ s,
      sourceSpectralCluster hp hp1 ψ j ⊆
        sourceClusterDisc hp hp1 φ (fun _ => ε/2) j := by
    rw [Finset.eventually_all]
    intro j hj
    exact eventually_sourceSpectralCluster_subset_open hp hp1 φ hφ j _
      Metric.isOpen_ball (sourceSpectralCluster_subset_disc hp hp1 φ hφ
        (fun _ => ε/2) j (by linarith))
  obtain ⟨Uc,hUcsub,hUcopen,hφUc⟩ := _root_.mem_nhds_iff.mp hevent
  let U := Uc ∩ Ut
  have hUopen : IsOpen U := hUcopen.inter hUtopen
  have hφU : φ ∈ U := ⟨hφUc,hφUt⟩
  have hmidCentral : ∀ ψ ∈ U, ∀ j : ℤ, j.natAbs ≤ N →
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) j ∈
          sourceClusterDisc hp hp1 φ (fun _ => ε/2) j := by
    intro ψ hψ j hj
    have hjS : j ∈ s := by simp only [s, Finset.mem_Icc]; omega
    have hc := (hUcsub hψ.1) j hjS
    have hconv : Convex ℝ (sourceClusterDisc hp hp1 φ (fun _ => ε/2) j) := by
      unfold sourceClusterDisc
      exact convex_ball _ _
    exact hconv.segment_subset (hc (Or.inl rfl))
      (hc (Or.inr (Or.inl rfl)))
        (sourcePeriodicMidpoint_mem_segment hp hp1 ψ j)
  have hmidTail : ∀ ψ ∈ U, ∀ j : ℤ, N < j.natAbs →
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) j ∈ refinedResonantDisk j := by
    intro ψ hψ j hj
    have hc := htail ψ hψ.2 j (hN₀.trans hj)
    have hconv : Convex ℝ (refinedResonantDisk j) := by
      unfold refinedResonantDisk
      exact convex_ball _ _
    exact hconv.segment_subset hc.1 hc.2.1
      (sourcePeriodicMidpoint_mem_segment hp hp1 ψ j)
  obtain ⟨C,hC,hsep⟩ := exists_source_midpoint_index_separation_of_disc_data
    hp hp1 φ hφ N ε hε hεmax houterL houterR hgap' U
      hmidCentral hmidTail
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hφU)
  refine ⟨N,ε,hε,hεmax,ball φ r,Metric.isOpen_ball,
    isConnected_ball hr,mem_ball_self hr,C,hC,?_⟩
  intro ψ hψ i j hij z hz
  exact hsep ψ (hrU hψ) i j hij z hz

private theorem squared_ratio_le_reciprocal_row
    (C d b g : ℝ) (hC : 1 ≤ C) (hd : 0 < d)
    (hsep : d ≤ C*b) :
    g^2/(4*b^2) ≤ (C^2/4)*(g^2*d^(-(2:ℝ))) := by
  have hCpos : 0 < C := by linarith
  have hbpos : 0 < b := by nlinarith
  have hd2 : d^2 ≤ C^2*b^2 := by
    calc
      d^2 ≤ (C*b)^2 := pow_le_pow_left₀ hd.le hsep 2
      _ = C^2*b^2 := by ring
  have hbase : (1:ℝ)/b^2 ≤ C^2/d^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hbpos) (sq_pos_of_pos hd)).mpr
    nlinarith [hd2]
  calc
    g^2/(4*b^2) = (g^2/4)*(1/b^2) := by ring
    _ ≤ (g^2/4)*(C^2/d^2) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (C^2/4)*(g^2*d^(-(2:ℝ))) := by
      rw [Real.rpow_neg hd.le]
      field_simp
      norm_num [Real.rpow_natCast]

/-- The actual squared-gap radicand is bounded by its reciprocal-square
row summand on every other isolating disc. -/
theorem sourceSingleRootGapRadicand_le_reciprocal_row
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-z‖)
    (i j : ℤ) (hij : i ≠ j)
    (z : ℂ) (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε i) :
    ‖sourceSingleRootGapRadicand hp hp1 ψ j z‖ ≤
      (C^2/4)*sourceSquaredGapReciprocalTerm hp hp1 ψ i j := by
  have hd : 0 < |((i-j : ℤ) : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast sub_ne_zero.mpr hij
  have hdist := hsep i j hij z hz
  have hterm : sourceSquaredGapReciprocalTerm hp hp1 ψ i j =
      ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖^2 *
        |((i-j : ℤ) : ℝ)|^(-(2:ℝ)) := by
    simp only [sourceSquaredGapReciprocalTerm, if_neg (Ne.symm hij)]
    rw [show j-i = -(i-j) by ring, Int.cast_neg, abs_neg]
  rw [hterm]
  have hnorm : ‖sourceSingleRootGapRadicand hp hp1 ψ j z‖ =
      ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖^2 /
        (4*‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) j-z‖^2) := by
    simp only [sourceSingleRootGapRadicand, norm_div, norm_pow, norm_mul,
      norm_ofNat, ← sourcePeriodicGapDisplacement_apply]
  rw [hnorm]
  exact squared_ratio_le_reciprocal_row C _ _ _ hC hd hdist

/-- Every finite off-diagonal radicand sum is dominated by the full
physical reciprocal-square row. -/
theorem sourceSingleRootGapRadicand_sum_le_reciprocal_row
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-z‖)
    (i : ℤ) (z : ℂ) (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε i)
    (s : Finset ℤ) (hs : ∀ j ∈ s, j ≠ i) :
    ∑ j ∈ s, ‖sourceSingleRootGapRadicand hp hp1 ψ j z‖ ≤
      (C^2/4) * ∑' j : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ i j := by
  have hsum := (exists_sourceSquaredGapPhysicalRows hp hp1 ψ).choose_spec.1 i |>.1
  have hterm_nonneg (j : ℤ) :
      0 ≤ sourceSquaredGapReciprocalTerm hp hp1 ψ i j := by
    unfold sourceSquaredGapReciprocalTerm
    split_ifs
    · rfl
    · positivity
  calc
    ∑ j ∈ s, ‖sourceSingleRootGapRadicand hp hp1 ψ j z‖ ≤
        ∑ j ∈ s, (C^2/4)*sourceSquaredGapReciprocalTerm hp hp1 ψ i j := by
          apply Finset.sum_le_sum
          intro j hj
          exact sourceSingleRootGapRadicand_le_reciprocal_row
            hp hp1 φ ψ N ε C hC hsep i j (Ne.symm (hs j hj)) z hz
    _ = (C^2/4) * ∑ j ∈ s,
        sourceSquaredGapReciprocalTerm hp hp1 ψ i j := by rw [Finset.mul_sum]
    _ ≤ (C^2/4) * ∑' j : ℤ,
        sourceSquaredGapReciprocalTerm hp hp1 ψ i j :=
          mul_le_mul_of_nonneg_left
            (hsum.sum_le_tsum s (fun j _ => hterm_nonneg j)) (by positivity)

/-- A connected neighborhood of each real-type source supports one
uniform radicand bound on every isolating disc and every finite cutoff. -/
theorem exists_local_sourceSingleRootGapRadicand_row_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C : ℝ, 1 ≤ C ∧
          ∀ ψ ∈ V, ∀ i : ℤ,
            ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
              ∀ s : Finset ℤ, (∀ j ∈ s, j ≠ i) →
                ∑ j ∈ s, ‖sourceSingleRootGapRadicand hp hp1 ψ j z‖ ≤
                  (C^2/4) * ∑' j : ℤ,
                    sourceSquaredGapReciprocalTerm hp hp1 ψ i j := by
  obtain ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,hC,hsep⟩ :=
    exists_local_source_midpoint_index_separation hp hp1 φ hφ
  refine ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,hC,?_⟩
  intro ψ hψ i z hz s hs
  exact sourceSingleRootGapRadicand_sum_le_reciprocal_row
    hp hp1 φ ψ N ε C hC (hsep ψ hψ) i z hz s hs

end NLS.ZakharovShabat
