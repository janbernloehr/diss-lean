import NLS.ZakharovShabat.SourcePsiOriginalNormLimit
import NLS.ZakharovShabat.SourcePsiOriginalUniformityCounterexample

/-!
# The printed source-only Jacobian estimate with independently varying roots

At the fixed free source, arbitrarily small real placed-root changes alter
some actual original Jacobian. A bound by source displacement alone is
therefore impossible when roots vary independently. The result concerns
both full extensions and actual deleted blocks, and constructs an existing
original isolating family. It does not address a prescribed root graph
whose variation is controlled by the source. The proved joint complex
root/source estimate is the replacement used in the inverse-bound proof.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceLemma12_4Data.original_free_spike_limit_ne_zeroRoot
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (h0W : (0:CoeffPair p) ∈ W) (h0V : (0:CoeffPair p) ∈ V)
    (k : ℤ) (z : ℂ) (hz : z ≠ 0) (hsmall : ‖z‖ < Real.pi/4)
    (hk : D k = refinedResonantDisk k) (hm : D (k+1) = refinedResonantDisk (k+1)) :
    sourcePsiOriginalLimitOperator hp hp1 (lp.single p k z) (0:CoeffPair p) ≠
      sourcePsiOriginalLimitOperator hp hp1 0 (0:CoeffPair p) := by
  intro heq
  have ha := hD.original_free_spike_placement h0V k hk z hsmall
  have ha0 : (0:Coeff p) ∈ sourcePsiOriginalRootPlacement D := by
    simpa using hD.original_free_spike_placement h0V k hk (0:ℂ) (by simp [Real.pi_pos])
  have hez := H.original_free_spike_diagonal_difference hD h0W h0V k z ha
    (Real.pi/4) (by positivity) (by linarith [Real.pi_pos]) hm
  have he0 := H.original_free_spike_diagonal_difference hD h0W h0V k 0 (by simpa using ha0)
    (Real.pi/4) (by positivity) (by linarith [Real.pi_pos]) hm
  have hfull : sourcePsiOriginalFullRootJacobian hp hp1 k (lp.single p k z) (0:CoeffPair p) =
      sourcePsiOriginalFullRootJacobian hp hp1 k 0 (0:CoeffPair p) := by
    simp only [sourcePsiOriginalFullRootJacobian,Coeff.deleteCoordinateTo_single_same,map_zero]
  simp only [lp.single_zero,mul_zero,zero_div] at he0
  rw [hfull,heq,he0] at hez
  exact (div_ne_zero (mul_ne_zero (by norm_num) hz) (by exact_mod_cast Real.pi_ne_zero)) hez.symm

theorem SourceLemma12_4Data.original_free_root_variation_on_every_ball
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (h0W : (0:CoeffPair p) ∈ W) (h0V : (0:CoeffPair p) ∈ V)
    (r : ℝ) (hr : 0 < r) :
    ∃ a : Coeff p, a ∈ ball 0 r ∧ a ∈ sourcePsiOriginalRootPlacement D ∧
      (∀ j : ℤ, (a j).im = 0) ∧ ∃ n : ℤ,
        sourcePsiOriginalFullRootJacobian hp hp1 n a (0:CoeffPair p) ≠
          sourcePsiOriginalFullRootJacobian hp hp1 n 0 (0:CoeffPair p) := by
  let : NeBot (Filter.comap Int.natAbs atTop) :=
    (inferInstance : NeBot (atTop : Filter ℕ)).comap_of_surj Int.natAbs_surjective
  let δ := min (r/2) (Real.pi/8)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
  have hδπ : δ < Real.pi/4 := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  obtain ⟨K,hK⟩ := hD.tail
  let k : ℤ := (K+1:ℕ)
  have hk : K < k.natAbs := by simp only [k,Int.natAbs_natCast]; omega
  have hm : K < (k+1).natAbs := by
    have hk0 : 0 ≤ k := by dsimp [k]; positivity
    omega
  have hz : (δ:ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hsmall : ‖(δ:ℂ)‖ < Real.pi/4 := by simpa only [Complex.norm_real,Real.norm_of_nonneg hδ.le] using hδπ
  let a : Coeff p := lp.single p k (δ:ℂ)
  have ha := hD.original_free_spike_placement h0V k (hK k hk) (δ:ℂ) hsmall
  have haR : ∀ j : ℤ, (a j).im = 0 := by
    intro j
    by_cases hj : j = k
    · subst j; simp [a]
    · simp [a,Pi.single_eq_of_ne hj]
  refine ⟨a,?_,ha,haR,?_⟩
  · simpa only [a,mem_ball,dist_zero_right,lp.norm_single (zero_lt_one.trans hp1),
      Complex.norm_real,Real.norm_of_nonneg hδ.le] using hδr
  · by_contra h
    push Not at h
    have ha0 : (0:Coeff p) ∈ sourcePsiOriginalRootPlacement D := by
      simpa using hD.original_free_spike_placement h0V k (hK k hk) (0:ℂ) (by simp [Real.pi_pos])
    have hlim := H.originalFullRootJacobian_tendsto hW hD hV 0 h0W h0V (by simp) a ha haR
    have hlim0 := H.originalFullRootJacobian_tendsto hW hD hV 0 h0W h0V (by simp) 0 ha0 (by simp)
    have hfun : (fun n : ℤ => sourcePsiOriginalFullRootJacobian hp hp1 n a (0:CoeffPair p)) =
        fun n : ℤ => sourcePsiOriginalFullRootJacobian hp hp1 n 0 (0:CoeffPair p) := funext h
    rw [hfun] at hlim
    exact H.original_free_spike_limit_ne_zeroRoot hD h0W h0V k (δ:ℂ) hz hsmall
      (hK k hk) (hK (k+1) hm) (tendsto_nhds_unique hlim hlim0)

/-- A source-only estimate with independently varying roots fails even at
one fixed source, however small the neighborhood and whatever the constant. -/
theorem SourceLemma12_4Data.original_free_no_sourceOnly_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (h0W : (0:CoeffPair p) ∈ W) (h0V : (0:CoeffPair p) ∈ V) :
    ¬ ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ a : Coeff p, a ∈ ball 0 r →
      a ∈ sourcePsiOriginalRootPlacement D → (∀ j : ℤ, (a j).im = 0) → ∀ n : ℤ,
      ‖sourcePsiOriginalFullRootJacobian hp hp1 n a (0:CoeffPair p)-
        sourcePsiOriginalFullRootJacobian hp hp1 n 0 (0:CoeffPair p)‖ ≤ C*‖(0:CoeffPair p)-0‖ := by
  rintro ⟨r,hr,C,hb⟩
  obtain ⟨a,har,haD,haR,n,hne⟩ := H.original_free_root_variation_on_every_ball hW hD hV h0W h0V r hr
  have h := hb a har haD haR n
  simp only [sub_self,norm_zero,mul_zero] at h
  exact hne (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _))))


/-- The same obstruction concerns the actual deleted Jacobian blocks. -/
theorem SourceLemma12_4Data.original_free_no_sourceOnly_deleted_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (h0W : (0:CoeffPair p) ∈ W) (h0V : (0:CoeffPair p) ∈ V) :
    ¬ ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ a : Coeff p, a ∈ ball 0 r →
      a ∈ sourcePsiOriginalRootPlacement D → (∀ j : ℤ, (a j).im = 0) → ∀ n : ℤ,
      ‖sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) (0:CoeffPair p)-
        sourcePsiOriginalRootJacobian hp hp1 n 0 (0:CoeffPair p)‖ ≤ C*‖(0:CoeffPair p)-0‖ := by
  rintro ⟨r,hr,C,hb⟩
  obtain ⟨a,har,haD,haR,n,hne⟩ := H.original_free_root_variation_on_every_ball hW hD hV h0W h0V r hr
  have h := hb a har haD haR n
  simp only [sub_self,norm_zero,mul_zero] at h
  have heq : sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) (0:CoeffPair p) =
      sourcePsiOriginalRootJacobian hp hp1 n 0 (0:CoeffPair p) := by
    apply sub_eq_zero.mp
    exact (norm_eq_zero (a := sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) (0:CoeffPair p)-
      sourcePsiOriginalRootJacobian hp hp1 n 0 (0:CoeffPair p))).mp (le_antisymm h
        (norm_nonneg (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) (0:CoeffPair p)-
          sourcePsiOriginalRootJacobian hp hp1 n 0 (0:CoeffPair p))))
  apply hne
  simpa only [sourcePsiOriginalFullRootJacobian,map_zero] using congrArg (Coeff.deletedJacobianExtension n) heq

/-- An existing original isolating family witnesses failure of the printed
source-only estimate for every finite exponent greater than one. -/
theorem sourceLemma12_10_no_sourceOnly_deleted_bound (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), ∃ D : ℤ → Set ℂ, ∃ c : ℝ,
      IsOpen V ∧ (0:CoeffPair p) ∈ V ∧ SourceIsolatingNeighborhoods hp hp1 V D c ∧
      ¬ ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ a : Coeff p, a ∈ ball 0 r →
        a ∈ sourcePsiOriginalRootPlacement D → (∀ j : ℤ, (a j).im = 0) → ∀ n : ℤ,
        ‖sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) (0:CoeffPair p)-
          sourcePsiOriginalRootJacobian hp hp1 n 0 (0:CoeffPair p)‖ ≤ C*‖(0:CoeffPair p)-0‖ := by
  obtain ⟨W,hW,_,hR,H⟩ := sourceLemma12_4 hp hp1
  have h0W : (0:CoeffPair p) ∈ W := hR (by simp [realTypeSourceLocus])
  obtain ⟨V,hV,_,h0V,_,D,c,hD⟩ := H.previous.quotients.neighborhoods 0 h0W
  exact ⟨V,D,c,hV,h0V,hD.toSourceIsolatingNeighborhoods,
    H.original_free_no_sourceOnly_deleted_bound hW hD.toSourceIsolatingNeighborhoods hV h0W h0V⟩

end NLS.ZakharovShabat
