import NLS.ZakharovShabat.SourceQuotientBlockLowerBound
import NLS.ZakharovShabat.SourceLemma10_8Estimates

/-!
# Failure of the printed local-uniformity scope in Lemma 10.8

At p=4 and q=1, blocks of length k⁴ and amplitude δ/(2k) have l4 norm
δ/2, but every l2 majorant of the quotient error has norm at least
δ*k/(12π). Thus even the three printed sequence classes cannot have
locally bounded norms in the original l4 topology. The final witness uses
the literal disk supremum on a genuine source neighborhood.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceQuotientUniformityCounterexampleFourFact : Fact (1 ≤ (4:ℝ≥0∞)) := ⟨by norm_num⟩

/-- Growing the block as k⁴ while shrinking its amplitude as 1/k fixes the l4 norm. -/
theorem sourceQuotientBlock_scaled_norm (δ : ℝ) (hδ : 0 < δ) (k : ℕ) (hk : 0 < k) :
    ‖sourceQuotientBlock 4 (k^4) ((δ/(2*(k:ℝ)):ℝ):ℂ)‖ = δ/2 := by
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  apply (pow_left_inj₀ (norm_nonneg _) (by positivity : 0 ≤ δ/2) (by decide : (4:ℕ) ≠ 0)).mp
  rw [sourceQuotientBlock_norm_fourth,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  push_cast
  field_simp

/-- Actual quotient errors have no common l2 majorant bound on any l4 ball, even for l1 offsets. -/
theorem exists_small_sourceQuotientBlock_large_error (δ : ℝ) (hδ : 0 < δ) (C : ℝ) :
    ∃ a : Coeff 4, ‖a‖ < δ ∧
      ∃ α : Coeff 1, (∀ m : ℤ, displacedRoots a m-
        canonicalPeriodicMidpoint (p := 4) (by norm_num) (by norm_num)
          (periodOnePotential 0) (periodOnePotential_mem 0) m = α m) ∧
      ∀ B : Coeff 2,
        (∀ n : ℤ, ‖sourceSingleRootQuotientJointProduct (p := 4) (by norm_num) (by norm_num) n
          ((Real.pi:ℂ)*n,(a,0))-1‖ ≤ ‖B n‖) → C < ‖B‖ := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max (1:ℝ) (max (δ/(2*Real.pi)) (12*Real.pi*C/δ)))
  have hk1 : (1:ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hkr : (0:ℝ) < k := by linarith
  have hk0 : 0 < k := by exact_mod_cast hkr
  have hkδ : δ/(2*Real.pi) < k := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hk
  have hkC : 12*Real.pi*C/δ < k := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hk
  let a := δ/(2*(k:ℝ))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have haπ : a ≤ Real.pi := by
    apply (div_le_iff₀ (by positivity : 0 < 2*(k:ℝ))).mpr
    have ht := (div_lt_iff₀ (by positivity : 0 < 2*Real.pi)).mp hkδ
    nlinarith
  let A : Coeff 4 := sourceQuotientBlock 4 (k^4) (a:ℂ)
  refine ⟨A,?_,sourceQuotientBlock 1 (k^4) (a:ℂ),?_,?_⟩
  · rw [show ‖A‖ = δ/2 from sourceQuotientBlock_scaled_norm δ hδ k hk0]
    linarith
  · intro m
    simp [displacedRoots,A,canonicalPeriodicMidpoint,map_zero,
      canonicalPeriodicLeft_zero,canonicalPeriodicRight_zero]
  · intro B hB
    have hb := sourceSingleRootQuotient_block_l2_lower (k^4) (by positivity) a ha haπ B (fun n _ => hB n)
    have he : ((k^4:ℕ):ℝ)*(a/(6*Real.pi))^2 = (δ*(k:ℝ)/(12*Real.pi))^2 := by
      dsimp [a]
      push_cast
      field_simp
      ring
    rw [he] at hb
    have hdn : δ*(k:ℝ)/(12*Real.pi) ≤ ‖B‖ :=
      (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) (by decide : (2:ℕ) ≠ 0)).mp hb
    have hCd : C < δ*(k:ℝ)/(12*Real.pi) := by
      apply (lt_div_iff₀ (by positivity : 0 < 12*Real.pi)).mpr
      have ht := (div_lt_iff₀ hδ).mp hkC
      nlinarith
    exact hCd.trans_le hdn

/-- The witnesses have summable midpoint offsets despite unbounded l2 error norms. -/
theorem exists_small_summable_sourceQuotient_large_error (δ : ℝ) (hδ : 0 < δ) (C : ℝ) :
    ∃ a : Coeff 4, ‖a‖ < δ ∧ Memℓp (fun m => a m) 1 ∧
      ∀ B : Coeff 2,
        (∀ n : ℤ, ‖sourceSingleRootQuotientJointProduct (p := 4) (by norm_num) (by norm_num) n
          ((Real.pi:ℂ)*n,(a,0))-1‖ ≤ ‖B n‖) → C < ‖B‖ := by
  obtain ⟨a,ha,α,hα,hB⟩ := exists_small_sourceQuotientBlock_large_error δ hδ C
  have he : (fun m => a m) = (fun m => α m) := by
    funext m
    simpa [displacedRoots,canonicalPeriodicMidpoint,map_zero,
      canonicalPeriodicLeft_zero,canonicalPeriodicRight_zero] using hα m
  exact ⟨a,ha,he ▸ lp.memℓp α,hB⟩

/-- No neighborhood of the free roots has a common l2 majorant norm bound. -/
theorem not_locally_bounded_sourceQuotient_l2 :
    ¬ ∃ V : Set (Coeff 4), V ∈ 𝓝 0 ∧ ∃ C : ℝ,
      ∀ a ∈ V, Memℓp (fun m => a m) 1 → ∃ B : Coeff 2, ‖B‖ ≤ C ∧
        ∀ n : ℤ, ‖sourceSingleRootQuotientJointProduct (p := 4) (by norm_num) (by norm_num) n
          ((Real.pi:ℂ)*n,(a,0))-1‖ ≤ ‖B n‖ := by
  rintro ⟨V,hV,C,hbound⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨a,ha,hmem,hlarge⟩ := exists_small_summable_sourceQuotient_large_error δ hδ C
  obtain ⟨B,hB,hpoint⟩ := hbound a (hball (by simpa only [mem_ball,dist_zero_right] using ha)) hmem
  exact (not_lt_of_ge hB) (hlarge B hpoint)

/-- The three printed sequence classes would imply the impossible l2 local bound. -/
theorem not_locally_bounded_sourceQuotient_mixed :
    ¬ ∃ V : Set (Coeff 4), V ∈ 𝓝 0 ∧ ∃ L₁ L₂ Lplus : ℝ,
      ∀ a ∈ V, Memℓp (fun m => a m) 1 →
        ∃ A : Coeff 1, ∃ B : Coeff 2, ∃ E : CoeffOnePlus,
          ‖A‖ ≤ L₁ ∧ ‖B‖ ≤ L₂ ∧ ‖CoeffOnePlus.toCoeff 2 (by norm_num) (by norm_num) E‖ ≤ Lplus ∧
          ∀ n : ℤ, ‖sourceSingleRootQuotientJointProduct (p := 4) (by norm_num) (by norm_num) n
            ((Real.pi:ℂ)*n,(a,0))-1‖ ≤ ‖A n+B n+E.1 n‖ := by
  rintro ⟨V,hV,L₁,L₂,Lplus,hb⟩
  apply not_locally_bounded_sourceQuotient_l2
  refine ⟨V,hV,L₁+L₂+Lplus,?_⟩
  intro a ha hmem
  obtain ⟨A,B,E,hA,hB,hE,hpoint⟩ := hb a ha hmem
  let X : Coeff 2 := Coeff.exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) A+B+
    CoeffOnePlus.toCoeff 2 (by norm_num) (by norm_num) E
  refine ⟨X,?_,hpoint⟩
  calc
    ‖X‖ ≤ ‖Coeff.exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) A+B‖+
        ‖CoeffOnePlus.toCoeff 2 (by norm_num) (by norm_num) E‖ := norm_add_le _ _
    _ ≤ (‖A‖+‖B‖)+‖CoeffOnePlus.toCoeff 2 (by norm_num) (by norm_num) E‖ :=
      add_le_add ((norm_add_le _ _).trans (add_le_add (Coeff.norm_exponentInclusion_le _ A) le_rfl)) le_rfl
    _ ≤ L₁+L₂+Lplus := add_le_add (add_le_add hA hB) hE

/-- Refutes locally uniform bounds for the literal supremum on any actual original disk family. -/
theorem not_locally_uniform_sourceQuotientDiscSup_mixed
    {U : Set (Coeff 4 × CoeffPair 4)} {D : ℤ → Set ℂ} {c R H M : ℝ} {N K : ℕ}
    (h : SourceQuotientDiscEstimates (p := 4) (by norm_num) (by norm_num) U D c R H M N K)
    (hU : IsOpen U) (h0 : (0,0) ∈ U) (hcenters : ∀ n : ℤ, (Real.pi:ℂ)*n ∈ D n) :
    ¬ ∃ L₁ L₂ Lplus : ℝ, ∀ a : Coeff 4, (a,0) ∈ U → Memℓp (fun m => a m) 1 →
      ∃ A : Coeff 1, ∃ B : Coeff 2, ∃ E : CoeffOnePlus,
        (∀ n : ℤ, (sourceQuotientDiscSup (p := 4) (by norm_num) (by norm_num) D (a,0) n : ℂ) =
          A n+B n+E.1 n) ∧
        ‖A‖ ≤ L₁ ∧ ‖B‖ ≤ L₂ ∧ ‖CoeffOnePlus.toCoeff 2 (by norm_num) (by norm_num) E‖ ≤ Lplus := by
  rintro ⟨L₁,L₂,Lplus,hb⟩
  apply not_locally_bounded_sourceQuotient_mixed
  refine ⟨(fun a : Coeff 4 => (a,(0:CoeffPair 4))) ⁻¹' U,
    (hU.preimage (continuous_id.prodMk continuous_const)).mem_nhds h0,L₁,L₂,Lplus,?_⟩
  intro a ha hmem
  obtain ⟨A,B,E,he,hA,hB,hE⟩ := hb a ha hmem
  refine ⟨A,B,E,hA,hB,hE,?_⟩
  intro n
  rw [← he n,Complex.norm_real,Real.norm_of_nonneg (h.sup_nonneg (a,0) ha n)]
  exact h.norm_le_sup (a,0) ha n _ (hcenters n)

/-- Every individual summable free-source perturbation still gives an l2 supremum sequence. -/
theorem SourceQuotientDiscEstimates.free_sup_mem_l2_of_summable
    {U : Set (Coeff 4 × CoeffPair 4)} {D : ℤ → Set ℂ} {c R H M : ℝ} {N K : ℕ}
    (h : SourceQuotientDiscEstimates (p := 4) (by norm_num) (by norm_num) U D c R H M N K)
    (a : Coeff 4) (ha : (a,0) ∈ U) (hmem : Memℓp (fun m => a m) 1) :
    Memℓp (fun n : ℤ => (sourceQuotientDiscSup (p := 4) (by norm_num) (by norm_num) D (a,0) n : ℂ)) 2 := by
  let α : Coeff 1 := ⟨fun m => a m,hmem⟩
  obtain ⟨A,B,he,_,_⟩ := h.supDecomposition_one ‖α‖ (norm_nonneg _)
  have hx : ((a,0),α) ∈ sourceQuotientOffsetFamily (p := 4) (by norm_num) (by norm_num) U ‖α‖ 1 := by
    refine ⟨ha,le_rfl,?_⟩
    intro m
    simp [α,displacedRoots,canonicalPeriodicMidpoint,map_zero,
      canonicalPeriodicLeft_zero,canonicalPeriodicRight_zero]
  have hA : Memℓp (fun n => A ((a,0),α) n) 2 := by
    convert lp.memℓp (A ((a,0),α)) using 1
    norm_num
  have heq : (fun n : ℤ => (sourceQuotientDiscSup (p := 4) (by norm_num) (by norm_num) D (a,0) n : ℂ)) =
      (fun n => A ((a,0),α) n)+(fun n => (B ((a,0),α)).1 n) :=
    funext (he ((a,0),α) hx)
  rw [heq]
  exact hA.add (lp.memℓp (CoeffOnePlus.toCoeff 2 (by norm_num) (by norm_num) (B ((a,0),α))))

/-- The obstruction occurs on a genuine Lemma 10.8 disk neighborhood of the free source. -/
theorem exists_sourceQuotientDiscSup_uniformity_counterexample :
    ∃ U : Set (Coeff 4 × CoeffPair 4), IsOpen U ∧ (0,0) ∈ U ∧
      ∃ D : ℤ → Set ℂ, ∃ c R H M : ℝ, ∃ N K : ℕ,
        SourceQuotientDiscEstimates (p := 4) (by norm_num) (by norm_num) U D c R H M N K ∧
        ¬ ∃ L₁ L₂ Lplus : ℝ, ∀ a : Coeff 4, (a,0) ∈ U → Memℓp (fun m => a m) 1 →
          ∃ A : Coeff 1, ∃ B : Coeff 2, ∃ E : CoeffOnePlus,
            (∀ n : ℤ, (sourceQuotientDiscSup (p := 4) (by norm_num) (by norm_num) D (a,0) n : ℂ) =
              A n+B n+E.1 n) ∧
            ‖A‖ ≤ L₁ ∧ ‖B‖ ≤ L₂ ∧ ‖CoeffOnePlus.toCoeff 2 (by norm_num) (by norm_num) E‖ ≤ Lplus := by
  obtain ⟨W,_,_,hr,h⟩ := sourceLemma10_8_estimates (p := 4) (by norm_num) (by norm_num)
  obtain ⟨V,_,_,h0V,_,D,c,hD,ha⟩ := h.neighborhoods 0 (hr (by simp [realTypeSourceLocus]))
  obtain ⟨U,ho,h0,_,R,H,M,N,K,hE⟩ := ha 0
  have hcenters (n : ℤ) : (Real.pi:ℂ)*n ∈ D n := by
    apply hD.gap 0 h0V n
    simp [sourcePeriodicSegment,map_zero,canonicalPeriodicLeft_zero,canonicalPeriodicRight_zero,segment_same]
  exact ⟨U,ho,h0,D,c,R,H,M,N,K,hE,not_locally_uniform_sourceQuotientDiscSup_mixed hE ho h0 hcenters⟩

end NLS.ZakharovShabat
