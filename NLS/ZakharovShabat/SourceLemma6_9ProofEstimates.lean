import NLS.ZakharovShabat.SourceLemma6_9ProofRoots
import NLS.ZakharovShabat.SourceLemma6_9PositiveCorrected
import NLS.ZakharovShabat.SourceResonantSup

/-! # Literal root estimates and corrected sums in Lemma 6.9

The exterior separation uses the exact infimum on the closed strip outside the
open refined disk. Root estimates retain both leading Fourier coefficients.
One common neighborhood carries the literal Rouche proof, the canonical
period-two pair, and corrected signed and positive-index displacement sums.
-/
noncomputable section
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The strip outside the open refined disk attains its least center distance, pi/4. -/
theorem resonantProof_exterior_isLeast (n : ℤ) :
    IsLeast ((fun z : ℂ => ‖z-(Real.pi : ℂ)*n‖) ''
      (resonantStrip n \ refinedResonantDisk n)) (Real.pi/4) := by
  let z : ℂ := (Real.pi : ℂ)*n+(Real.pi/4 : ℝ)
  have hd : ‖z-(Real.pi : ℂ)*n‖ = Real.pi/4 := by
    simp only [z,add_sub_cancel_left,Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ Real.pi/4)]
  refine ⟨⟨z,⟨?_,?_⟩,hd⟩,?_⟩
  · apply closedBall_subset_resonantStrip n (r := Real.pi/4) (by linarith [Real.pi_pos])
    apply Metric.mem_closedBall.mpr
    rw [dist_eq_norm,hd]
  · change ¬ dist z ((Real.pi : ℂ)*n) < Real.pi/4
    rw [dist_eq_norm,hd]
    exact lt_irrefl _
  · rintro _ ⟨u,hu,rfl⟩
    have h := hu.2
    change ¬ dist u ((Real.pi : ℂ)*n) < Real.pi/4 at h
    simpa only [dist_eq_norm] using le_of_not_gt h

/-- The exact exterior infimum used in the source Rouche argument. -/
theorem resonantProof_exterior_inf (n : ℤ) :
    sInf ((fun z : ℂ => ‖z-(Real.pi : ℂ)*n‖) ''
      (resonantStrip n \ refinedResonantDisk n)) = Real.pi/4 :=
  (resonantProof_exterior_isLeast n).csInf_eq

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual full-strip suprema are strictly below the exact exterior infimum. -/
theorem SourceResonantStripControl.sup_separation {hp : p ≠ ⊤} {φ : CoeffPair p} {n : ℤ}
    (hc : SourceResonantStripControl hp φ n) :
    sourceResonantDiagonalSup hp φ n + Real.sqrt (sourceResonantBProductSup hp φ n) <
      sInf ((fun z : ℂ => ‖z-(Real.pi : ℂ)*n‖) ''
        (resonantStrip n \ refinedResonantDisk n)) := by
  have ha : sourceResonantDiagonalSup hp φ n ≤ Real.pi/32 := by
    apply csSup_le
    · exact ⟨_,⟨_,center_mem_resonantStrip n,rfl⟩⟩
    · rintro _ ⟨z,hz,rfl⟩
      exact hc.diagonal z hz
  have hb : Real.sqrt (sourceResonantBProductSup hp φ n) ≤ Real.pi/16 := by
    have h := Real.sqrt_le_sqrt hc.product_bounds.2.2.1
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ Real.pi/16)] using h
  rw [resonantProof_exterior_inf]
  linarith [Real.pi_pos]

/-- Both leading signed Fourier coefficients lie in the full tail at 2|n|, including its boundary. -/
theorem sourceResonantLeading_le_fullTail (φ : CoeffPair p) (n : ℤ) :
    ‖φ.fst (-(2*n))‖ ≤ ‖sourceFourierTail (2*n.natAbs) φ‖ ∧
      ‖φ.snd (2*n)‖ ≤ ‖sourceFourierTail (2*n.natAbs) φ‖ := by
  have hm := lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    (sourceFourierTail (2*n.natAbs) φ).fst (-(2*n))
  have hp' := lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    (sourceFourierTail (2*n.natAbs) φ).snd (2*n)
  norm_num only [sourceFourierTail_fst,sourceFourierTail_snd,Int.natAbs_neg,Int.natAbs_mul] at hm hp'
  simp only [le_refl,if_true] at hm hp'
  exact ⟨hm.trans (WithLp.norm_fst_le _ _),hp'.trans (WithLp.norm_snd_le _ _)⟩

/-- Each original off-diagonal coefficient is bounded by the retained leading tail plus its remainder. -/
theorem sourceResonant_fullCoefficient_le_tail_add (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) :
    ‖sourceResonantBMinusFunction hp φ n z‖ ≤ ‖sourceFourierTail (2*n.natAbs) φ‖ +
      ‖sourceResonantBMinusFunction hp φ n z-φ.fst (-(2*n))‖ ∧
    ‖sourceResonantBPlusFunction hp φ n z‖ ≤ ‖sourceFourierTail (2*n.natAbs) φ‖ +
      ‖sourceResonantBPlusFunction hp φ n z-φ.snd (2*n)‖ := by
  obtain ⟨hm,hp'⟩ := sourceResonantLeading_le_fullTail φ n
  constructor
  · exact (norm_le_norm_sub_add _ _).trans (by linarith)
  · exact (norm_le_norm_sub_add _ _).trans (by linarith)

/-- The pointwise root-displacement bound retains both leading coefficients and both remainders. -/
theorem sourceResonantRoot_displacement_rpow_le (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : sourceResonantDeterminantFunction hp φ n z = 0) :
    ‖z-(Real.pi : ℂ)*n‖^p.toReal ≤
      (2 : ℝ)^(p.toReal-1) * (‖sourceResonantAFunction hp φ n z‖^p.toReal +
        (2 : ℝ)^(p.toReal-1)/2 *
          (‖φ.snd (2*n)‖^p.toReal + ‖φ.fst (-(2*n))‖^p.toReal +
           ‖sourceResonantBPlusFunction hp φ n z-φ.snd (2*n)‖^p.toReal +
           ‖sourceResonantBMinusFunction hp φ n z-φ.fst (-(2*n))‖^p.toReal)) := by
  simpa only [unitWeightedPairEquiv_fst,unitWeightedPairEquiv_snd,
    sourceResonantAFunction,sourceResonantBPlusFunction,sourceResonantBMinusFunction,
    sourceCorrectionEntryFunction,weightedResonantAExtension,weightedResonantBPlusExtension,
    weightedResonantBMinusExtension] using
    resonantRoot_displacement_rpow_le hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz

/-- The actual determinant is strictly closer to the centered square on the refined boundary. -/
theorem SourceResonantStripControl.quadratic_comparison {hp : p ≠ ⊤} {φ : CoeffPair p} {n : ℤ}
    (hc : SourceResonantStripControl hp φ n) (z : ℂ)
    (hz : z ∈ Metric.sphere ((Real.pi : ℂ)*n) (Real.pi/4)) :
    ‖sourceResonantDeterminantFunction hp φ n z-(z-(Real.pi : ℂ)*n)^2‖ <
      ‖(z-(Real.pi : ℂ)*n)^2‖ := by
  have hs := closedBall_subset_resonantStrip n
    (r := Real.pi/4) (by linarith [Real.pi_pos]) (Metric.sphere_subset_closedBall hz)
  exact norm_resonant_quadratic_error_lt _ _ _ _
    (by simpa only [dist_eq_norm] using Metric.mem_sphere.mp hz)
    (hc.diagonal z hs) (hc.positive z hs) (hc.negative z hs)

/-- The literal intermediate gap inequality follows from Cauchy and the full-strip product supremum. -/
theorem SourceResonantStripControl.gap_linear {hp : p ≠ ⊤} {φ : CoeffPair p} {n : ℤ}
    (hc : SourceResonantStripControl hp φ n) (x y : ℂ)
    (hx : x ∈ resonantStrip n) (hy : y ∈ resonantStrip n)
    (hx0 : sourceResonantDeterminantFunction hp φ n x = 0)
    (hy0 : sourceResonantDeterminantFunction hp φ n y = 0) :
    ‖x-y‖ ≤ (1/8 : ℝ)*‖x-y‖ + 2*Real.sqrt (sourceResonantBProductSup hp φ n) := by
  let a := sourceResonantAFunction hp φ n
  let c : ℂ := (Real.pi : ℂ)*n
  have ha : AnalyticOnNhd ℂ a (resonantStrip n) := by
    intro z hz
    exact (analyticAt_sourceCorrectionEntryFunction hp φ n z hz
      ((hc.small z hz).trans_lt (by norm_num)) 0 0).comp
      (analyticAt_const.prod analyticAt_id)
  have hproof := hc.proof_roots
  have hxD : x ∈ refinedResonantDisk n := by_contra (fun h => hproof.no_exterior_roots x hx h hx0)
  have hyD : y ∈ refinedResonantDisk n := by_contra (fun h => hproof.no_exterior_roots y hy h hy0)
  have hdiag := norm_diagonal_sub_le_on_refined_disk n a ha hc.diagonal x y hxD hyD
  have hres (z : ℂ) (hz : z ∈ resonantStrip n)
      (hz0 : sourceResonantDeterminantFunction hp φ n z = 0) :
      ‖z-c-a z‖ ≤ Real.sqrt (sourceResonantBProductSup hp φ n) := by
    rw [hproof.residual_norm z hz0]
    exact Real.sqrt_le_sqrt (hc.product_bounds.2.2.2 z hz)
  calc
    _ = ‖(a x-a y)+((x-c-a x)-(y-c-a y))‖ := congrArg norm (by ring)
    _ ≤ ‖a x-a y‖+(‖x-c-a x‖+‖y-c-a y‖) :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    _ ≤ (1/8 : ℝ)*‖x-y‖ +
        (Real.sqrt (sourceResonantBProductSup hp φ n)+Real.sqrt (sourceResonantBProductSup hp φ n)) :=
      add_le_add hdiag (add_le_add (hres x hx hx0) (hres y hy hy0))
    _ = _ := by ring

/-- One common neighborhood supports the root proof, canonical pair identification and corrected displacement sums, including the literally duplicated positive label. -/
theorem sourceLemma6_9_proof (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∃ ξ η : ℤ → ℂ,
        (∀ n : ℤ, N₀ ≤ n.natAbs →
          SourceLemma69Proof hp ψ n ∧ SourceResonantRootPair hp ψ n (ξ n) (η n) ∧
          ({ξ n,η n} : Multiset ℂ) =
            {sourcePeriodTwoCanonicalLeft hp hp1 ψ n,sourcePeriodTwoCanonicalRight hp hp1 ψ n} ∧
          ‖sourcePeriodTwoCanonicalGap hp hp1 ψ n‖ = ‖ξ n-η n‖) ∧
        ∀ N : ℕ, N₀ ≤ N →
          (Summable (rootDisplacementPowerTail p N ξ η) ∧
            (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ sourcePeriodTwoDisplacementBudget ψ N) ∧
          (Summable (sourcePositiveDisplacementPowerTail p N ξ η) ∧
            (∑' n : ℤ, sourcePositiveDisplacementPowerTail p N ξ η n) ≤ sourcePeriodTwoDisplacementBudget ψ N) ∧
          (Summable (sourcePositiveDisplacementPowerTail p N ξ ξ) ∧
            (∑' n : ℤ, sourcePositiveDisplacementPowerTail p N ξ ξ n) ≤ 2*sourcePeriodTwoDisplacementBudget ψ N) := by
  obtain ⟨N₁,hN₁,V,hoV,hcV,hφV,h0V,hcan⟩ := sourceLemma6_9_proof_canonical hp hp1 φ
  obtain ⟨N₂,_,W,hoW,hcW,hφW,h0W,_,ht⟩ := sourceLemma6_9 hp hp1 φ
  refine ⟨max N₁ N₂,by omega,V ∩ W,hoV.inter hoW,hcV.inter hcW,
    ⟨hφV,hφW⟩,⟨h0V,h0W⟩,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hpair⟩ := hcan ψ hψ.1
  obtain ⟨α,β,hpair',hsum⟩ := ht ψ hψ.2
  refine ⟨ξ,η,fun n hn => hpair n (by omega),?_⟩
  intro N hN
  have he := sourceResonantRoot_displacementTail_eq N ξ η α β
    (fun n hn => (hpair n (by omega)).2.1) (fun n hn => hpair' n (by omega))
  have hs : Summable (rootDisplacementPowerTail p N ξ η) ∧
      (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ sourcePeriodTwoDisplacementBudget ψ N := by
    simpa only [he] using hsum N (by omega)
  have hdup := sourcePositiveDisplacementPowerTail_self_summable_and_le p N ξ η hs.1
  exact ⟨hs,⟨summable_sourcePositiveDisplacementPowerTail p N ξ η hs.1,
    (tsum_sourcePositiveDisplacementPowerTail_le p N ξ η hs.1).trans hs.2⟩,
    ⟨hdup.1,hdup.2.trans (mul_le_mul_of_nonneg_left hs.2 (by norm_num))⟩⟩

end NLS.ZakharovShabat
