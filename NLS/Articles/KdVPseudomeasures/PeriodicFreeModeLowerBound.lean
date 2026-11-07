import NLS.Articles.KdVPseudomeasures.PeriodicEndpointProjectionConvergence
import NLS.Articles.KdVPseudomeasures.PeriodicSpectralBasis
import NLS.FunctionalAnalysis.NearProjectionLowerBound
import NLS.KdV.HillFreeModeProjection
import NLS.KdV.HillStrongSobolevDomain
import NLS.KdV.SingularHillL2EigenProjection

/-! Source Lemma 2.14 on the original complex endpoint space, original
finite-p eigenfunction domains and SAME literal free Fourier projector.
The cutoff is uniform on each original endpoint norm ball. -/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The original strong-space Fourier equation is exactly the native Hill
equation of its IDENTICAL entire H1 distribution, for EVERY Banach exponent. -/
theorem sourceStrongHillEquation_iff_native (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : FourierLebesgueSpace (2:ℝ) (-r+2) p) (z : ℂ) :
    singularHillOperator (sourceComplexHminusOne r hr q)
        (hillStrongSobolevToH1 (-r+2) (by linarith [hr.2]) p f) =
      z • singularHillDomainInclusion (hillStrongSobolevToH1 (-r+2) (by linarith [hr.2]) p f) ↔
    ∀ k : ℤ, (z-(freeHillValue k:ℂ))*f.val (mode (-k)) =
      ∑' m : ℤ, q.val (mode (-(k-m)))*f.val (mode (-m)) := by
  rw [singularHillOperator_eigen_iff]
  simp only [hillStrongSobolevToH1_val,sourceComplexHminusOne_val]

/-- ONE cutoff gives a one-half free-mode norm lower bound on the ENTIRE
actual high spectral range, including all complex associated vectors.
It may be chosen above ANY supplied prior spectral cutoff. -/
theorem exists_uniform_sourcePeriodicRange_freeMode_lower (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (Nmin : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ Nmin ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ n : ℕ+, N ≤ (n:ℕ) → ∀ F : CircleL2,
        F ∈ (singularHillL2RieszProjection (sourceComplexHminusOne r hr q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range →
        (1/2:ℝ)*‖F‖ ≤ ‖hillFreeL2ModeProjection (n:ℕ) F‖ := by
  obtain ⟨NP,hNP,hproj⟩ := exists_uniform_sourceEndpointPeriodicProjection_sub_free_small r hr R
    (epsilon := 1/2) (by norm_num)
  obtain ⟨NC,_,hcircle⟩ := exists_uniform_sourcePeriodicCircle_rank_two r hr R
  have hl : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NL,hNL⟩ := eventually_atTop.mp (hl.eventually_gt_atTop (1:ℝ))
  let N := max Nmin (max NP (max NC NL))
  refine ⟨N,by dsimp [N];omega,by dsimp [N];omega,?_⟩
  intro q hq n hn F hF
  have hnP : NP ≤ (n:ℕ) := by dsimp [N] at hn;omega
  have hnC : NC ≤ (n:ℕ) := by dsimp [N] at hn;omega
  have hnL : NL ≤ (n:ℕ) := by dsimp [N] at hn;omega
  have hc := (hcircle q hq n hnC).1
  have hnear := (hproj q hq n hnP).2.2
  have hfree : singularHillL2RieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) = hillFreeL2ModeProjection (n:ℕ) := by
    rw [← freeHillValue_natCast_complex]
    exact hillL2RieszProjection_zero_eq_modes (n:ℕ) n.property (hNL (n:ℕ) hnL)
  rw [hfree] at hnear
  have hfixed : singularHillL2RieszProjection (sourceComplexHminusOne r hr q)
      (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) F=F := by
    obtain ⟨G,hG⟩ := hF
    rw [← hG]
    exact congrArg (fun T : CircleL2 →L[ℂ] CircleL2 => T G)
      (isIdempotentElem_singularHillL2RieszProjection _ _ _ (by exact_mod_cast n.property) hc)
  have h := NLS.FunctionalAnalysis.norm_image_ge_of_near_fixed _ _ (1/2) hnear.le F hfixed
  norm_num only [show (1:ℝ)-1/2=1/2 by norm_num] at h
  exact h

/-- Every native high eigenvector in the ORIGINAL spectral strip belongs
to the SAME actual source-circle range, without a nonzero-vector premise. -/
theorem sourcePeriodicEigenvector_mem_range (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (n : ℕ+) (pair : SourceHillComplexPair r hr q n)
    (z : ℂ) (hz : z ∈ reducedHillStrip (n:ℕ)) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (sourceComplexHminusOne r hr q) f=z • singularHillDomainInclusion f) :
    singularHillL2DomainInclusion f ∈
      (singularHillL2RieszProjection (sourceComplexHminusOne r hr q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range := by
  by_cases hf0 : f=0
  · simp [hf0]
  have hsp := (sourceHillSpectrum_mem_iff r hr q z).mpr ⟨f,hf0,hf⟩
  have hi : z ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) := by
    rw [← freeHillValue_natCast_complex]
    rcases (SourceHillComplexPair.spectrum_iff r hr q (n:ℕ) pair z hz).mp hsp with h | h
    · rw [h]
      exact pair.left_mem_sourceBall r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r q) n.property
    · rw [h]
      exact pair.right_mem_sourceBall r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r q) n.property
  have hfix := singularHillL2RieszProjection_eigenvector_inside (sourceComplexHminusOne r hr q) _ _
    (by exact_mod_cast n.property) (SourceHillComplexPair.sourceCircle_rank_two r hr q n pair).1 z hi f hf
  exact ⟨singularHillL2DomainInclusion f,hfix⟩

/-- The source one-half lower bound for ALL original native high eigenvectors,
with ONE cutoff before the entire original complex endpoint norm ball. -/
theorem exists_uniform_sourcePeriodicEigen_freeMode_lower (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (Nmin : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ Nmin ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ n : ℕ+, N ≤ (n:ℕ) → ∀ z ∈ wideHillStrip (n:ℕ), ∀ f : FourierLebesgueSpace (2:ℝ) 1 2,
        singularHillOperator (sourceComplexHminusOne r hr q) f=z • singularHillDomainInclusion f →
        (1/2:ℝ)*‖singularHillL2DomainInclusion f‖ ≤
          ‖hillFreeL2ModeProjection (n:ℕ) (singularHillL2DomainInclusion f)‖ := by
  obtain ⟨NP,hNP,hmin,hbound⟩ := exists_uniform_sourcePeriodicRange_freeMode_lower r hr R Nmin
  obtain ⟨NL,_,hlabels⟩ := source_uniform_canonical_complex_labels r hr R
  obtain ⟨NW,_,hwide⟩ := exists_wideEndpointHill_cutoff r hr.2 R
  let N := max NP (max NL NW)
  refine ⟨N,by dsimp [N];omega,by dsimp [N];omega,?_⟩
  intro q hq n hn z hz f hf
  by_cases hf0 : f=0
  · simp [hf0]
  have hnP : NP ≤ (n:ℕ) := by dsimp [N] at hn;omega
  have hnL : NL ≤ (n:ℕ) := by dsimp [N] at hn;omega
  have hnW : NW ≤ (n:ℕ) := by dsimp [N] at hn;omega
  have hn2 : 2 ≤ (n:ℕ) := hNP.trans hnP
  have hswide : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hq (by positivity [endpointHillConstant_pos r hr.2])).trans (hwide (n:ℕ) hnW)
  have hsp := (sourceHillSpectrum_mem_iff r hr q z).mpr ⟨f,hf0,hf⟩
  have hznarrow := (sourceHillSpectrum_wide_localization r hr (n:ℕ) hn2 q hswide z hz hsp).1
  obtain ⟨pair,_,_⟩ := (hlabels q hq).high_pair (n:ℕ) hnL
  exact hbound q hq n hnP _ (sourcePeriodicEigenvector_mem_range r hr q n pair z hznarrow f hf)

/-- Source Lemma 2.14 in its ORIGINAL F-ell^(s+2,p) domain, for EVERY Banach
exponent p including infinity. Its literal full Fourier eigen-equation,
original strip and norm-ball-uniform cutoff are retained. The faithful H1
realization defines the SAME original physical L2 function on both sides. -/
theorem sourceLemma2_14 (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) (Nmin : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ Nmin ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ n : ℕ+, N ≤ (n:ℕ) → ∀ z ∈ wideHillStrip (n:ℕ),
        ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : FourierLebesgueSpace (2:ℝ) (-r+2) p),
          (∀ k : ℤ, (z-(freeHillValue k:ℂ))*f.val (mode (-k)) =
            ∑' m : ℤ, q.val (mode (-(k-m)))*f.val (mode (-m))) →
          (1/2:ℝ)*‖singularHillL2DomainInclusion (hillStrongSobolevToH1 (-r+2) (by linarith [hr.2]) p f)‖ ≤
            ‖hillFreeL2ModeProjection (n:ℕ)
              (singularHillL2DomainInclusion (hillStrongSobolevToH1 (-r+2) (by linarith [hr.2]) p f))‖ := by
  obtain ⟨N,hN,hmin,hbound⟩ := exists_uniform_sourcePeriodicEigen_freeMode_lower r hr R Nmin
  refine ⟨N,hN,hmin,?_⟩
  intro q hq n hn z hz p _ f hf
  exact hbound q hq n hn z hz _ ((sourceStrongHillEquation_iff_native r hr q p f z).mpr hf)

end NLS.Articles.KdVPseudomeasures
