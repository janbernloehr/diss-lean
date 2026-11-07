import NLS.Articles.KdVPseudomeasures.OriginalHillNativeCompactFibers
import NLS.Articles.KdVPseudomeasures.OriginalCanonicalGapSquares
import NLS.KdV.HillDirichletSpectralCurveInvariants
import NLS.FunctionalAnalysis.CompactInvariantGlobalCurve

/-! Complete native indexed spectral flows through every original
physical H-minus-one source. Actual original isospectral compactness
proves completeness. All original gaps and the intrinsic angle-pair
scalar are preserved, without continuing a local additive angle chart. -/
noncomputable section
open Set NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

def originalHillNativeSpectralFlow (k : ℕ+) (q : HillRealMeanZeroSource) (t : ℝ) : HillRealMeanZeroSource :=
  (originalHillNativeSpectralSystem k).globalCurve q t

theorem originalHillNativeSpectralFlow_zero (k : ℕ+) (q : HillRealMeanZeroSource) :
    originalHillNativeSpectralFlow k q 0=q :=
  (originalHillNativeSpectralSystem k).globalCurve_zero q

theorem hasDerivAt_originalHillNativeSpectralFlow (k : ℕ+) (q : HillRealMeanZeroSource) (t : ℝ) :
    HasDerivAt (originalHillNativeSpectralFlow k q)
      (hillRealDirichletSpectralVector k (originalHillNativeSpectralFlow k q t)) t :=
  (originalHillNativeSpectralSystem k).hasDerivAt_globalCurve q t

theorem originalHillNativeSpectralFlow_add (k : ℕ+) (q : HillRealMeanZeroSource) (s t : ℝ) :
    originalHillNativeSpectralFlow k q (t+s)=
      originalHillNativeSpectralFlow k (originalHillNativeSpectralFlow k q s) t :=
  (originalHillNativeSpectralSystem k).globalCurve_add q s t

theorem originalHillNativeSpectralFlow_conserved (k : ℕ+) (q : HillRealMeanZeroSource) (t : ℝ) :
    hillRealDiscriminantData (originalHillNativeSpectralFlow k q t)=hillRealDiscriminantData q :=
  (originalHillNativeSpectralSystem k).globalCurve_conserved q t

theorem hasDerivAt_originalHillNativeSpectralFlow_inclusion (k : ℕ+) (q : HillRealMeanZeroSource) (t : ℝ) :
    HasDerivAt (fun τ => hillRealMeanZeroInclusion (originalHillNativeSpectralFlow k q τ))
      (hillHminusDirichletSpectralVector k
        (hillRealMeanZeroInclusion (originalHillNativeSpectralFlow k q t))) t := by
  simpa only [hillRealDirichletSpectralVector_inclusion] using
    hasDerivAt_hillRealMeanZeroInclusion_comp _ _ t (hasDerivAt_originalHillNativeSpectralFlow k q t)

def originalHillSpectralFlow (k : ℕ+) (q : OriginalHminusOnePotential) (t : ℝ) : OriginalHminusOnePotential :=
  originalHillPotentialOfRealSource (originalHillNativeSpectralFlow k (originalHillRealMeanZeroSource q) t)

theorem originalHillSpectralFlow_zero (k : ℕ+) (q : OriginalHminusOnePotential) :
    originalHillSpectralFlow k q 0=q := by
  rw [originalHillSpectralFlow,originalHillNativeSpectralFlow_zero,originalHillPotentialOfRealSource_ofOriginal]

theorem originalHillSpectralFlow_coefficients (k : ℕ+) (q : OriginalHminusOnePotential) (t : ℝ) :
    originalPeriodOneCoefficients (originalHillSpectralFlow k q t)=
      hillRealMeanZeroInclusion (originalHillNativeSpectralFlow k (originalHillRealMeanZeroSource q) t) :=
  originalHillPotentialOfRealSource_coefficients _

theorem originalHillSpectralFlow_add (k : ℕ+) (q : OriginalHminusOnePotential) (s t : ℝ) :
    originalHillSpectralFlow k q (t+s)=originalHillSpectralFlow k (originalHillSpectralFlow k q s) t := by
  simp only [originalHillSpectralFlow,originalHillRealMeanZeroSource_ofRealSource,
    originalHillNativeSpectralFlow_add]

theorem originalHillSpectralFlow_inverse (k : ℕ+) (q : OriginalHminusOnePotential) (t : ℝ) :
    originalHillSpectralFlow k (originalHillSpectralFlow k q t) (-t)=q := by
  rw [← originalHillSpectralFlow_add,neg_add_cancel,originalHillSpectralFlow_zero]

theorem hasDerivAt_originalHillSpectralFlow_coefficients (k : ℕ+) (q : OriginalHminusOnePotential) (t : ℝ) :
    HasDerivAt (fun τ => originalPeriodOneCoefficients (originalHillSpectralFlow k q τ))
      (hillHminusDirichletSpectralVector k (originalPeriodOneCoefficients (originalHillSpectralFlow k q t))) t := by
  simpa only [originalHillSpectralFlow_coefficients] using
    hasDerivAt_originalHillNativeSpectralFlow_inclusion k (originalHillRealMeanZeroSource q) t

theorem originalHillSpectralFlow_mem_isospectral (k : ℕ+) (q : OriginalHminusOnePotential) (t : ℝ) :
    originalHillSpectralFlow k q t ∈ originalIsospectralSet q := by
  apply (mem_originalIsospectralSet_iff_discriminant_eq _ _).mpr
  have he := originalHillNativeSpectralFlow_conserved k (originalHillRealMeanZeroSource q) t
  change hillRealDiscriminantData (originalHillRealMeanZeroSource (originalHillSpectralFlow k q t))=
    hillRealDiscriminantData (originalHillRealMeanZeroSource q)
  simpa only [originalHillSpectralFlow,originalHillRealMeanZeroSource_ofRealSource] using he

theorem originalHillSpectralFlow_gapSquare (k n : ℕ+) (q : OriginalHminusOnePotential) (t : ℝ) :
    hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients (originalHillSpectralFlow k q t))=
      hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) := by
  rw [originalCanonicalGapSquare_eq,originalCanonicalGapSquare_eq,
    originalCanonicalGapValues_isospectral q _ (originalHillSpectralFlow_mem_isospectral k q t)]

theorem originalHillSpectralFlow_other_terminal (j k : ℕ+) (hjk : j ≠ k)
    (q : OriginalHminusOnePotential) (t : ℝ) :
    (hillHminusCanonicalDirichlet j (originalPeriodOneCoefficients (originalHillSpectralFlow k q t)),
      hillHminusDirichletNorming j (originalPeriodOneCoefficients (originalHillSpectralFlow k q t)),
      hillHminusDirichletSheet j (originalPeriodOneCoefficients (originalHillSpectralFlow k q t)))=
    (hillHminusCanonicalDirichlet j (originalPeriodOneCoefficients q),
      hillHminusDirichletNorming j (originalPeriodOneCoefficients q),
      hillHminusDirichletSheet j (originalPeriodOneCoefficients q)) := by
  let γ : ℝ → PeriodOneHminusOne := fun τ => originalPeriodOneCoefficients (originalHillSpectralFlow k q τ)
  let a : ℝ := min t 0-1
  let b : ℝ := max t 0+1
  have ht : t ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_left t 0],
    by dsimp [b]; linarith [le_max_left t 0]⟩
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_right t 0],
    by dsimp [b]; linarith [le_max_right t 0]⟩
  have hd (s : ℝ) (_hs : s ∈ Ioo a b) : HasDerivAt γ (hillHminusDirichletSpectralVector k (γ s)) s :=
    hasDerivAt_originalHillSpectralFlow_coefficients k q s
  have hdom (s : ℝ) (_hs : s ∈ Ioo a b) : γ s ∈ hillHminusCanonicalDirichletDomain :=
    real_mem_hillHminusCanonicalDirichletDomain _ (originalPeriodOneCoefficients_real _)
  simpa only [γ,originalHillSpectralFlow_zero] using
    hillHminus_other_terminal_eq_on_spectralCurve j k hjk γ a b hd hdom t 0 ht h0

theorem originalHillSpectralFlow_completePhasePair (n m k : ℕ+) (q : OriginalHminusOnePotential)
    (hn : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0)
    (hm : hillHminusCanonicalGapSquare m (originalPeriodOneCoefficients q) ≠ 0) (t : ℝ) :
    hillHminusCompletePhasePairBracket n m (originalPeriodOneCoefficients (originalHillSpectralFlow k q t))=
      hillHminusCompletePhasePairBracket n m (originalPeriodOneCoefficients q) := by
  let γ : ℝ → PeriodOneHminusOne := fun τ => originalPeriodOneCoefficients (originalHillSpectralFlow k q τ)
  let a : ℝ := min t 0-1
  let b : ℝ := max t 0+1
  have ht : t ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_left t 0],
    by dsimp [b]; linarith [le_max_left t 0]⟩
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_right t 0],
    by dsimp [b]; linarith [le_max_right t 0]⟩
  have hgn (s : ℝ) (_hs : s ∈ Ioo a b) : hillHminusCanonicalGapSquare n (γ s) ≠ 0 := by
    change hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients (originalHillSpectralFlow k q s)) ≠ 0
    rwa [originalHillSpectralFlow_gapSquare]
  have hgm (s : ℝ) (_hs : s ∈ Ioo a b) : hillHminusCanonicalGapSquare m (γ s) ≠ 0 := by
    change hillHminusCanonicalGapSquare m (originalPeriodOneCoefficients (originalHillSpectralFlow k q s)) ≠ 0
    rwa [originalHillSpectralFlow_gapSquare]
  simpa only [γ,originalHillSpectralFlow_zero] using
    hillHminusCompletePhasePair_eq_on_spectralCurve n m k γ a b
      (fun s _ => hasDerivAt_originalHillSpectralFlow_coefficients k q s)
      (fun _ _ => originalPeriodOneCoefficients_real _) hgn hgm t 0 ht h0

end NLS.Articles.KdVPseudomeasures
