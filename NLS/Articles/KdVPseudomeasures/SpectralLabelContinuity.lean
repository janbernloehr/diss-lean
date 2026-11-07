import NLS.Articles.KdVPseudomeasures.SpectralCumulativeCounts

/-! Weak-star continuity of the ACTUAL intrinsic canonical real labels and
gaps on every original endpoint norm-bounded physical set. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV NLS.ComplexAnalysis

/-- Every intrinsic canonical real label is weak-star continuous on every
original endpoint norm-bounded physical set, including repeated entries. -/
theorem continuousAt_sourceHillLabels_on_bounded (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) (q0 : A) (j : ℕ) :
    ContinuousAt (fun q : A => sourceHillLabels r hr q.val.toPotential j) q0 := by
  obtain ⟨R, hR⟩ := hb
  obtain ⟨M, hM, hlabels⟩ := source_uniform_canonical_labels r hr R
  let N := max M (j+2)
  have hN : 2 ≤ N := hM.trans (le_max_left _ _)
  have hj : j < 2*N-1 := by dsimp [N]; omega
  have hs (q : A) : SourceHillRealLabeling r hr q.val.toPotential N
      (sourceHillLabels r hr q.val.toPotential) := by
    apply sourceHillLabels_spec_at r hr q.val.toPotential N hN
    intro n hn
    exact (hlabels q.val.toPotential (hR q.val q.property)).cutoff_small n ((le_max_left _ _).trans hn)
  let a := -sourceSpectralBound r hr R-1
  let b := freeHillValue N-12*(N:ℝ)
  let labels (q : A) := sourceHillLabels r hr q.val.toPotential
  have ha (q : A) : ∀ z ∈ sourceHillSpectrum r hr q.val.toPotential.val, a < z.re := by
    intro z hz
    have hh := sourceHillSpectrum_re_lower_bound_on_ball r hr R q.val.toPotential.val
      (hR q.val q.property) z hz
    dsimp [a]
    linarith
  apply NLS.tendsto_ordered_finite_of_counts (2*N-1) labels (labels q0) a b
    (fun q i _ k _ hik => monotone_sourceHillLabels r hr q.val.toPotential hik)
    (fun i _ k _ hik => (hs q0).monotone hik) ?_ ?_ j hj
  · intro k hk
    exact ⟨ha q0 _ ((hs q0).spectral k), (hs q0).central_below k hk⟩
  · intro c hc hnot
    have hnc : (c:ℂ) ∉ sourceHillSpectrum r hr q0.val.toPotential.val := by
      intro hsp
      obtain ⟨k, hk⟩ := (sourceHillLabels_spectrum_iff r hr q0.val.toPotential c).mp hsp
      have he : labels q0 k = c := (Complex.ofReal_injective hk).symm
      by_cases hkl : k < 2*N-1
      · exact hnot (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hkl, he⟩)
      · have hh := (hs q0).tail_above_separator k (by omega)
        change b < labels q0 k at hh
        rw [he] at hh
        linarith [hc.2]
    have hcircle := source_realDiameter_resolvent r hr q0.val.toPotential a c hc.1.le (ha q0) hnc
    have hρ : 0 < (c-a)/2 := by linarith [hc.1]
    have hstable := eventually_sourceCircleAlgebraicCount_eq r hr A ⟨R,hR⟩ q0
      (((a+c)/2:ℝ):ℂ) ((c-a)/2) hρ hcircle
    filter_upwards [hstable] with q hq
    have hcSphere : (c:ℂ) ∈ Metric.sphere (((a+c)/2:ℝ):ℂ) ((c-a)/2) :=
      (ofReal_mem_realDiameter_sphere_iff a c c hc.1.le).mpr (Or.inr rfl)
    have hnq := hq.1 (c:ℂ) hcSphere
    rw [← sourceCircleAlgebraicCount_realDiameter_eq_lowerCount r hr q.val.toPotential N
      (hs q) a c (ha q) hc.2 hnq,
      ← sourceCircleAlgebraicCount_realDiameter_eq_lowerCount r hr q0.val.toPotential N
      (hs q0) a c (ha q0) hc.2 hnc]
    exact hq.2

/-- Continuity holds on each bounded set with its inherited physical weak-star topology. -/
theorem continuous_sourceHillLabels_on_bounded (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) (j : ℕ) :
    Continuous (fun q : A => sourceHillLabels r hr q.val.toPotential j) :=
  continuous_iff_continuousAt.mpr (fun q => continuousAt_sourceHillLabels_on_bounded r hr A hb q j)

/-- The entire intrinsic label sequence is continuous in the product topology. -/
theorem continuous_sourceHillLabels_sequence_on_bounded (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) :
    Continuous (fun q : A => sourceHillLabels r hr q.val.toPotential) :=
  continuous_pi_iff.mpr (continuous_sourceHillLabels_on_bounded r hr A hb)

/-- Each ACTUAL signed canonical gap is weak-star continuous on bounded original sets. -/
theorem continuous_sourceCanonicalGapValues_on_bounded (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) (k : ℤ) :
    Continuous (fun q : A => sourceCanonicalGapValues r hr q.val.toPotential k) := by
  unfold sourceCanonicalGapValues
  split_ifs
  · exact continuous_const
  · exact Complex.continuous_ofReal.comp
      ((continuous_sourceHillLabels_on_bounded r hr A hb (2*k.natAbs)).sub
        (continuous_sourceHillLabels_on_bounded r hr A hb (2*k.natAbs-1)))

/-- The entire actual signed gap sequence is continuous in its product topology. -/
theorem continuous_sourceCanonicalGapValues_sequence_on_bounded (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) :
    Continuous (fun q : A => sourceCanonicalGapValues r hr q.val.toPotential) :=
  continuous_pi_iff.mpr (continuous_sourceCanonicalGapValues_on_bounded r hr A hb)

end NLS.Articles.KdVPseudomeasures
