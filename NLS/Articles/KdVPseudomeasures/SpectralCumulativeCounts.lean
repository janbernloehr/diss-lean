import NLS.Articles.KdVPseudomeasures.SpectralWeakStarResolvent
import NLS.SequenceSpaces.OrderedFiniteContinuity
import NLS.ComplexAnalysis.RealDiameterDisc

/-! Actual physical disk counts and cumulative canonical label counts. -/
noncomputable section
open Set Metric
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV NLS.ComplexAnalysis

/-- For the real physical spectrum, a diameter circle is a full resolvent
circle when its left endpoint is below the spectrum and its right endpoint
is not spectral. -/
theorem source_realDiameter_resolvent (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (a b : ℝ) (hab : a ≤ b)
    (ha : ∀ z ∈ sourceHillSpectrum r hr q.val, a < z.re)
    (hb : (b:ℂ) ∉ sourceHillSpectrum r hr q.val) :
    ∀ z ∈ sphere (((a+b)/2:ℝ):ℂ) ((b-a)/2), z ∉ sourceHillSpectrum r hr q.val := by
  intro z hz hs
  have him := sourceHillSpectrum_ofPotential_real r hr q z hs
  have he : (z.re:ℂ) = z := by apply Complex.ext <;> simp [him]
  have hx := (ofReal_mem_realDiameter_sphere_iff a b z.re hab).mp (he.symm ▸ hz)
  rcases hx with hx | hx
  · have hh := ha z hs
    linarith
  · exact hb (by rwa [← he, hx] at hs)

/-- A real diameter disk below the central separator counts EXACTLY the
canonical prefix entries below its right endpoint, with every actual
algebraic repetition retained. -/
theorem sourceCircleAlgebraicCount_realDiameter_eq_lowerCount
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (N : ℕ)
    (h : SourceHillRealLabeling r hr q N (sourceHillLabels r hr q)) (a b : ℝ)
    (ha : ∀ z ∈ sourceHillSpectrum r hr q.val, a < z.re)
    (hb : b < freeHillValue N-12*(N:ℝ))
    (hnb : (b:ℂ) ∉ sourceHillSpectrum r hr q.val) :
    sourceCircleAlgebraicCount r hr ⟨q⟩ (((a+b)/2:ℝ):ℂ) ((b-a)/2) =
      NLS.finiteLowerCount (2*N-1) (sourceHillLabels r hr q) b := by
  let ell := sourceHillLabels r hr q
  let S := sourceCircleSpectrum r hr ⟨q⟩ (((a+b)/2:ℝ):ℂ) ((b-a)/2)
  have hs (z : ℂ) (hz : z ∈ S) : z ∈ sourceHillSpectrum r hr q.val ∧ a < z.re ∧ z.re < b := by
    obtain ⟨hsp, hball⟩ := (mem_sourceCircleSpectrum r hr ⟨q⟩ _ _ z).mp hz
    have him := sourceHillSpectrum_ofPotential_real r hr q z hsp
    have he : (z.re:ℂ) = z := by apply Complex.ext <;> simp [him]
    have hi := (ofReal_mem_realDiameter_ball_iff a b z.re).mp (he.symm ▸ hball)
    exact ⟨hsp, hi.1, hi.2⟩
  have hsreal (z : ℂ) (hz : z ∈ S) : (z.re:ℂ) = z := by
    have him := sourceHillSpectrum_ofPotential_real r hr q z (hs z hz).1
    apply Complex.ext <;> simp [him]
  have hmult (z : ℂ) (hz : z ∈ S) : sourceHillAlgebraicMultiplicity r hr q.val z =
      ∑ j ∈ Finset.range (2*N-1), if ell j = z.re then 1 else 0 := by
    have hc := h.central_counts z.re
    have hm : (z.re:ℂ) ∈ sourceCentralSpectrum r hr q.val N :=
      (mem_sourceCentralSpectrum r hr q.val N _).mpr
        ⟨(hsreal z hz).symm ▸ (hs z hz).1, (hs z hz).2.2.trans hb⟩
    rw [if_pos hm, hsreal z hz] at hc
    exact hc.symm
  have hsum (j : ℕ) (hj : j ∈ Finset.range (2*N-1)) :
      (∑ z ∈ S, if ell j = z.re then (1:ℕ) else 0) = if ell j ≤ b then 1 else 0 := by
    by_cases hjb : ell j ≤ b
    · have hjne : ell j ≠ b := by
        intro he
        exact hnb (he ▸ h.spectral j)
      have hjball : (ell j:ℂ) ∈ ball (((a+b)/2:ℝ):ℂ) ((b-a)/2) :=
        (ofReal_mem_realDiameter_ball_iff a b (ell j)).mpr
          ⟨ha _ (h.spectral j), lt_of_le_of_ne hjb hjne⟩
      have hjS : (ell j:ℂ) ∈ S :=
        (mem_sourceCircleSpectrum r hr ⟨q⟩ _ _ _).mpr ⟨h.spectral j, hjball⟩
      rw [Finset.sum_eq_single (ell j:ℂ)]
      · simp [hjb]
      · intro z hz hzne
        have hne : ell j ≠ z.re := by
          intro he
          exact hzne ((hsreal z hz).symm.trans (congrArg Complex.ofReal he).symm)
        exact if_neg hne
      · intro hnot
        exact (hnot hjS).elim
    · rw [if_neg hjb]
      apply Finset.sum_eq_zero
      intro z hz
      apply if_neg
      intro he
      exact hjb (he ▸ (hs z hz).2.2.le)
  change (∑ z ∈ S, sourceHillAlgebraicMultiplicity r hr q.val z) = _
  calc
    _ = ∑ z ∈ S, ∑ j ∈ Finset.range (2*N-1), if ell j = z.re then 1 else 0 :=
      Finset.sum_congr rfl hmult
    _ = ∑ j ∈ Finset.range (2*N-1), ∑ z ∈ S, if ell j = z.re then 1 else 0 := Finset.sum_comm
    _ = ∑ j ∈ Finset.range (2*N-1), if ell j ≤ b then 1 else 0 := Finset.sum_congr rfl hsum
    _ = _ := by rw [NLS.finiteLowerCount, Finset.card_filter]

end NLS.Articles.KdVPseudomeasures
