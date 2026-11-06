import NLS.KdV.SingularHillSpectralProjection

/-! # Exact physical root-space ranges for a one- or two-value spectral island -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal Classical
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem singularHillRieszProjection_range_eq_pair
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (hq : q.val = q.val.conjugate)
    (c : ℂ) (r : ℝ) (hr : 0 < r) (hc : sphere c r ⊆ singularHillResolventSet q)
    (a b : ℂ) (ha : a ∈ ball c r) (hb : b ∈ ball c r)
    (honly : ∀ z ∈ ball c r, z ∈ singularHillSpectrum q → z = a ∨ z = b) :
    (singularHillRieszProjection q c r).range = singularHillRootSpaceTop q a ⊔ singularHillRootSpaceTop q b := by
  obtain ⟨w,hw⟩ := singularHillResolventSet_nonempty q
  rw [singularHillRieszProjection_range_eq_roots q hq c r hr hc w hw]
  apply le_antisymm
  · apply iSup_le
    intro z
    by_cases hz : z.val ∈ singularHillSpectrum q
    · rcases honly z.val z.property hz with he | he
      · rw [he]; exact le_sup_left
      · rw [he]; exact le_sup_right
    · have hres : z.val ∈ singularHillResolventSet q := by
        simpa only [singularHillSpectrum,mem_compl_iff,not_not] using hz
      rw [singularHillRootSpaceTop_eq_bot_of_mem_resolvent q z.val hres]
      exact bot_le
  · apply sup_le
    · exact le_iSup (fun z : ball c r => singularHillRootSpaceTop q z.val) ⟨a,ha⟩
    · exact le_iSup (fun z : ball c r => singularHillRootSpaceTop q z.val) ⟨b,hb⟩

theorem singularHillRieszProjection_rank_eq_pair_multiplicity
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (hq : q.val = q.val.conjugate)
    (c : ℂ) (r : ℝ) (hr : 0 < r) (hc : sphere c r ⊆ singularHillResolventSet q)
    (a b : ℂ) (ha : a ∈ ball c r) (hb : b ∈ ball c r) (hab : a ≠ b)
    (honly : ∀ z ∈ ball c r, z ∈ singularHillSpectrum q → z = a ∨ z = b) :
    Module.finrank ℂ (singularHillRieszProjection q c r).range =
      singularHillAlgebraicMultiplicity q a+singularHillAlgebraicMultiplicity q b := by
  rw [singularHillRieszProjection_range_eq_pair q hq c r hr hc a b ha hb honly]
  obtain ⟨w,hw⟩ := singularHillResolventSet_nonempty q
  let : ∀ z : ℂ, FiniteDimensional ℂ (singularHillRootSpaceTop q z) :=
    fun z => finiteDimensional_singularHillRootSpaceTop q z
  have h := NLS.FunctionalAnalysis.finrank_finset_sup_of_iSupIndep (singularHillRootSpaceTop q)
    (independent_singularHillRootSpaceTop q w hw) ({a,b} : Finset ℂ)
  rw [Finset.sup_insert,Finset.sup_singleton,Finset.sum_pair hab] at h
  exact h

theorem singularHillRieszProjection_rank_eq_single_multiplicity
    (q : FourierLebesgueSpace (2 : ℝ) (-1) 2) (hq : q.val = q.val.conjugate)
    (c : ℂ) (r : ℝ) (hr : 0 < r) (hc : sphere c r ⊆ singularHillResolventSet q)
    (a : ℂ) (ha : a ∈ ball c r)
    (honly : ∀ z ∈ ball c r, z ∈ singularHillSpectrum q → z = a) :
    Module.finrank ℂ (singularHillRieszProjection q c r).range = singularHillAlgebraicMultiplicity q a := by
  rw [singularHillRieszProjection_range_eq_pair q hq c r hr hc a a ha ha
    (fun z hz hspec => Or.inl (honly z hz hspec)),sup_idem]
  rfl

end NLS.KdV
