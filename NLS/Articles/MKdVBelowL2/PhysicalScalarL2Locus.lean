import NLS.Articles.MKdVBelowL2.PhysicalNonzeroBirkhoffIndex
import NLS.Articles.MKdVBelowL2.ScalarFourthTrajectory
import NLS.Fourier.PeriodicFourierLebesgueEmbeddings

/-! # The literal physical L² locus of original real scalar distributions

Membership is square-summability of the unchanged original Fourier
coefficients. The verified period-one Fourier isometry identifies this
with an actual L² function representing the same original distribution.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory NLS.Fourier NLS.Fourier.SmoothPeriodicTest
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def physicalScalarL2Locus (p : ℝ≥0∞) [Fact (1 ≤ p)] : Set (PhysicalScalarRealInput p) :=
  {u | u.val.val ∈ periodicFourierLebesgueSubmodule (L := (1:ℝ)) Weight.one 2}

/-- A Hilbert pair representing the same original scalar distribution
puts that scalar distribution in the literal physical L² locus. -/
theorem mem_physicalScalarL2Locus_of_pair_hilbert (u : PhysicalScalarRealInput p)
    (hu : physicalPairHasHilbertRepresentative (physicalScalarPairCLM u)) :
    u ∈ physicalScalarL2Locus p := by
  obtain ⟨v,h1,_⟩ := hu
  change u.val.val ∈ periodicFourierLebesgueSubmodule (L := (1:ℝ)) Weight.one 2
  change u.val.val = v.val.1.val at h1
  rw [h1]
  exact v.val.1.property

/-- The same literal locus is represented by actual functions in the
period-one L² quotient, with the same original distribution functional. -/
theorem mem_physicalScalarL2Locus_iff_l2_function (u : PhysicalScalarRealInput p) :
    u ∈ physicalScalarL2Locus p ↔
      ∃ f : Lp ℂ 2 (@AddCircle.haarAddCircle (1:ℝ) inferInstance),
        Distribution.ofCircleL1 f ((Lp.memLp f).integrable (by norm_num)) = u.val.val := by
  constructor
  · intro hu
    let v : PhysicalFL 2 := ⟨u.val.val,hu⟩
    exact ⟨PeriodicFourierLebesgue.l2Isometry v,PeriodicFourierLebesgue.l2Isometry_represents v⟩
  · rintro ⟨f,hf⟩
    let v : PhysicalFL 2 := PeriodicFourierLebesgue.ofLp (q := 2) (by norm_num) f
    have hv : v.val = u.val.val := (PeriodicFourierLebesgue.ofLp_represents (by norm_num) f).trans hf
    change u.val.val ∈ periodicFourierLebesgueSubmodule (L := (1:ℝ)) Weight.one 2
    rw [← hv]
    exact v.property

end NLS.Articles.MKdVBelowL2
