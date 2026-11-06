import NLS.KdV.HillIntrinsicFrequencyCircleMoments
import NLS.KdV.HillFrequencyContourPhysicalBands

/-! A single rough neighborhood makes every original frequency circle
homotopic to its actual intrinsic physical contour. Its size is chosen before
all positive indices, all moment orders and all physical real inputs. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

/-- Actual source-cover data give one H-minus-one ball on which every
frequency circle crosses the same two bands as its intrinsic physical contour. -/
theorem exists_hillHminus_frequency_circles_physical_bands :
    ∃ δ : ℝ, 0<δ ∧ ∀ q : RealPeriodOneHillPotential,
      hillOriginalHminusSource q.val ∈ ball (0 : PeriodOneHminusOne) δ → ∀ k : ℕ+,
      (Real.pi*(k : ℝ)-Real.pi/4)^2 ∈
        Ioo (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)-2))
          (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)-1)) ∧
      (Real.pi*(k : ℝ)+Real.pi/4)^2 ∈
        Ioo (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)))
          (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)+1)) := by
  obtain ⟨C,N,V,_,D⟩ := exists_hillHminus_all_contour_period_data
  obtain ⟨δ,hδ,hsub⟩ := Metric.isOpen_iff.mp D.isOpen 0 D.zero_mem
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈NLS.Coeff.paritySubspace 0 := by simp
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by intro j; simp
  refine ⟨δ,hδ,?_⟩
  intro q hq k
  let u := Fourier.paritySample 0 (SpectralWeight.one.toCoeff q.val)
  have hcoeff : SpectralWeight.one.toCoeff q.val=NLS.Coeff.periodDouble u :=
    (hillPeriodDouble_unitSample _ q.property.1).symm
  have hu : periodOneL2Inclusion u∈V := hsub hq
  exact hillSquaredFrequencyCircle_crossings_physical_bands h0q h0r C D q.val
    q.property.1 q.property.2 u hcoeff hu k

/-- On a single actual rough ball, any series family with its proved
original numerator has EXACTLY the original intrinsic physical moments,
including every logarithm shift, root sign and the quadratic Jacobian. -/
theorem exists_hillHminus_miura_moments_eq_original :
    ∃ δ : ℝ, 0<δ ∧ ∀ (C : HillHminusMiuraChart)
      (s : (n : ℤ) → NLS.CoeffPair 2 → NLS.DeletedCoeff 2 n)
      (q : RealPeriodOneHillPotential), hillOriginalHminusSource q.val ∈ ball (0 : PeriodOneHminusOne) δ →
      ∀ n : ℕ+, (∀ E : ℂ, hillHminusMiuraEnergyPsi C s (n : ℤ) (E,hillOriginalHminusSource q.val) =
        hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E) →
      ∀ (k : ℕ+) (m : ℕ), hillHminusMiuraMoment C s n k m (hillOriginalHminusSource q.val) =
        hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n n.pos k m := by
  obtain ⟨δ,hδ,hbands⟩ := exists_hillHminus_frequency_circles_physical_bands
  refine ⟨δ,hδ,?_⟩
  intro C s q hq n hnum k m
  exact (hillHminusMiuraMoment_eq_physical_frequency_circle C s q n k m hnum).trans
    (hillPhysical_frequency_circle_moment_eq_intrinsic q n k m (hbands q hq k))

end NLS.KdV
