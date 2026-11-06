import NLS.KdV.HillHminusOneCanonicalFreeLabels
import NLS.KdV.HillAllGapSymmetricData
import NLS.KdV.HillLocalGapPhysicalMatching
import NLS.KdV.HillFreeGapContourGeometry

/-! # Scalar symmetric rough gap germs on the original free contours -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillHminusLocalGapMidpoint (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  logarithmicCircleMoment (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1)
    (hillRealGapCenter 0 h0q h0r (n : ℕ))
    (hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ)) 1 q/2

def hillHminusLocalGapSquare (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  2*logarithmicCircleMoment (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1)
    (hillRealGapCenter 0 h0q h0r (n : ℕ))
    (hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ)) 2 q-
  (logarithmicCircleMoment (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1)
    (hillRealGapCenter 0 h0q h0r (n : ℕ))
    (hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ)) 1 q)^2

theorem hillHminusLocalGapMidpoint_l2 (n : ℕ+) (u : Coeff 2) :
    hillHminusLocalGapMidpoint h0q h0r n (periodOneL2Inclusion u) =
      hillLocalGapMidpoint 0 h0q h0r (n : ℕ) (Coeff.periodDouble u) := by
  simp only [hillHminusLocalGapMidpoint,hillLocalGapMidpoint,logarithmicCircleMoment,
    hillHminusRadicand_eq_hillL2]

theorem hillHminusLocalGapSquare_l2 (n : ℕ+) (u : Coeff 2) :
    hillHminusLocalGapSquare h0q h0r n (periodOneL2Inclusion u) =
      hillLocalGapSquare 0 h0q h0r (n : ℕ) (Coeff.periodDouble u) := by
  simp only [hillHminusLocalGapSquare,hillLocalGapSquare,logarithmicCircleMoment,
    hillHminusRadicand_eq_hillL2]

theorem hillHminusLocalGapMoments_zero (n : ℕ+) :
    hillHminusLocalGapMidpoint h0q h0r n 0 = (hillRealGapCenter 0 h0q h0r (n : ℕ) : ℂ) ∧
      hillHminusLocalGapSquare h0q h0r n 0 = 0 := by
  have hdata := hillLocalGapSymmetricData_eq_physical_of_geometry 0 h0q h0r 0 h0q h0r
    (n : ℕ) n.property (hillRealGapContour_band_bounds 0 h0q h0r (n : ℕ) n.property)
    (hillRealGapSegment_subset_intrinsic_contour_ball 0 h0q h0r (n : ℕ) n.property)
  have hM := hillHminusLocalGapMidpoint_l2 h0q h0r n (0 : Coeff 2)
  have hS := hillHminusLocalGapSquare_l2 h0q h0r n (0 : Coeff 2)
  simp only [map_zero] at hM hS hdata
  exact ⟨hM.trans hdata.1,by
    rw [hS,hdata.2,hillFreeGapHalfLength h0q h0r (n : ℕ) n.property]
    norm_num⟩

theorem exists_hillHminusLocalGapMoments_analytic (n : ℕ+) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ (0 : PeriodOneHminusOne) ∈ V ∧
      AnalyticOnNhd ℂ (hillHminusLocalGapMidpoint h0q h0r n) V ∧
      AnalyticOnNhd ℂ (hillHminusLocalGapSquare h0q h0r n) V := by
  let c : ℂ := hillRealGapCenter 0 h0q h0r (n : ℕ)
  let R := hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ)
  have hR : 0 < R := add_pos_of_nonneg_of_pos
    (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).1
    (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).2.1
  let F : ℂ × PeriodOneHminusOne → ℂ := fun t => hillHminusRadicand t.2 t.1
  have hF : AnalyticOnNhd ℂ F univ := analyticOnNhd_hillHminusRadicand_joint
  let D : Set (ℂ × PeriodOneHminusOne) := {t | F t ≠ 0}
  have hD : IsOpen D := isOpen_ne_fun hF.continuous continuous_const
  have hbase : sphere c R ×ˢ ({0} : Set PeriodOneHminusOne) ⊆ D := by
    rintro ⟨z,q⟩ ⟨hz,hq⟩
    have hq0 : q = 0 := mem_singleton_iff.mp hq
    subst q
    change hillHminusRadicand 0 z ≠ 0
    rw [hillHminusRadicand_zero_eq_hillL2]
    simpa only [map_zero] using hillL2Radicand_ne_zero_on_realCutDomain 0 h0q h0r z
      (hillRealGapContour_sphere_subset 0 h0q h0r (n : ℕ) n.property hz)
  obtain ⟨W,V,_,hV,hKW,h0V,hWV⟩ :=
    generalized_tube_lemma (isCompact_sphere c R) isCompact_singleton hD hbase
  have hm (j : ℕ) := analyticOnNhd_logarithmicCircleMoment F hF c R hR.le j hV
    (fun q hq z hz => hWV ⟨hKW hz,hq⟩)
  exact ⟨V,hV,h0V (mem_singleton 0),(hm 1).div_const,
    (analyticOnNhd_const.mul (hm 2)).sub ((hm 1).pow 2)⟩

end NLS.KdV
