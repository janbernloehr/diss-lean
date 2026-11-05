import NLS.KdV.HillAbelianComplexRoot
import NLS.KdV.HillAbelianHilbertPeriods

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillAbelianComplexRoot_contour_neighborhood (k : ℕ) (hk : 1 ≤ k) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ SpectralWeight.one.toCoeff q ∈ U ∧
      ∀ p ∈ U, ∀ z ∈ sphere (hillRealGapCenter q hq hr k : ℂ)
        (hillRealGapHalfLength q hq hr k + hillRealGapCollar q hq hr k),
        (z,p) ∈ hillAbelianComplexRootDomain q hq hr := by
  let c := (hillRealGapCenter q hq hr k : ℂ)
  let R := hillRealGapHalfLength q hq hr k + hillRealGapCollar q hq hr k
  have hK : sphere c R ×ˢ {SpectralWeight.one.toCoeff q} ⊆
      hillAbelianComplexRootDomain q hq hr := by
    rintro ⟨z,p⟩ ⟨hz,hp⟩
    have he : p = SpectralWeight.one.toCoeff q := hp
    subst p
    exact mem_hillAbelianComplexRootDomain_base q hq hr z
      (hillRealGapContour_sphere_subset q hq hr k hk hz)
  obtain ⟨W,U,_,hU,hW,hqU,hWU⟩ := generalized_tube_lemma
    (isCompact_sphere c R) isCompact_singleton
    (isOpen_hillAbelianComplexRootDomain q hq hr) hK
  refine ⟨U,hU,hqU (mem_singleton _),?_⟩
  intro p hp z hz
  exact hWU ⟨hW hz,hp⟩

def hillAbelianComplexPeriod (n k : ℕ) (t : Coeff 2 × Coeff 2) : ℂ :=
  (2*(Real.pi : ℂ))⁻¹ * ∮ z in C((hillRealGapCenter q hq hr k : ℂ),
    hillRealGapHalfLength q hq hr k + hillRealGapCollar q hq hr k),
      hillAbelianHilbertPsi n (z,t.1)/hillAbelianComplexRoot q hq hr (z,t.2)

theorem exists_hillAbelianComplexPeriod_analytic_neighborhood (n k : ℕ) (hk : 1 ≤ k) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ SpectralWeight.one.toCoeff q ∈ U ∧
      AnalyticOnNhd ℂ (hillAbelianComplexPeriod q hq hr n k) (univ ×ˢ U) := by
  obtain ⟨U,hU,hqU,hcircle⟩ := exists_hillAbelianComplexRoot_contour_neighborhood q hq hr k hk
  let J : ℂ × (Coeff 2 × Coeff 2) → ℂ × Coeff 2 := fun v => (v.1,v.2.2)
  let K : ℂ × (Coeff 2 × Coeff 2) → ℂ × Coeff 2 := fun v => (v.1,v.2.1)
  let D := J ⁻¹' hillAbelianComplexRootDomain q hq hr
  let F : ℂ × (Coeff 2 × Coeff 2) → ℂ := fun v =>
    hillAbelianHilbertPsi n (K v)/hillAbelianComplexRoot q hq hr (J v)
  have hJ : AnalyticOnNhd ℂ J univ := by
    intro v _
    exact analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have hK : AnalyticOnNhd ℂ K univ := by
    intro v _
    exact analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have hD : IsOpen D := (isOpen_hillAbelianComplexRootDomain q hq hr).preimage
    (continuousOn_univ.mp hJ.continuousOn)
  have hF : AnalyticOnNhd ℂ F D := by
    intro v hv
    have hn := (analyticOnNhd_hillAbelianHilbertPsi n (K v) (mem_univ _)).comp (hK v (mem_univ _))
    have hd := (analyticOnNhd_hillAbelianComplexRoot q hq hr (J v) hv).comp (hJ v (mem_univ _))
    exact hn.div hd (hillAbelianComplexRoot_ne_zero q hq hr (J v) hv)
  have hR := add_nonneg (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1.le
  have hc := analyticOnNhd_circleIntegral_of_jointAnalytic F hD hF
    (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr k + hillRealGapCollar q hq hr k) hR
    (isOpen_univ.prod hU)
    (fun t ht z hz => hcircle t.2 ht.2 z hz)
  exact ⟨U,hU,hqU,analyticOnNhd_const.mul hc⟩

theorem hillAbelianComplexPeriod_at_base (n k : ℕ) (hk : 1 ≤ k) (a : Coeff 2) :
    hillAbelianComplexPeriod q hq hr n k (a,SpectralWeight.one.toCoeff q) =
      hillAbelianHilbertPeriod q hq hr n k a := by
  unfold hillAbelianComplexPeriod hillAbelianHilbertPeriod
  congr 1
  apply circleIntegral.integral_congr
    (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1
      (hillRealGapContour_geometry q hq hr k hk).2.1.le)
  intro z hz
  dsimp only []
  rw [hillAbelianComplexRoot_base q hq hr z (hillRealGapContour_sphere_subset q hq hr k hk hz)]

end NLS.KdV
