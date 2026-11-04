import NLS.KdV.HillQuadraticRootFreeNormalization
import NLS.KdV.HillFilledFreeGapFactorization
import NLS.KdV.HillBoundedComplexTailDomain

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGap_bounded_complex_root_product_matching (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ p ∈ ball (0 : Coeff 2) B, ∀ k : ℕ, N ≤ k →
      ∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        (E,p) ∈ hillAbelianComplexRootDomain 0 h0q h0r ∧
        hillFreeGapQuadraticRoot h0q h0r k (E,p)*hillFilledFreeGapRoot h0q h0r k (E,p)=
          hillAbelianComplexRoot 0 h0q h0r (E,p) := by
  obtain ⟨Nq,hNq,hquadratic⟩ := exists_hillFreeGap_bounded_complex_quadratic_root_chart h0q h0r B
  obtain ⟨Nr,hNr,hroot⟩ := exists_hillFilledFreeGapRoot_bounded_complex_analytic h0q h0r B
  obtain ⟨Nf,hNf,hfactor⟩ := exists_hillFilledFreeGapUnit_bounded_complex_factorization h0q h0r B
  obtain ⟨Nd,hNd,C,hC,htail⟩ := exists_hillFreeGapContour_bounded_complex_tail_domain h0q h0r B
  refine ⟨max (max Nq Nr) (max Nf Nd),hNq.trans ((le_max_left _ _).trans (le_max_left _ _)),?_⟩
  intro p hp k hk E hE
  have hkq : Nq ≤ k := (le_max_left _ _).trans ((le_max_left _ _).trans hk)
  have hkr : Nr ≤ k := (le_max_right _ _).trans ((le_max_left _ _).trans hk)
  have hkf : Nf ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hkd : Nd ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hk1 : 1 ≤ k := hNq.trans hkq
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hhalf : R/2 ≤ ‖E-c‖ := by
    have hh : ‖E-c‖=R := by simpa only [mem_sphere,dist_eq_norm] using hE
    linarith
  have hpB : ‖p‖ < B := by simpa only [mem_ball,dist_zero_right] using hp
  have hnorm (a : Coeff 2) (ha : a ∈ ball (0 : Coeff 2) B) : ‖a‖ ≤ B :=
    (show ‖a‖ < B by simpa only [mem_ball,dist_zero_right] using ha).le
  have hdom (a : Coeff 2) (ha : a ∈ ball (0 : Coeff 2) B) : (E,a) ∈ hillAbelianComplexRootDomain 0 h0q h0r :=
    (htail a (hnorm a ha) k hkd E hE).1
  have hprod (a : Coeff 2) (ha : a ∈ ball (0 : Coeff 2) B) :
      (hillFreeGapQuadraticRoot h0q h0r k (E,a)*hillFilledFreeGapRoot h0q h0r k (E,a))^2=hillL2Radicand a E := by
    rw [mul_pow,((hquadratic k hkq).2 a ha E hhalf).1,
      ((hroot k hkr).2 a ha E (sphere_subset_closedBall hE)).1]
    exact (hfactor a (hnorm a ha) k hkf E).symm
  have hqcont : ContinuousOn (fun a : Coeff 2 => hillFreeGapQuadraticRoot h0q h0r k (E,a)) (ball (0 : Coeff 2) B) :=
    (hquadratic k hkq).1.continuousOn.comp (f := fun a : Coeff 2 => (E,a)) (by fun_prop)
      (fun a ha => ⟨hhalf,ha⟩)
  have hrcont : ContinuousOn (fun a : Coeff 2 => hillFilledFreeGapRoot h0q h0r k (E,a)) (ball (0 : Coeff 2) B) :=
    (hroot k hkr).1.continuousOn.comp (f := fun a : Coeff 2 => (E,a)) (by fun_prop)
      (fun a ha => ⟨sphere_subset_closedBall hE,ha⟩)
  have hleft := hqcont.mul hrcont
  have hright : ContinuousOn (fun a : Coeff 2 => hillAbelianComplexRoot 0 h0q h0r (E,a)) (ball (0 : Coeff 2) B) :=
    (analyticOnNhd_hillAbelianComplexRoot 0 h0q h0r).continuousOn.comp (f := fun a : Coeff 2 => (E,a)) (by fun_prop)
      (fun a ha => hdom a ha)
  have hsq (a : Coeff 2) (ha : a ∈ ball (0 : Coeff 2) B) :
      (hillFreeGapQuadraticRoot h0q h0r k (E,a)*hillFilledFreeGapRoot h0q h0r k (E,a))^2=
        hillAbelianComplexRoot 0 h0q h0r (E,a)^2 :=
    (hprod a ha).trans (hillAbelianComplexRoot_sq 0 h0q h0r (E,a) (hdom a ha)).symm
  have hbase : hillFreeGapQuadraticRoot h0q h0r k (E,0)*hillFilledFreeGapRoot h0q h0r k (E,0)=
      hillAbelianComplexRoot 0 h0q h0r (E,0) := by
    have hb := hillAbelianComplexRoot_base 0 h0q h0r E (hillRealGapContour_sphere_subset 0 h0q h0r k hk1 hE)
    rw [map_zero] at hb
    exact (hillFreeGap_root_product_base h0q h0r k hk1 E hE).trans hb.symm
  have h0B : (0 : Coeff 2) ∈ ball 0 B := mem_ball_self ((norm_nonneg p).trans_lt hpB)
  have heq := (convex_ball (0 : Coeff 2) B).isPreconnected.eq_of_sq_eq hleft hright hsq
    (fun {a} ha => hillAbelianComplexRoot_ne_zero 0 h0q h0r (E,a) (hdom a ha)) h0B hbase
  exact ⟨hdom p hp,heq hp⟩

end NLS.KdV
