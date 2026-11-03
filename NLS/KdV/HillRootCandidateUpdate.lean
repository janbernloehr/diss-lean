import NLS.KdV.HillRootPeriodGapLocation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelianHilbertPsi_rootUpdate_eq_candidate_update
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n m : ℕ) (hm : 1 ≤ m) (s : ℝ) (E : ℂ) :
    hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m
      (hillGapRootHilbertCoordinates q hq hr roots hroots,(s:ℂ))) =
      hillAbelianPsiCandidate (Function.update roots (m-1) s) n E := by
  apply hillAbelianHilbertPsi_eq_real_candidate
  intro j
  change ((Function.update roots (m-1) s j):ℂ) = hillAbelianHilbertRootEnergy
    (hillAbelianRootUpdate m (hillGapRootHilbertCoordinates q hq hr roots hroots,(s:ℂ))) (j+1)
  by_cases hj : j = m-1
  · subst j
    rw [Function.update_self,Nat.sub_add_cancel hm,hillAbelianHilbertRootEnergy_update_same m hm]
  · rw [Function.update_apply,if_neg hj,
      hillAbelianHilbertRootEnergy_update_other m (j+1) (by omega)]
    exact hillGapRootHilbertCoordinates_reconstruct q hq hr roots hroots j

theorem hillIntrinsicGapPeriod_rootUpdate_eq_candidate_update
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (s : ℝ) :
    hillIntrinsicGapPeriod q hq hr k (fun E => hillAbelianHilbertPsi n
      (E,hillAbelianRootUpdate m (hillGapRootHilbertCoordinates q hq hr roots hroots,(s:ℂ)))) =
      hillAbelianCandidatePeriod q hq hr (Function.update roots (m-1) s) n k := by
  unfold hillIntrinsicGapPeriod hillAbelianCandidatePeriod
  congr 1
  apply circleIntegral.integral_congr (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1.le)
  intro E _
  dsimp only []
  rw [hillAbelianHilbertPsi_rootUpdate_eq_candidate_update q hq hr roots hroots n m hm s E]

def hillGapRootBoxCoordinateUpdate (m : ℕ) (hm : 1 ≤ m) (s : ℝ)
    (hs : s ∈ Icc (hillRealLabels q hq hr (2*m-1)) (hillRealLabels q hq hr (2*m)))
    (roots : hillGapRootBox q hq hr) : hillGapRootBox q hq hr :=
  ⟨Function.update roots.val (m-1) s,by
    intro j
    by_cases hj : j = m-1
    · subst j
      simpa only [Function.update_self,Nat.sub_add_cancel hm] using hs
    · simpa only [Function.update_apply,if_neg hj] using roots.property j⟩

theorem continuous_hillGapRootBoxCoordinateUpdate (m : ℕ) (hm : 1 ≤ m) (s : ℝ)
    (hs : s ∈ Icc (hillRealLabels q hq hr (2*m-1)) (hillRealLabels q hq hr (2*m))) :
    Continuous (hillGapRootBoxCoordinateUpdate q hq hr m hm s hs) := by
  have hc : Continuous (fun roots : hillGapRootBox q hq hr => Function.update roots.val (m-1) s) := by
    apply continuous_pi
    intro j
    by_cases hj : j = m-1
    · simpa only [Function.update_apply,hj,ite_true] using (continuous_const : Continuous (fun _ : hillGapRootBox q hq hr => s))
    · simpa only [Function.update_apply,if_neg hj,Function.comp_def] using (continuous_apply j).comp continuous_subtype_val
  exact hc.subtype_mk (fun roots => (hillGapRootBoxCoordinateUpdate q hq hr m hm s hs roots).property)

end NLS.KdV
