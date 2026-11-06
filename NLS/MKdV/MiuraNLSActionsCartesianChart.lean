import NLS.MKdV.MiuraCartesianRotations
import NLS.MKdV.MiuraCartesianRealIdentity
import NLS.ComplexAnalysis.InverseCoordinateStationarity

/-! # Actual l1-valued NLS actions in an original native Cartesian inverse chart

One complex target ball carries the genuine nonlinear inverse, preserves
the physical real form, and supports all original signed NLS actions in
the full summable norm. The source is the exact inverse chart over that
ball, with both inverse identities and the original raw profile retained.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraOriginalNLSActionSequence (a : Coeff 2) : Coeff 1 :=
  sourceHilbertActionSequence miuraActionFlowFamily.psi (scalarL2Diagonal a)

def miuraOriginalNLSActionDomain : Set (Coeff 2) := scalarL2Diagonal ⁻¹' miuraActionFlowFamily.domain

theorem isOpen_miuraOriginalNLSActionDomain : IsOpen miuraOriginalNLSActionDomain :=
  miuraActionFlowFamily.data.source_open.preimage scalarL2Diagonal.continuous

theorem real_mem_miuraOriginalNLSActionDomain (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    a ∈ miuraOriginalNLSActionDomain :=
  miuraActionFlowFamily.data.real_subset (scalarL2Diagonal_realDiagonal a ha).1

theorem analyticOnNhd_miuraOriginalNLSActionSequence :
    AnalyticOnNhd ℂ miuraOriginalNLSActionSequence miuraOriginalNLSActionDomain :=
  fun a ha => (miuraActionFlowFamily.data.hilbert_actionSequence_analytic _ ha).comp (scalarL2Diagonal.analyticAt a)

theorem miuraOriginalNLSActionSequence_apply (a : Coeff 2) (ha : a ∈ miuraOriginalNLSActionDomain) (k : ℤ) :
    miuraOriginalNLSActionSequence a k = sourceComplexAction (by simp) (by norm_num) k (scalarL2Diagonal a) :=
  miuraActionFlowFamily.data.hilbert_actionSequence_apply _ ha k

theorem miuraOriginalNLSActionSequence_actionFlow (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) (t : ℝ) :
    miuraOriginalNLSActionSequence (miuraOriginalL2ActionFlow a ha n t) = miuraOriginalNLSActionSequence a :=
  miuraOriginalL2ActionFlow_NLS_actionSequence a ha n t

structure MiuraCartesianNLSActionChart where
  source : Set (Coeff 2)
  radius : ℝ
  inverse : MiuraPositiveCartesianTarget → Coeff 2
  source_open : IsOpen source
  radius_pos : 0 < radius
  source_zero : (0 : Coeff 2) ∈ source
  forward_analytic : AnalyticOnNhd ℂ miuraPositiveCartesianMap source
  inverse_analytic : AnalyticOnNhd ℂ inverse (ball 0 radius)
  inverse_zero : inverse 0 = 0
  image_source : miuraPositiveCartesianMap '' source = ball 0 radius
  left_inverse : ∀ a ∈ source, inverse (miuraPositiveCartesianMap a) = a
  right_inverse : ∀ z ∈ ball 0 radius, inverse z ∈ source ∧ miuraPositiveCartesianMap (inverse z) = z
  inverse_real : ∀ z ∈ ball 0 radius, z ∈ miuraCartesianRealSubmodule → inverse z ∈ Coeff.physicalRealSubmodule 2
  inverse_action_domain : ∀ z ∈ ball 0 radius, inverse z ∈ miuraOriginalNLSActionDomain

theorem nonempty_miuraCartesianNLSActionChart : Nonempty MiuraCartesianNLSActionChart := by
  obtain ⟨U,V,hU,hV,h0U,h0V,_,_,G,hM,hG,hG0,hleft,hright⟩ := exists_miuraPositiveCartesian_localInverse_at_zero
  have hzero : (0 : Coeff 2) ∈ miuraOriginalNLSActionDomain :=
    real_mem_miuraOriginalNLSActionDomain 0 (by intro j; simp)
  have hnear : ∀ᶠ z in 𝓝 (0 : MiuraPositiveCartesianTarget), z ∈ V ∧ G z ∈ miuraOriginalNLSActionDomain := by
    have ht : Tendsto G (𝓝 0) (𝓝 (0 : Coeff 2)) := by simpa only [hG0] using (hG 0 h0V).continuousAt.tendsto
    filter_upwards [hV.mem_nhds h0V,ht.eventually (isOpen_miuraOriginalNLSActionDomain.mem_nhds hzero)] with z hz hgz
    exact ⟨hz,hgz⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hleftG : ∀ᶠ a in 𝓝 (0 : Coeff 2), G (miuraPositiveCartesianMap a) = a := by
    filter_upwards [hU.mem_nhds h0U] with a ha
    exact hleft a ha
  have hrealG := miuraPositiveCartesian_complex_inverse_real_germ G hleftG
  obtain ⟨q,hq,hrealball⟩ := Metric.mem_nhds_iff.mp hrealG
  let R := min r q
  have hR : 0 < R := lt_min hr hq
  have hRr : ball (0 : MiuraPositiveCartesianTarget) R ⊆ ball 0 r := ball_subset_ball (min_le_left _ _)
  have hRq : ball (0 : MiuraRealCartesianTarget) R ⊆ ball 0 q := ball_subset_ball (min_le_right _ _)
  let S := U ∩ miuraPositiveCartesianMap ⁻¹' ball (0 : MiuraPositiveCartesianTarget) R
  have hS : IsOpen S := hM.continuousOn.isOpen_inter_preimage hU isOpen_ball
  have h0S : (0 : Coeff 2) ∈ S := ⟨h0U,by simp only [mem_preimage,miuraPositiveCartesianMap_zero]; exact mem_ball_self hR⟩
  have hGR (z : MiuraPositiveCartesianTarget) (hz : z ∈ ball 0 R) : G z ∈ S ∧ miuraPositiveCartesianMap (G z) = z := by
    have hb := hball (hRr hz)
    have hg := hright z hb.1
    exact ⟨⟨hg.1,by change miuraPositiveCartesianMap (G z) ∈ ball 0 R; rwa [hg.2]⟩,hg.2⟩
  refine ⟨⟨S,R,G,hS,hR,h0S,fun a ha => hM a ha.1,fun z hz => hG z (hball (hRr hz)).1,hG0,?_,
    fun a ha => hleft a ha.1,hGR,?_,fun z hz => (hball (hRr hz)).2⟩⟩
  · apply Subset.antisymm
    · rintro _ ⟨a,ha,rfl⟩
      exact ha.2
    · intro z hz
      exact ⟨G z,(hGR z hz).1,(hGR z hz).2⟩
  · intro z hz hzr
    have hsub : (⟨z,hzr⟩ : MiuraRealCartesianTarget) ∈ ball 0 R := by
      simp only [mem_ball,dist_zero_right]
      change ‖z‖ < R
      simpa only [mem_ball,dist_zero_right] using hz
    exact hrealball (hRq hsub)

namespace MiuraCartesianNLSActionChart

def observables (C : MiuraCartesianNLSActionChart) (z : MiuraPositiveCartesianTarget) : Coeff 1 :=
  miuraOriginalNLSActionSequence (C.inverse z)

theorem observables_analytic (C : MiuraCartesianNLSActionChart) :
    AnalyticOnNhd ℂ C.observables (ball 0 C.radius) := fun z hz =>
  (analyticOnNhd_miuraOriginalNLSActionSequence _ (C.inverse_action_domain z hz)).comp (C.inverse_analytic z hz)

theorem observables_recover (C : MiuraCartesianNLSActionChart) (a : Coeff 2) (ha : a ∈ C.source) :
    C.observables (miuraPositiveCartesianMap a) = miuraOriginalNLSActionSequence a := by
  change miuraOriginalNLSActionSequence (C.inverse (miuraPositiveCartesianMap a)) = _
  rw [C.left_inverse a ha]

theorem observables_apply (C : MiuraCartesianNLSActionChart) (z : MiuraPositiveCartesianTarget)
    (hz : z ∈ ball 0 C.radius) (k : ℤ) :
    C.observables z k = sourceComplexAction (by simp) (by norm_num) k (scalarL2Diagonal (C.inverse z)) :=
  miuraOriginalNLSActionSequence_apply _ (C.inverse_action_domain z hz) k

end MiuraCartesianNLSActionChart
end NLS.MKdV
