import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianRegularity
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianRealInverse
import NLS.KdV.HillBirkhoffAbelianInjective
import NLS.KdV.HillRoughPhysicalL2Reconstruction
import NLS.SequenceSpaces.DeletedRealFiniteApprox

/-! # Global injectivity of the SAME actual real mean-zero rough map

Regular target approximants are compared through actual real inverse
branches. The all-order nonlinear criterion recovers physical L2 sources,
and the verified ORIGINAL global L2 Birkhoff map determines them uniquely.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV
namespace GlobalRoughAbelianForwardData

theorem real_meanZero_injective_of_regular_target (D : GlobalRoughAbelianForwardData)
    (q1 q2 : PeriodOneHminusOne) (hr1 : IsRealPeriodOneHminusOne q1) (hr2 : IsRealPeriodOneHminusOne q2)
    (hm1 : q1.val 0 = 0) (hm2 : q2.val 0 = 0) (he : D.signed q1 = D.signed q2)
    (hZ : Memℓp (fun j => (Weight.sobolev (1/2) j : ℂ)*(D.signed q1).val j) 2) : q1 = q2 := by
  have hL1 : Memℓp q1.val 2 := by
    have h := (D.sobolev_iff_signed_mem q1 hr1 0 (by norm_num)).mpr (by simpa only [zero_add] using hZ)
    simpa only [Weight.sobolev_zero_apply,ofReal_one,one_mul] using h
  have hL2 : Memℓp q2.val 2 := by
    have hZ2 : Memℓp (fun j => (Weight.sobolev (1/2) j : ℂ)*(D.signed q2).val j) 2 := by
      rw [←he]
      exact hZ
    have h := (D.sobolev_iff_signed_mem q2 hr2 0 (by norm_num)).mpr (by simpa only [zero_add] using hZ2)
    simpa only [Weight.sobolev_zero_apply,ofReal_one,one_mul] using h
  obtain ⟨p1,hp1⟩ := exists_original_physical_meanZero_of_real_hminus_l2 q1 hr1 hm1 hL1
  obtain ⟨p2,hp2⟩ := exists_original_physical_meanZero_of_real_hminus_l2 q2 hr2 hm2 hL2
  have hp : p1 = p2 := hillOriginalBirkhoffAbelianCoordinate_injective p1 p2 (by
    intro n
    rw [←D.original_global_birkhoff_agreement p1 n,←D.original_global_birkhoff_agreement p2 n,hp1,hp2,he])
  exact hp1.symm.trans ((congrArg (fun p : hillRealMeanZeroSourceSubmodule => hillOriginalHminusSource p.val.val) hp).trans hp2)

/-- GLOBAL injectivity in the actual normalized real mean-zero rough
charts. There is no smallness, L2 membership or regular target condition. -/
theorem meanZeroForward_injective_on_real (D : GlobalRoughAbelianForwardData)
    (a b : DeletedCoeff 2 0)
    (hr1 : IsRealPeriodOneHminusOne (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a))
    (hr2 : IsRealPeriodOneHminusOne (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) b))
    (he : D.meanZeroForward a = D.meanZeroForward b) : a = b := by
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
  let z := D.meanZeroForward a
  have hJa : deletedL2Conjugation a = a :=
    (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) a).mp hr1
  have hJz : deletedL2Conjugation z = z := by
    change deletedL2Conjugation (D.meanZeroForward a) = D.meanZeroForward a
    rw [←D.meanZeroForward_conjugation,hJa]
  obtain ⟨U1,hU1,hz1,G1,hG1,hG1z,hd1⟩ := D.exists_real_weak_inverse_germ a hr1
  obtain ⟨U2,hU2,hz2,G2,hG2,hG2z,hd2⟩ := D.exists_real_weak_inverse_germ b hr2
  have hz2' : z ∈ U2 := by change D.meanZeroForward a ∈ U2; rw [he]; exact hz2
  have hG2z' : G2 z = b := by change G2 (D.meanZeroForward a) = b; rw [he]; exact hG2z
  let c := fun S : ℕ => deletedSymmetricTruncate S z
  have ht : Tendsto c atTop (𝓝 z) := tendsto_deletedSymmetricTruncate z
  have hnear := ht.eventually ((hU1.inter hU2).mem_nhds ⟨hz1,hz2'⟩)
  have hevent : (fun S => G1 (c S)) =ᶠ[atTop] (fun S => G2 (c S)) := by
    filter_upwards [hnear] with S hS
    have hrealc : deletedL2Conjugation (c S) = c S := deletedSymmetricTruncate_real S z hJz
    have h1 := hd1 (c S) hS.1
    have h2 := hd2 (c S) hS.2
    have htarget : D.signed (L (G1 (c S))) = D.signed (L (G2 (c S))) := h1.2.2.1.trans h2.2.2.1.symm
    have hreg : Memℓp (fun j => (Weight.sobolev (1/2) j : ℂ)*(D.signed (L (G1 (c S)))).val j) 2 := by
      rw [h1.2.2.1]
      exact deletedSymmetricTruncate_weighted_mem S z (Weight.sobolev (-1/2)) (Weight.sobolev (1/2))
    have hh := D.real_meanZero_injective_of_regular_target (L (G1 (c S))) (L (G2 (c S)))
      (h1.2.2.2 hrealc) (h2.2.2.2 hrealc)
      (WeightedCoeff.meanZeroWeightedLift_zero _ _) (WeightedCoeff.meanZeroWeightedLift_zero _ _) htarget hreg
    have hproj := congrArg (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1))) hh
    simpa only [L,WeightedCoeff.meanZeroWeightedProjection_lift] using hproj
  have hlim1 : Tendsto (fun S => G1 (c S)) atTop (𝓝 a) := by
    have h := ((hG1.continuousOn.continuousAt (hU1.mem_nhds hz1)).tendsto).comp ht
    simpa only [z,hG1z,Function.comp_def] using h
  have hlim2 : Tendsto (fun S => G2 (c S)) atTop (𝓝 b) := by
    have h := ((hG2.continuousOn.continuousAt (hU2.mem_nhds hz2')).tendsto).comp ht
    simpa only [hG2z',Function.comp_def] using h
  exact tendsto_nhds_unique (hlim1.congr' hevent) hlim2

/-- The actual global signed map is injective on the ENTIRE real
mean-zero HminusOne space, including all non-L2 sources and closed gaps. -/
theorem signed_injective_real_meanZero (D : GlobalRoughAbelianForwardData)
    (q1 q2 : PeriodOneHminusOne) (hr1 : IsRealPeriodOneHminusOne q1) (hr2 : IsRealPeriodOneHminusOne q2)
    (hm1 : q1.val 0 = 0) (hm2 : q2.val 0 = 0) (he : D.signed q1 = D.signed q2) : q1 = q2 := by
  let P := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1))
  have h1 := WeightedCoeff.meanZeroWeightedLift_projection (Weight.sobolev (-1)) q1 hm1
  have h2 := WeightedCoeff.meanZeroWeightedLift_projection (Weight.sobolev (-1)) q2 hm2
  have ha : P q1 = P q2 := D.meanZeroForward_injective_on_real (P q1) (P q2)
    (by rwa [h1]) (by rwa [h2]) (by
      change WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
        (D.signed (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (P q1))) =
        WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
          (D.signed (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (P q2)))
      rw [h1,h2,he])
  have h := congrArg (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))) ha
  simpa only [P,h1,h2] using h

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
