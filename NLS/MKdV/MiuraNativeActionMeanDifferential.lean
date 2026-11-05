import NLS.MKdV.MiuraNativeActionMeanParameters
import NLS.MKdV.MiuraThetaActionDirection

/-! # Native action differentials preserve the original physical action amplitudes -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem analyticAt_miuraSobolevActionSequence (s : ℕ) (a : MiuraRealSobolevSource s) :
    AnalyticAt ℂ (miuraSobolevActionSequence s) a.val := by
  obtain ⟨U,_,ha,hF,_⟩ := exists_local_miuraSobolevActionSequence_analytic s a.val a.property
  exact hF a.val ha

theorem analyticAt_miuraNativeActionMeanMap (s : ℕ) (a : MiuraRealSobolevSource s) :
    AnalyticAt ℂ (miuraNativeActionMeanMap s) a.val :=
  (analyticAt_miuraSobolevActionSequence s a).prod ((WeightedCoeff.evalCLM (Weight.sobolev (s : ℝ)) 2 0).analyticAt a.val)

theorem fderiv_miuraSobolevActionSequence_eval_positive (s : ℕ) (a : MiuraRealSobolevSource s)
    (k : ℕ) (hk : 1 ≤ k) (v : ScalarSobolev s) :
    (fderiv ℂ (miuraSobolevActionSequence s) a.val v).val (k : ℤ) =
      fderiv ℂ (miuraL2Action k) (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val)
        (hierarchySobolevJetL2 s 0 (Nat.zero_le _) v) := by
  let J := hierarchySobolevJetL2 s 0 (Nat.zero_le s)
  let E := WeightedCoeff.evalCLM (miuraSpectralActionWeight s) 1 (k : ℤ)
  obtain ⟨U,hU,ha,hA,hcoord⟩ := exists_local_miuraSobolevActionSequence_analytic s a.val a.property
  have he : (fun b => E (miuraSobolevActionSequence s b)) =ᶠ[𝓝 a.val]
      (fun b => miuraL2Action k (J b)) := by
    filter_upwards [hU.mem_nhds ha] with b hb
    change (miuraSobolevActionSequence s b).val (k : ℤ) = _
    rw [hcoord b hb k (by omega),miuraL2Action,miuraSobolevActionSource_eq_L2_diagonal]
  have hr : ∀ j, J a.val j = conj (J a.val (-j)) := by
    intro j
    simpa only [J,hierarchySobolevJetL2_apply,pow_zero,one_mul] using! a.property j
  have hleft := E.hasFDerivAt.comp a.val (hA a.val ha).differentiableAt.hasFDerivAt
  have hright := ((analyticOnNhd_miuraL2Action k hk _ (real_mem_miuraL2ActionDomain _ hr)).differentiableAt.hasFDerivAt).comp a.val J.hasFDerivAt
  have hd := hleft.fderiv
  change fderiv ℂ (fun b => E (miuraSobolevActionSequence s b)) a.val = _ at hd
  have hrd := hright.fderiv
  change fderiv ℂ (fun b => miuraL2Action k (J b)) a.val = _ at hrd
  rw [he.fderiv_eq,hrd] at hd
  exact (congrArg (fun L : ScalarSobolev s →L[ℂ] ℂ => L v) hd).symm

theorem fderiv_miuraSobolevActionSequence_eval_nonpositive (s : ℕ) (a : MiuraRealSobolevSource s)
    (k : ℤ) (hk : ¬0 < k) (v : ScalarSobolev s) :
    (fderiv ℂ (miuraSobolevActionSequence s) a.val v).val k = 0 := by
  let E := WeightedCoeff.evalCLM (miuraSpectralActionWeight s) 1 k
  have hd := E.hasFDerivAt.comp a.val (analyticAt_miuraSobolevActionSequence s a).differentiableAt.hasFDerivAt
  have he : (fun b => E (miuraSobolevActionSequence s b)) = fun _ => 0 :=
    funext (fun b => miuraSobolevActionSequence_nonpositive s b k hk)
  change HasFDerivAt (fun b => E (miuraSobolevActionSequence s b)) _ a.val at hd
  rw [he] at hd
  exact congrArg (fun L : ScalarSobolev s →L[ℂ] ℂ => L v) (hd.unique (hasFDerivAt_const 0 a.val))

end NLS.MKdV
