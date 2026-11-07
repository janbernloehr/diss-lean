import NLS.Articles.KdVPseudomeasures.OriginalHillWienerPhysicalModels
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeSignedGardner
import NLS.FunctionalAnalysis.AnalyticLinearEquivalenceTransport

/-! Original Theorem 5.1 on the ENTIRE physical real mean-zero
period-one Wiener source at EVERY nonnegative integer order. The
original distribution, every actual native Birkhoff coefficient,
ordinary weighted ell-one norm topologies, analytic inverse and
signed Gardner normalization are all retained. -/
noncomputable section
open Complex NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

private def nativeWienerEquiv (N : ℕ) :
    fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1 ≃
      fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder (1/2) N)) 1 :=
  Classical.choose (hillWienerBirkhoffDiffeomorphism_all N)

private theorem nativeWienerEquiv_raw (N : ℕ)
    (q : fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1) (k : ℤ) :
    (nativeWienerEquiv N q).val.val.val k = (hillRealSignedMap (hillWienerSourceInclusion N q)).val.val.val k :=
  (Classical.choose_spec (hillWienerBirkhoffDiffeomorphism_all N)).1 q k

private theorem analytic_nativeWienerEquiv (N : ℕ)
    (q : fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1) :
    AnalyticAt ℝ (nativeWienerEquiv N) q :=
  (Classical.choose_spec (hillWienerBirkhoffDiffeomorphism_all N)).2.1 q

private theorem analytic_nativeWienerEquiv_symm (N : ℕ)
    (z : fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder (1/2) N)) 1) :
    AnalyticAt ℝ (nativeWienerEquiv N).symm z :=
  (Classical.choose_spec (hillWienerBirkhoffDiffeomorphism_all N)).2.2 z

def originalHillWienerEquiv (N : ℕ) : OriginalWienerPotential N ≃ OriginalWienerTarget N :=
  (originalWienerSourceCoefficients N).toEquiv.trans
    ((nativeWienerEquiv N).trans (originalWienerTargetCoefficients N).symm.toEquiv)

theorem originalHillWienerEquiv_apply (N : ℕ) (q : OriginalWienerPotential N) (k : ℤ) :
    (originalHillWienerEquiv N q).val.val.val k =
      (hillRealSignedMap (originalHillRealMeanZeroSource (originalWienerOriginalPotential N q))).val.val.val k := by
  change ((originalWienerTargetCoefficients N).symm (nativeWienerEquiv N (originalWienerSourceCoefficients N q))).val.val.val k = _
  rw [originalWienerTargetCoefficients_symm_apply,nativeWienerEquiv_raw,originalWienerOriginalPotential_native]
  rfl

theorem analyticAt_originalHillWienerEquiv (N : ℕ) (q : OriginalWienerPotential N) :
    AnalyticAt ℝ (originalHillWienerEquiv N) q :=
  @NLS.FunctionalAnalysis.analyticAt_linearEquiv_transport
    (OriginalWienerPotential N)
    (fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1)
    (fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder (1/2) N)) 1)
    (OriginalWienerTarget N)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance (fourierRealZeroSubmodule_normedSpace _) (fourierRealZeroSubmodule_normedSpace _)
    (fourierRealZeroSubmodule_normedSpace _)
    (originalWienerSourceCoefficients N) (originalWienerTargetCoefficients N).symm
    (nativeWienerEquiv N) q (analytic_nativeWienerEquiv N _)

theorem analyticAt_originalHillWienerEquiv_symm (N : ℕ) (z : OriginalWienerTarget N) :
    AnalyticAt ℝ (originalHillWienerEquiv N).symm z :=
  @NLS.FunctionalAnalysis.analyticAt_linearEquiv_transport
    (OriginalWienerTarget N)
    (fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder (1/2) N)) 1)
    (fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1)
    (OriginalWienerPotential N)
    inferInstance inferInstance inferInstance inferInstance
    (fourierRealZeroSubmodule_normedSpace _) (fourierRealZeroSubmodule_normedSpace _)
    (fourierRealZeroSubmodule_normedSpace _) inferInstance
    (originalWienerTargetCoefficients N) (originalWienerSourceCoefficients N).symm
    (nativeWienerEquiv N).symm z (analytic_nativeWienerEquiv_symm N _)

def sourceTheorem5_1Statement : Prop :=
  ∀ N : ℕ, ∃ e : OriginalWienerPotential N ≃ OriginalWienerTarget N,
    (∀ q, (originalWienerOriginalPotential N q).val.val = q.val.val) ∧
    (∀ q k, (e q).val.val.val k =
      (hillRealSignedMap (originalHillRealMeanZeroSource (originalWienerOriginalPotential N q))).val.val.val k) ∧
    (∀ q, AnalyticAt ℝ e q) ∧ (∀ z, AnalyticAt ℝ e.symm z) ∧
    ∀ (q : OriginalWienerPotential N) (k l : ℤ),
      hillHminusNativeGardnerBracket k l (originalPeriodOneCoefficients (originalWienerOriginalPotential N q)) =
        if k=0 then 0 else if l= -k then (if 0 < k then I else -I) else 0

theorem sourceTheorem5_1 : sourceTheorem5_1Statement := by
  intro N
  exact ⟨originalHillWienerEquiv N,originalWienerOriginalPotential_same_distribution N,
    originalHillWienerEquiv_apply N,analyticAt_originalHillWienerEquiv N,
      analyticAt_originalHillWienerEquiv_symm N,
        fun q k l => original_Hill_native_Gardner_signed_canonical k l (originalWienerOriginalPotential N q)⟩

end NLS.Articles.KdVPseudomeasures
