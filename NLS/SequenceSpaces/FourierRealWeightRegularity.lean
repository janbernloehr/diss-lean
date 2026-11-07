import NLS.SequenceSpaces.FourierRealZeroSpatialGenerator

/-! Exact weighted membership realizes the same physical Fourier
sequence in a stronger real mean-zero Banach space. -/
noncomputable section
namespace NLS.WeightedCoeff

theorem fourierRealZeroFullProjection_apply (v : Weight) (hv : ∀ k, v (-k)=v k)
    (a : WeightedCoeff v 2) (k : ℤ) :
    (fourierRealZeroFullProjection v hv a).val.val.val k =
      (1/2:ℂ)*((if k=0 then 0 else a.val k)+
        (starRingEnd ℂ) (if -k=0 then 0 else a.val (-k))) := by
  change (zeroModeSymmetricPartCLM v hv (zeroModeProjection v a)).val.val k = _
  rw [zeroModeSymmetricPartCLM_apply]
  change (1/2:ℂ)*((eraseZeroModeCLM v a).val k+
    (starRingEnd ℂ) ((eraseZeroModeCLM v a).val (-k))) = _
  rw [eraseZeroModeCLM_apply, eraseZeroModeCLM_apply]

def physicalWeightRealization (w v : Weight) (hv : ∀ k, v (-k)=v k) (q : fourierRealZeroSubmodule w 2)
    (hq : Memℓp (fun k => (v k:ℂ)*q.val.val.val k) 2) : fourierRealZeroSubmodule v 2 :=
  fourierRealZeroFullProjection v hv ⟨q.val.val.val,hq⟩

theorem physicalWeightRealization_apply (w v : Weight) (hv : ∀ k, v (-k)=v k)
    (q : fourierRealZeroSubmodule w 2)
    (hq : Memℓp (fun k => (v k:ℂ)*q.val.val.val k) 2) (k : ℤ) :
    (physicalWeightRealization w v hv q hq).val.val.val k = q.val.val.val k := by
  have hh := fourierRealZeroFullProjection_apply v hv
    (⟨q.val.val.val,hq⟩ : WeightedCoeff v 2) k
  change (physicalWeightRealization w v hv q hq).val.val.val k =
    (1/2:ℂ)*((if k=0 then 0 else q.val.val.val k)+
      (starRingEnd ℂ) (if -k=0 then 0 else q.val.val.val (-k))) at hh
  apply hh.trans
  by_cases hk : k=0
  · subst k
    simp only [neg_zero, ite_true, map_zero, add_zero, mul_zero]
    exact (show q.val.val.val 0 = 0 from q.val.property).symm
  · simp only [if_neg hk, if_neg (neg_ne_zero.mpr hk), q.property k, Complex.conj_conj]
    ring

theorem exists_physicalWeightRealization (w v : Weight) (hv : ∀ k, v (-k)=v k)
    (I : fourierRealZeroSubmodule v 2 →L[ℝ] fourierRealZeroSubmodule w 2)
    (hI : ∀ u k, (I u).val.val.val k = u.val.val.val k)
    (q : fourierRealZeroSubmodule w 2)
    (hq : Memℓp (fun k => (v k:ℂ)*q.val.val.val k) 2) :
    ∃ u : fourierRealZeroSubmodule v 2, I u = q := by
  refine ⟨physicalWeightRealization w v hv q hq,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  exact (hI _ k).trans (physicalWeightRealization_apply w v hv q hq k)

end NLS.WeightedCoeff
