import NLS.Articles.KdVKdV2Frequencies.FiniteActionHamiltonianDifferential
import NLS.Articles.KdVKdV2Frequencies.GlobalRawSobolevDiffeomorphisms
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianOrigin

/-! # Actual physical native first variations at finite-action sources

The source action sequence is the literal signed product of the SAME global
Birkhoff map. Its native Banach differential and the independent physical
H_m have an exact finite frequency expansion at every finite-action source.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The already proved actual native restriction of the SAME original map. -/
def rawIntegerForwardHomeomorph (D : GlobalRoughAbelianForwardData) (m : ℕ) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ)) ≃ₜ
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2)) :=
  Classical.choose (D.exists_global_raw_real_analytic_sobolev_diffeomorphism (m : ℝ)
    (by have := Nat.cast_nonneg (α := ℝ) m; linarith))

theorem rawIntegerForwardHomeomorph_analytic (D : GlobalRoughAbelianForwardData) (m : ℕ) :
    AnalyticOnNhd ℝ (fun q => D.rawIntegerForwardHomeomorph m q) univ :=
  (Classical.choose_spec (D.exists_global_raw_real_analytic_sobolev_diffeomorphism (m : ℝ)
    (by have := Nat.cast_nonneg (α := ℝ) m; linarith))).1

theorem rawIntegerForwardHomeomorph_symm_analytic (D : GlobalRoughAbelianForwardData) (m : ℕ) :
    AnalyticOnNhd ℝ (D.rawIntegerForwardHomeomorph m).symm univ :=
  (Classical.choose_spec (D.exists_global_raw_real_analytic_sobolev_diffeomorphism (m : ℝ)
    (by have := Nat.cast_nonneg (α := ℝ) m; linarith))).2.1

/-- Every signed native coefficient belongs to the already fixed global rough map. -/
theorem rawIntegerForwardHomeomorph_signed (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
    WeightedCoeff.sobolevInclusion
      (by have := Nat.cast_nonneg (α := ℝ) m; linarith : (-1/2 : ℝ)≤(m : ℝ)+1/2)
      (D.rawIntegerForwardHomeomorph m q).val = D.signed (nativeHillSource m q.val) :=
  (Classical.choose_spec (D.exists_global_raw_real_analytic_sobolev_diffeomorphism (m : ℝ)
    (by have := Nat.cast_nonneg (α := ℝ) m; linarith))).2.2 q

/-- No new inverse is introduced by the native restriction. -/
theorem rawIntegerForwardHomeomorph_inverse_apply (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
    D.rawIntegerInverseSource m (D.rawIntegerForwardHomeomorph m q) = q.val :=
  D.rawIntegerInverseSource_eq_of_signed_eq m q.val q.property.1 q.property.2 _
    (D.rawIntegerForwardHomeomorph_signed m q).symm

theorem rawIntegerForwardHomeomorph_symm_val (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) :
    ((D.rawIntegerForwardHomeomorph m).symm z).val = D.rawIntegerInverseSource m z := by
  have h := D.rawIntegerForwardHomeomorph_inverse_apply m ((D.rawIntegerForwardHomeomorph m).symm z)
  rw [(D.rawIntegerForwardHomeomorph m).apply_symm_apply] at h
  exact h.symm

/-- The complete actual original source action sequence in the exact native weighted norm. -/
def nativeSourceActionSequence (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
    WeightedCoeff (Weight.sobolev r) 1 :=
  sobolevSignedActionSequence r ((m : ℝ)+1/2) hrs (D.rawIntegerForwardHomeomorph m q)

/-- Literal raw products of the SAME original signed global map, not a
newly normalized or auxiliary action coordinate. -/
theorem nativeSourceActionSequence_apply (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℤ) :
    (D.nativeSourceActionSequence m r hrs q).val n = if 0<n then
      (D.signed (nativeHillSource m q.val)).val n*(D.signed (nativeHillSource m q.val)).val (-n) else 0 := by
  have he (j : ℤ) : (D.rawIntegerForwardHomeomorph m q).val.val j =
      (D.signed (nativeHillSource m q.val)).val j := by
    have h := congrArg (fun a => a.val j) (D.rawIntegerForwardHomeomorph_signed m q)
    simpa only [WeightedCoeff.sobolevInclusion_apply] using! h
  unfold nativeSourceActionSequence
  rw [sobolevSignedActionSequence_apply,he n,he (-n)]

theorem nativeSourceActionSequence_analytic (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2)) :
    AnalyticOnNhd ℝ (D.nativeSourceActionSequence m r hrs) univ := by
  intro q _
  exact (analyticOnNhd_sobolevSignedActionSequence r ((m : ℝ)+1/2) hrs _ (mem_univ _)).comp
    (D.rawIntegerForwardHomeomorph_analytic m q (mem_univ _))

/-- The source derivative is the actual native Banach chain rule. -/
theorem hasFDerivAt_nativeSourceActionSequence (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
    HasFDerivAt (D.nativeSourceActionSequence m r hrs)
      ((sobolevRealSignedActionJacobian r ((m : ℝ)+1/2) hrs (D.rawIntegerForwardHomeomorph m q)).comp
        (fderiv ℝ (fun u => D.rawIntegerForwardHomeomorph m u) q)) q := by
  exact (hasFDerivAt_sobolevSignedActionSequence r ((m : ℝ)+1/2) hrs _).comp q
    (D.rawIntegerForwardHomeomorph_analytic m q (mem_univ _)).differentiableAt.hasFDerivAt

/-- Every original action differential has its exact signed coefficient formula. -/
theorem nativeSourceActionSequence_fderiv_apply (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (q h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℤ) :
    ((fderiv ℝ (D.nativeSourceActionSequence m r hrs) q) h).val n = if 0<n then
      (D.rawIntegerForwardHomeomorph m q).val.val n*
        (((fderiv ℝ (fun u => D.rawIntegerForwardHomeomorph m u) q) h).val).val (-n)+
      (((fderiv ℝ (fun u => D.rawIntegerForwardHomeomorph m u) q) h).val).val n*
        (D.rawIntegerForwardHomeomorph m q).val.val (-n) else 0 := by
  have hd := D.hasFDerivAt_nativeSourceActionSequence m r hrs q
  have he := congrArg (fun L => (L h).val n) hd.fderiv
  simpa only [ContinuousLinearMap.comp_apply,sobolevRealSignedActionJacobian_apply] using! he

/-- The independent physical hierarchy member restricted to the original real mean-zero source. -/
def nativeSourceHierarchyHamiltonian (_D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) : ℂ :=
  nativeHillHierarchyHamiltonian m q.val

/-- Exact physical source recovery through this SAME actual native restriction. -/
theorem complexBirkhoffHierarchyHamiltonian_forward (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
    D.complexBirkhoffHierarchyHamiltonian m (D.rawIntegerForwardHomeomorph m q) =
      D.nativeSourceHierarchyHamiltonian m q := by
  unfold complexBirkhoffHierarchyHamiltonian nativeSourceHierarchyHamiltonian
  rw [D.rawIntegerForwardHomeomorph_inverse_apply]

/-- The actual original physical H_m first variation at a finite-action source
is the FINITE sum of its intrinsic frequencies times the original action
first variations. No Hamiltonian frequency or spectral identity is assumed. -/
theorem nativeSourceHierarchyHamiltonian_fderiv_finite_actions
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → (D.nativeSourceActionSequence m r hrs q).val (n : ℤ) = 0)
    (h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
    (fderiv ℝ (D.nativeSourceHierarchyHamiltonian m) q) h = ∑ n ∈ S,
      ((fderiv ℝ (D.nativeSourceActionSequence m r hrs) q) h).val (n : ℤ)*
        (D.originalHierarchyFrequency m r hrs
          (originalPositiveActions m r hrs (D.rawIntegerForwardHomeomorph m q)) n : ℂ) := by
  obtain ⟨F⟩ := nonempty_originalHierarchyActionFactor D m r hrs
  let z := D.rawIntegerForwardHomeomorph m q
  let v := (fderiv ℝ (fun u => D.rawIntegerForwardHomeomorph m u) q) h
  have hdC := D.hasFDerivAt_complexBirkhoffHierarchyHamiltonian_actions m r hrs F z
  have hdE := (D.rawIntegerForwardHomeomorph_analytic m q (mem_univ _)).differentiableAt.hasFDerivAt
  have hd := hdC.comp q hdE
  have hefun : D.complexBirkhoffHierarchyHamiltonian m ∘ (D.rawIntegerForwardHomeomorph m).toEquiv.toFun =
      D.nativeSourceHierarchyHamiltonian m := funext (D.complexBirkhoffHierarchyHamiltonian_forward m)
  rw [hefun] at hd
  have hsource : (fderiv ℝ (D.nativeSourceHierarchyHamiltonian m) q) h =
      (fderiv ℝ (D.complexBirkhoffHierarchyHamiltonian m) z) v := by
    have hleft := congrArg (fun L => L h) hd.fderiv
    have hright := congrArg (fun L => L v) hdC.fderiv
    exact hleft.trans hright.symm
  rw [hsource,D.fderiv_complexBirkhoffHierarchyHamiltonian_finite_actions m r hrs z S hq v]
  apply Finset.sum_congr rfl
  intro n _
  rw [D.nativeSourceActionSequence_fderiv_apply m r hrs q h (n : ℤ),
    if_pos (by exact_mod_cast n.pos : (0 : ℤ)<n)]

/-- The finite-action first variation for the exact printed physical H1. -/
theorem nativeKdVHamiltonian_fderiv_finite_actions (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → (D.nativeSourceActionSequence 1 3 (by norm_num) q).val (n : ℤ) = 0)
    (h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) :
    (fderiv ℝ (fun u : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)) => nativeKdVHamiltonian u.val) q) h =
      ∑ n ∈ S, ((fderiv ℝ (D.nativeSourceActionSequence 1 3 (by norm_num)) q) h).val (n : ℤ)*
        (D.originalKdVFrequency (originalPositiveActions 1 3 (by norm_num) (D.rawIntegerForwardHomeomorph 1 q)) n : ℂ) := by
  have he : D.nativeSourceHierarchyHamiltonian 1 =
      (fun u : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)) => nativeKdVHamiltonian u.val) :=
    funext (fun u => nativeHillHierarchyHamiltonian_one u.val)
  simpa only [he,originalKdVFrequency] using
    D.nativeSourceHierarchyHamiltonian_fderiv_finite_actions 1 3 (by norm_num) q S hq h

/-- The finite-action first variation for the exact printed physical H2. -/
theorem nativeKdV2Hamiltonian_fderiv_finite_actions (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → (D.nativeSourceActionSequence 2 5 (by norm_num) q).val (n : ℤ) = 0)
    (h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ))) :
    (fderiv ℝ (fun u : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ)) => nativeKdV2Hamiltonian u.val) q) h =
      ∑ n ∈ S, ((fderiv ℝ (D.nativeSourceActionSequence 2 5 (by norm_num)) q) h).val (n : ℤ)*
        (D.originalKdV2Frequency (originalPositiveActions 2 5 (by norm_num) (D.rawIntegerForwardHomeomorph 2 q)) n : ℂ) := by
  have he : D.nativeSourceHierarchyHamiltonian 2 =
      (fun u : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ)) => nativeKdV2Hamiltonian u.val) :=
    funext (fun u => nativeHillHierarchyHamiltonian_two u.val)
  simpa only [he,originalKdV2Frequency] using
    D.nativeSourceHierarchyHamiltonian_fderiv_finite_actions 2 5 (by norm_num) q S hq h

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
