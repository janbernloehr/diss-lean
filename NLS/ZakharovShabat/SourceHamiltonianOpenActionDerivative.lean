import NLS.ZakharovShabat.SourceHamiltonianActionExtension
import NLS.ZakharovShabat.SourceFiniteGapHamiltonianExponent
import NLS.ZakharovShabat.SourceFiniteGapRenormalizedDerivative

/-! # Action derivatives of the actual Hamiltonian extension

The physical finite-gap action-reduction curve identifies a coordinate
of the Banach derivative of any differentiable action extension recovering
the cubic-moment Hamiltonian. The source exponents are bridged by equality
of the physical Hamiltonians, not by an assumed gradient identity.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4:ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W W₀ B X : Set (CoeffPair 4)} {t : (k : ℤ) → CoeffPair 4 → DeletedCoeff 4 k}
variable {Y P : Set (CoeffPair 2)} {u : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- At every open action of a finite-gap Hilbert source, the actual
ℓ² Hamiltonian derivative equals the renormalized physical frequency. -/
theorem sourceHamiltonian_fderiv_open_finiteGap
    (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t)
    (C : SourceAbelianMomentAtlas (by simp) (by norm_num) Y u)
    (hs : SourcePsiNormalizedComplexExtension (by simp) (by norm_num) P u)
    (H : Coeff 2 → ℂ)
    (hrec : ∀ ψ : realTypeSourceSubmodule 4,
      H (sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ.val) = A.renormalizedHamiltonian ψ.val)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0)
    (hH : DifferentiableAt ℂ H (sourceActionSequence (q := 2) (by simp) (by norm_num) t
      (realTypeSourceExponentInclusion (by norm_num : (2:ℝ≥0∞) ≤ 4) φ).val)) :
    fderiv ℂ H (sourceActionSequence (q := 2) (by simp) (by norm_num) t
      (realTypeSourceExponentInclusion (by norm_num : (2:ℝ≥0∞) ≤ 4) φ).val) (lp.single 2 n 1) =
      C.renormalizedFrequency n φ.val := by
  obtain ⟨W₂,B₂,X₂,s₂,D₂⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  let γ := D₂.hilbertActionReduction φ n
  let ψ : ℝ → realTypeSourceSubmodule 4 := fun r : ℝ => realTypeSourceExponentInclusion (by norm_num : (2:ℝ≥0∞) ≤ 4) (γ r)
  let I := fun χ : realTypeSourceSubmodule 4 => sourceActionSequence (q := 2) (by simp) (by norm_num) t χ.val
  let a := I (realTypeSourceExponentInclusion (by norm_num : (2:ℝ≥0∞) ≤ 4) φ)
  let v : Coeff 2 := lp.single 2 n 1
  have hact := sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) φ.val φ.property n
  have ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re := by
    apply lt_of_le_of_ne hact.1
    intro he
    exact hn (by simpa only [sourcePeriodicGapDisplacement_apply] using hact.2.2.mp (Complex.ext he.symm hact.2.1))
  have hi : (fun r : ℝ => I (ψ r)) =ᶠ[𝓝 0] (fun r => a - (r:ℂ) • v) := by
    filter_upwards [gt_mem_nhds ha] with r hr
    ext k
    simp only [lp.coeFn_sub,Pi.sub_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    dsimp only [I,a]
    rw [D.actionSequence_apply _ (D.real_subset (ψ r).property),
      D.actionSequence_apply _ (D.real_subset (realTypeSourceExponentInclusion (by norm_num : (2:ℝ≥0∞) ≤ 4) φ).property)]
    dsimp only [ψ,realTypeSourceExponentInclusion]
    rw [← sourceComplexAction_real_exponent (by simp) (by simp) (by norm_num) (by norm_num)
      (by norm_num : (2:ℝ≥0∞) ≤ 4) k (γ r),
      ← sourceComplexAction_real_exponent (by simp) (by simp) (by norm_num) (by norm_num)
        (by norm_num : (2:ℝ≥0∞) ≤ 4) k φ]
    rw [D₂.hilbertActionReduction_complexAction φ n k ha r hr.le]
    by_cases hkn : k = n <;> simp [v,lp.single_apply,hkn]
  have ht : HasDerivAt (fun r : ℝ => (r:ℂ)) 1 0 := by
    simpa using! (Complex.ofRealCLM.hasDerivAt (x := (0:ℝ)))
  have hI : HasDerivAt (fun r => I (ψ r)) (-v) 0 := by
    apply HasDerivAt.congr_of_eventuallyEq _ hi
    simpa using! (hasDerivAt_const (0:ℝ) a).sub (ht.smul_const v)
  have hbase : I (ψ 0) = a := by simp only [ψ,γ,D₂.hilbertActionReduction_zero,a]
  have hdH : HasFDerivAt H (fderiv ℂ H a) (I (ψ 0)) := hbase.symm ▸ hH.hasFDerivAt
  have hd := (hdH.restrictScalars ℝ).comp_hasDerivAt 0 hI
  have he : (fun r => H (I (ψ r))) = D₂.physicalActionReductionRenormalizedHamiltonian φ hf n := by
    funext r
    change H (sourceActionSequence (q := 2) (by simp) (by norm_num) t (ψ r).val) = _
    rw [hrec (ψ r)]
    have hfγ := D₂.hilbertActionReduction_mem_finiteGap φ hf n r
    have hfψ := (sourceFiniteGapLocus_exponent_iff (by simp) (by simp) (by norm_num) (by norm_num)
      (by norm_num : (2:ℝ≥0∞) ≤ 4) (γ r)).mp hfγ
    rw [A.renormalizedHamiltonian_eq_finiteGap (ψ r) hfψ]
    exact (sourceFiniteGapRenormalizedHamiltonian_real_exponent (by simp) (by simp) (by norm_num)
      (by norm_num) (by norm_num : (2:ℝ≥0∞) ≤ 4) (γ r) hfγ).symm
  dsimp only [Function.comp_def] at hd
  rw [he] at hd
  have hphys := D₂.hasDerivAt_physicalActionReductionRenormalizedHamiltonian C hs φ hf n hn
  have hval := hd.unique hphys
  change (fderiv ℂ H a) (-v) = -C.renormalizedFrequency n φ.val at hval
  rw [map_neg] at hval
  exact neg_injective hval

end NLS.ZakharovShabat
