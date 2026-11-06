import NLS.KdV.HillMeanZeroComplexDecomposition
import NLS.KdV.HillGardnerOriginalHilbertDirection
import NLS.KdV.HillHminusPhysicalConjugateDerivative

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

/-- The FULL original Gardner matrix produces literal real mean-zero L2
preimages of every scalar real and imaginary coordinate, at EVERY source.
The original physical matching and all closed gaps are retained. -/
theorem exists_hillOriginalCartesian_basis_directions
    (q : hillRealMeanZeroSourceSubmodule)
    (Z : Bool → ℕ+ → PeriodOneHminusOne → ℂ)
    (hZ : ∀ (σ : Bool) (n : ℕ+),
      AnalyticAt ℂ (Z σ n) (hillOriginalHminusSource q.val.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q.val.val,q.val.property⟩ : RealPeriodOneHillPotential),
        Z σ n (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p)
    (m : ℕ+) :
    ∃ a b : hillRealMeanZeroSourceSubmodule, ∀ n : ℕ+,
      (fderiv ℂ (Z true n) (hillOriginalHminusSource q.val.val))
          (hillOriginalRealHminusInclusion a.val) =
        I*(if (n : ℕ) = (m : ℕ) then 1 else 0) ∧
      (fderiv ℂ (Z true n) (hillOriginalHminusSource q.val.val))
          (hillOriginalRealHminusInclusion b.val) =
        (if (n : ℕ) = (m : ℕ) then 1 else 0) := by
  let Q : RealPeriodOneHillPotential := ⟨q.val.val,q.val.property⟩
  let x := hillOriginalHminusSource q.val.val
  let M := fderiv ℂ (Z false m) x
  let v := hillGardnerOriginalHilbertDirection M
  obtain ⟨a,b,hab⟩ := exists_hillMeanZeroReal_complex_decomposition v
    (hillGardnerOriginalHilbertDirection_even M) (hillGardnerOriginalHilbertDirection_mean_zero M)
  refine ⟨a,b,?_⟩
  intro n
  have hmean : Q.val.val 0 = 0 := (mem_hillRealMeanZeroSourceSubmodule q.val).mp q.property
  have hP := hillSignedCartesians_hminus_Gardner_original_matrix Q hmean n m true false
    (Z true n) (Z false m) (hZ true n).1 (hZ false m).1 (hZ true n).2 (hZ false m).2
  have hN := hillSignedCartesians_hminus_Gardner_original_matrix Q hmean n m false false
    (Z false n) (Z false m) (hZ false n).1 (hZ false m).1 (hZ false n).2 (hZ false m).2
  have hPV : (fderiv ℂ (Z true n) x) (hillOriginalHminusSource v) =
      (2*I)*(if (n : ℕ) = (m : ℕ) then 1 else 0) := by
    rw [hillGardnerOriginalHilbertDirection_source,NLS.Poisson.apply_gardnerHamiltonianDirection]
    exact hP
  have hNV : (fderiv ℂ (Z false n) x) (hillOriginalHminusSource v) = 0 := by
    rw [hillGardnerOriginalHilbertDirection_source,NLS.Poisson.apply_gardnerHamiltonianDirection]
    have he : hillOriginalComplexGardnerMatrixEntry false false n m = 0 := by
      simp [hillOriginalComplexGardnerMatrixEntry]
    rw [he] at hN
    exact hN
  have hconj (h : hillRealMeanZeroSourceSubmodule) :
      (fderiv ℂ (Z false n) x) (hillOriginalRealHminusInclusion h.val) =
        conj ((fderiv ℂ (Z true n) x) (hillOriginalRealHminusInclusion h.val)) := by
    apply hillHminusPhysicalGerm_fderiv_conj_real_source q.val (Z true n) (Z false n)
      (hZ true n).1 (hZ false n).1 _ h.val
    filter_upwards [(hZ true n).2,(hZ false n).2] with p hp hn
    simp only [hp,hn,hillSignedSpectralCartesian,ite_true,Bool.false_eq_true,ite_false]
  rw [hab,map_add,map_smul,map_add,map_smul] at hPV hNV
  change (fderiv ℂ (Z true n) x) (hillOriginalRealHminusInclusion a.val)+
      I*(fderiv ℂ (Z true n) x) (hillOriginalRealHminusInclusion b.val) = _ at hPV
  change (fderiv ℂ (Z false n) x) (hillOriginalRealHminusInclusion a.val)+
      I*(fderiv ℂ (Z false n) x) (hillOriginalRealHminusInclusion b.val) = 0 at hNV
  rw [hconj a,hconj b] at hNV
  have hNVc := congrArg conj hNV
  simp only [map_add,map_mul,conj_I,Complex.conj_conj,map_zero] at hNVc
  by_cases he : (n : ℕ) = (m : ℕ)
  · rw [if_pos he,mul_one] at hPV ⊢
    constructor
    · linear_combination (1/2 : ℂ)*hPV+(1/2 : ℂ)*hNVc
    · apply mul_left_cancel₀ I_ne_zero
      linear_combination (1/2 : ℂ)*hPV-(1/2 : ℂ)*hNVc
  · rw [if_neg he,mul_zero] at hPV ⊢
    constructor
    · linear_combination (1/2 : ℂ)*hPV+(1/2 : ℂ)*hNVc
    · apply mul_left_cancel₀ I_ne_zero
      linear_combination (1/2 : ℂ)*hPV-(1/2 : ℂ)*hNVc

end NLS.KdV
