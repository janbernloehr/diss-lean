import NLS.KdV.HillHminusRealPhysicalChart
import NLS.KdV.HillHminusOneDirichletAntiNorming
import NLS.ZakharovShabat.SourceDirichletAntiSamplesAnalytic
import NLS.SequenceSpaces.ArsinhSuperposition

/-! # Actual positive logarithmic norming data in the native Hilbert norm -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.ZakharovShabat

def hillPositiveHalfSign : Coeff ⊤ :=
  ⟨fun j => if 0 < j then (-1 : ℂ)^j.natAbs/2 else 0,memℓp_infty ⟨1,by
    rintro _ ⟨j,rfl⟩
    change ‖if 0 < j then (-1 : ℂ)^j.natAbs/2 else 0‖ ≤ 1
    split_ifs <;> norm_num [norm_div,norm_pow]⟩⟩

def hillPositiveDirichletSinhSamples (φ : CoeffPair 2) : Coeff 2 :=
  Coeff.multiplierCLM hillPositiveHalfSign
    (sourceDirichletAntiDiscriminantSamples (by simp) (by norm_num) φ)

theorem hillPositiveDirichletSinhSamples_positive (φ : CoeffPair 2) (n : ℕ+) :
    hillPositiveDirichletSinhSamples φ (n : ℤ) = (-1 : ℂ)^(n : ℕ)*
      sourceAntiDiscriminantCandidate (by simp) (by norm_num) φ
        (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ (n : ℤ))/2 := by
  simp only [hillPositiveDirichletSinhSamples,Coeff.multiplierCLM_apply,Coeff.multiplier_apply,
    hillPositiveHalfSign,if_pos (show 0 < (n : ℤ) by exact_mod_cast n.property),
    Int.natAbs_natCast,sourceDirichletAntiDiscriminantSamples_apply]
  ring

theorem hillPositiveDirichletSinhSamples_nonpositive (φ : CoeffPair 2) (j : ℤ) (hj : j ≤ 0) :
    hillPositiveDirichletSinhSamples φ j = 0 := by
  simp only [hillPositiveDirichletSinhSamples,Coeff.multiplierCLM_apply,Coeff.multiplier_apply,
    hillPositiveHalfSign,if_neg (not_lt.mpr hj),zero_mul]

theorem analyticOnNhd_hillPositiveDirichletSinhSamples {W : Set (CoeffPair 2)}
    (hS : AnalyticOnNhd ℂ (sourceDirichletAntiDiscriminantSamples (by simp) (by norm_num)) W) :
    AnalyticOnNhd ℂ hillPositiveDirichletSinhSamples W := fun p hp =>
  ((Coeff.multiplierCLM (p := 2) hillPositiveHalfSign).analyticAt _).comp (hS p hp)

theorem exists_hillHminus_native_dirichlet_norming_sequences
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ V : Set PeriodOneHminusOne, ∃ K S : PeriodOneHminusOne → Coeff 2,
      IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ K V ∧ AnalyticOnNhd ℂ S V ∧
      (∀ p ∈ V, ∀ hp : IsRealPeriodOneHminusOne p, ∀ n : ℕ+,
        K p (n : ℤ) = (hillHminusDirichletLogNorming p hp n : ℂ) ∧
        S p (n : ℤ) = (Real.sinh (hillHminusDirichletLogNorming p hp n) : ℂ)) ∧
      ∀ p ∈ V, ∀ j : ℤ, j ≤ 0 → K p j = 0 ∧ S p j = 0 := by
  obtain ⟨C,hqC,c,_hc,hc,hreal⟩ := exists_hillHminus_real_Miura_chart q hr
  let F : PeriodOneHminusOne → CoeffPair 2 := fun p => hillDirichletMiuraSource (C.lift p)
  have hF : AnalyticOnNhd ℂ F C.domain := fun p hp =>
    (hillDirichletMiuraSource.analyticAt _).comp (C.lift_analytic p hp)
  obtain ⟨W,hW,hrealW,hanti⟩ := exists_sourceDirichletAntiDiscriminantSamples_analytic_common_domain
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)
  let V0 := C.domain ∩ F ⁻¹' W
  have hV0 : IsOpen V0 := hF.continuousOn.isOpen_inter_preimage C.domain_open hW
  have hqV0 : q ∈ V0 := ⟨hqC,hrealW (C.dirichlet_source_real q (hreal q hqC hr))⟩
  let S : PeriodOneHminusOne → Coeff 2 := fun p => hillPositiveDirichletSinhSamples (F p)
  have hS : AnalyticOnNhd ℂ S V0 := fun p hp =>
    (analyticOnNhd_hillPositiveDirichletSinhSamples hanti _ hp.2).comp (f := F) (hF p hp.1)
  have hrec (p : PeriodOneHminusOne) (hp : p ∈ V0) (hpr : IsRealPeriodOneHminusOne p) (n : ℕ+) :
      S p (n : ℤ) = (Real.sinh (hillHminusDirichletLogNorming p hpr n) : ℂ) := by
    rw [hillPositiveDirichletSinhSamples_positive,
      C.dirichlet_antiDiscriminant_eq_norming p hp.1 hpr c hc (hreal p hp.1 hpr) n]
    exact signed_half_norming_difference_eq_sinh p hpr n
  obtain ⟨V,K,hV,hqV,hsub,hK,hval⟩ := Coeff.exists_local_analytic_arsinhSuperposition_comp
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) S V0 hV0 q hqV0 hS (by
      intro j
      by_cases hj : 0 < j
      · let n : ℕ+ := ⟨j.toNat,by omega⟩
        have he : j = (n : ℤ) := by
          change j = (j.toNat : ℤ)
          exact (Int.toNat_of_nonneg hj.le).symm
        rw [he,hrec q hqV0 hr]
        rfl
      · rw [hillPositiveDirichletSinhSamples_nonpositive (F q) j (not_lt.mp hj)]
        rfl)
  refine ⟨V,K,S,hV,hqV,hK,hS.mono hsub,?_,?_⟩
  · intro p hp hpr n
    refine ⟨?_,hrec p (hsub hp) hpr n⟩
    rw [hval p hp,hrec p (hsub hp) hpr n,
      NLS.ComplexAnalysis.realArsinhExtension_ofReal,Real.arsinh_sinh]
  · intro p hp j hj
    have hz : S p j = 0 := hillPositiveDirichletSinhSamples_nonpositive (F p) j hj
    refine ⟨?_,hz⟩
    rw [hval p hp,hz]
    exact NLS.ComplexAnalysis.realArsinhExtension_ofReal 0 |>.trans (by simp)

end NLS.KdV
