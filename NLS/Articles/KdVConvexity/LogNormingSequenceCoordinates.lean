import NLS.Articles.KdVConvexity.DirichletSequenceCoordinates
import NLS.KdV.HillHminusOneDirichletAntiNorming
import NLS.ZakharovShabat.SourceDirichletAntiSamplesAnalytic
import NLS.SequenceSpaces.ArsinhSuperposition

/-! # Actual logarithmic Dirichlet norming sequences are locally Hilbert analytic

Signed positive-index anti-discriminant samples form an analytic ell2
sequence. The principal inverse-sinh superposition recovers every actual
real norming logarithm on one complex neighborhood, including low indices.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.KdV NLS.ZakharovShabat

def dirichletHalfSignSymbol : Coeff ⊤ :=
  ⟨fun k => (-1 : ℂ)^(actionIndexEquiv k : ℕ)/2,memℓp_infty ⟨1,by
    rintro _ ⟨k,rfl⟩
    simp only [norm_div,norm_pow,norm_neg,norm_one,one_pow,norm_ofNat]
    norm_num⟩⟩

def signedDirichletAntiSamples : CoeffPair 2 → Coeff 2 := fun φ =>
  Coeff.multiplierCLM dirichletHalfSignSymbol
    (Coeff.hilbertSampleCLM positiveDirichletIndex (sourceDirichletAntiDiscriminantSamples (by simp) (by norm_num) φ))

@[simp] theorem signedDirichletAntiSamples_apply (φ : CoeffPair 2) (k : ℤ) :
    signedDirichletAntiSamples φ k = (-1 : ℂ)^(actionIndexEquiv k : ℕ)*
      sourceAntiDiscriminantCandidate (by simp) (by norm_num) φ
        (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ (actionIndexEquiv k : ℤ))/2 := by
  simp only [signedDirichletAntiSamples,Coeff.multiplierCLM_apply,Coeff.multiplier_apply,
    dirichletHalfSignSymbol,Coeff.hilbertSampleCLM_apply,positiveDirichletIndex_apply,
    sourceDirichletAntiDiscriminantSamples_apply]
  ring

theorem analyticOnNhd_signedDirichletAntiSamples {W : Set (CoeffPair 2)}
    (hanti : AnalyticOnNhd ℂ (sourceDirichletAntiDiscriminantSamples (by simp) (by norm_num)) W) :
    AnalyticOnNhd ℂ signedDirichletAntiSamples W := by
  intro p hp
  exact ((Coeff.multiplierCLM (p := 2) dirichletHalfSignSymbol).analyticAt _).comp
    (((Coeff.hilbertSampleCLM positiveDirichletIndex).analyticAt _).comp (hanti p hp))

theorem signedDirichletAntiSamples_eq_sinh (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (hr : IsRealPeriodOneHminusOne q)
    (c : ℝ) (hc : C.energyShift = (c : ℂ)^2)
    (hreal : star (C.physicalProfile q) = C.physicalProfile q) (k : ℤ) :
    signedDirichletAntiSamples (hillDirichletMiuraSource (C.lift q)) k =
      (Real.sinh (hillHminusDirichletLogNorming q hr (actionIndexEquiv k)) : ℂ) := by
  rw [signedDirichletAntiSamples_apply,
    C.dirichlet_antiDiscriminant_eq_norming q hq hr c hc hreal]
  exact signed_half_norming_difference_eq_sinh q hr (actionIndexEquiv k)

theorem exists_local_analytic_Dirichlet_log_norming
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ V : Set PeriodOneHminusOne, ∃ K : PeriodOneHminusOne → Coeff 2,
      IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ K V ∧
      ∀ p ∈ V, ∀ hp : IsRealPeriodOneHminusOne p, ∀ n : ℕ+,
        K p (actionIndexEquiv.symm n) = (hillHminusDirichletLogNorming p hp n : ℂ) := by
  obtain ⟨C,hqC,c,_,hc,hreal⟩ := exists_hillHminus_real_Miura_chart q hr
  let F : PeriodOneHminusOne → CoeffPair 2 := fun p => hillDirichletMiuraSource (C.lift p)
  have hF : AnalyticOnNhd ℂ F C.domain := fun p hp =>
    (hillDirichletMiuraSource.analyticAt _).comp (C.lift_analytic p hp)
  obtain ⟨W,hW,hrealW,hanti⟩ := exists_sourceDirichletAntiDiscriminantSamples_analytic_common_domain
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)
  let V0 := C.domain ∩ F ⁻¹' W
  have hV0 : IsOpen V0 := hF.continuousOn.isOpen_inter_preimage C.domain_open hW
  have hqV0 : q ∈ V0 := ⟨hqC,hrealW (C.dirichlet_source_real q (hreal q hqC hr))⟩
  let A : PeriodOneHminusOne → Coeff 2 := fun p => signedDirichletAntiSamples (F p)
  have hA : AnalyticOnNhd ℂ A V0 := fun p hp =>
    ((analyticOnNhd_signedDirichletAntiSamples hanti) _ hp.2).comp (f := F) (hF p hp.1)
  have hrec (p : PeriodOneHminusOne) (hp : p ∈ V0) (hpr : IsRealPeriodOneHminusOne p) (k : ℤ) :
      A p k = (Real.sinh (hillHminusDirichletLogNorming p hpr (actionIndexEquiv k)) : ℂ) :=
    signedDirichletAntiSamples_eq_sinh C p hp.1 hpr c hc (hreal p hp.1 hpr) k
  obtain ⟨V,K,hV,hqV,hsub,hK,hval⟩ := Coeff.exists_local_analytic_arsinhSuperposition_comp
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) A V0 hV0 q hqV0 hA
    (by intro k; rw [hrec q hqV0 hr k]; rfl)
  refine ⟨V,K,hV,hqV,hK,?_⟩
  intro p hp hpr n
  rw [hval p hp,hrec p (hsub hp) hpr,Equiv.apply_symm_apply,
    NLS.ComplexAnalysis.realArsinhExtension_ofReal,Real.arsinh_sinh]

end NLS.Articles.KdVConvexity
