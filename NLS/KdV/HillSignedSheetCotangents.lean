import NLS.KdV.HillAbelianEndpointCotangents
import NLS.KdV.HillSheetGardnerCommutation
import NLS.KdV.HillOffIndexCorrectionGardnerLimit

/-! Literal signed positive extensions of the actual sheet and
Abelian-term cotangents. Nonpositive indices and the omitted diagonal
are zero. At endpoint data each actual term lies in its sheet span. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.LpSequence
open scoped ENNReal
namespace NLS.KdV

def hillHminusSignedSheetCotangent (q : PeriodOneHminusOne) (j : ℤ) :
    PeriodOneHminusOne →L[ℂ] ℂ :=
  fderiv ℂ (fun p => positiveScalarExtension (fun m : ℕ+ => hillHminusDirichletSheet m p) j) q

theorem hillHminusSignedSheetCotangent_apply_positive (q : PeriodOneHminusOne) (m : ℕ+) :
    hillHminusSignedSheetCotangent q ((m:ℕ):ℤ)=fderiv ℂ (hillHminusDirichletSheet m) q := by
  simp only [hillHminusSignedSheetCotangent,positiveScalarExtension_apply]

theorem hillHminusSignedSheetCotangent_zero_of_not_mem_range (q : PeriodOneHminusOne)
    (j : ℤ) (hj : j ∉ range positiveEmbedding) : hillHminusSignedSheetCotangent q j=0 := by
  have he : (fun p : PeriodOneHminusOne => positiveScalarExtension (fun m : ℕ+ => hillHminusDirichletSheet m p) j) =
      (fun _ => (0:ℂ)) := funext (fun _ => positiveScalarExtension_zero_of_not_mem_range _ j hj)
  rw [hillHminusSignedSheetCotangent,he]
  exact (hasFDerivAt_const (0:ℂ) q).fderiv

theorem hillHminusSignedSheetCotangents_Gardner_commute
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) (i j : ℤ) :
    NLS.Poisson.gardnerCotangentBivector (hillHminusSignedSheetCotangent q i) (hillHminusSignedSheetCotangent q j)=0 := by
  by_cases hi : i ∈ range positiveEmbedding
  · obtain ⟨n,rfl⟩ := hi
    by_cases hj : j ∈ range positiveEmbedding
    · obtain ⟨m,rfl⟩ := hj
      change NLS.Poisson.gardnerCotangentBivector
        (hillHminusSignedSheetCotangent q ((n:ℕ):ℤ)) (hillHminusSignedSheetCotangent q ((m:ℕ):ℤ))=0
      rw [hillHminusSignedSheetCotangent_apply_positive,hillHminusSignedSheetCotangent_apply_positive]
      exact hillHminusDirichletSheets_Gardner_commute n m q hq
    · rw [hillHminusSignedSheetCotangent_zero_of_not_mem_range q j hj,map_zero]
  · rw [hillHminusSignedSheetCotangent_zero_of_not_mem_range q i hi,map_zero,zero_apply]

theorem exists_fderiv_offIndexSignedTerm_eq_sheet_smul_at_endpoints
    (n : ℕ+) (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (hterminal : ∀ m : ℕ+, hillHminusDirichletSheet m q=0) (j : ℤ) :
    ∃ a : ℂ, fderiv ℂ (fun p => positiveScalarExtension (hillHminusOffIndexAbelianTerm n p) j) q =
      a • hillHminusSignedSheetCotangent q j := by
  by_cases hj : j ∈ range positiveEmbedding
  · obtain ⟨m,rfl⟩ := hj
    change ∃ a : ℂ, fderiv ℂ (fun p => positiveScalarExtension (hillHminusOffIndexAbelianTerm n p) ((m:ℕ):ℤ)) q =
      a • hillHminusSignedSheetCotangent q ((m:ℕ):ℤ)
    simp only [positiveScalarExtension_apply,hillHminusSignedSheetCotangent_apply_positive]
    by_cases hmn : m=n
    · refine ⟨0,?_⟩
      simp only [hillHminusOffIndexAbelianTerm,if_pos hmn]
      rw [(hasFDerivAt_const (0:ℂ) q).fderiv]
      ext v
      simp only [zero_apply,smul_apply,smul_eq_mul,zero_mul]
    · simp only [hillHminusOffIndexAbelianTerm,if_neg hmn]
      exact exists_fderiv_hillHminusOffIndexAbelianValue_eq_sheet_smul_at_endpoint n m hmn q hr (hterminal m)
  · refine ⟨0,?_⟩
    have he : (fun p : PeriodOneHminusOne => positiveScalarExtension (hillHminusOffIndexAbelianTerm n p) j) =
        (fun _ => (0:ℂ)) := funext (fun _ => positiveScalarExtension_zero_of_not_mem_range _ j hj)
    rw [he,(hasFDerivAt_const (0:ℂ) q).fderiv]
    ext v
    simp only [zero_apply,smul_apply,smul_eq_mul,zero_mul]

end NLS.KdV
