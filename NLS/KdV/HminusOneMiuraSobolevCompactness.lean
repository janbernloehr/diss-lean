import NLS.KdV.HminusOneMiuraCompactness
import NLS.ZakharovShabat.SourceSobolevCompactRegularity
import NLS.ZakharovShabat.ExponentSourcePotentials

/-!
# Stronger compact realizations of actual isospectral real Miura lifts

All scalar lifts in one actual Hilbert Dirac isospectral set have identical
canonically indexed gaps. A Sobolev bound on this fixed gap sequence supplies
a compact scalar realization in every strictly lower nonnegative order.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The entire actual real scalar Dirac-isospectral lift family has a
continuous compact Sobolev realization. The exact unit-period Fourier
coefficients are retained; no stronger-norm continuity is assumed. -/
theorem exists_compact_sobolev_miura_isospectral_lifts
    (hp : p ≠ ⊤) (hp2 : 2 ≤ p) (u₀ : PeriodOneRealL2)
    (S s : ℝ) (hs : 0 ≤ s) (hsS : s < S)
    (hgap : Memℓp (fun n : ℤ => (Weight.sobolev S n:ℂ)*
      (hillMiuraDiracRight u₀.val n-hillMiuraDiracLeft u₀.val n)) p) :
    ∃ F : (hillMiuraRealSource ⁻¹'
        sourceIsospectralSet (by norm_num) (hillMiuraRealSource u₀)) → Coeff p,
      Continuous F ∧
      (∀ v n, F v n = (Weight.sobolev s n:ℂ)*v.val.val n) ∧ IsCompact (range F) := by
  let K := hillMiuraRealSource ⁻¹' sourceIsospectralSet (by norm_num) (hillMiuraRealSource u₀)
  let : CompactSpace K := isCompact_iff_compactSpace.mp
    (isCompact_hillMiuraRealSource_isospectral_preimage u₀)
  let : Nonempty K := ⟨⟨u₀,⟨rfl,fun _ => rfl⟩⟩⟩
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num : (1:ℝ≥0∞) < 2) hp2
  let φ : K → realTypeSourceSubmodule p := fun v =>
    ⟨CoeffPair.exponentInclusion hp2 (hillMiuraDiagonal v.val.val),by
      intro n
      change (CoeffPair.exponentInclusion hp2 (hillMiuraDiagonal v.val.val)).snd n =
        conj ((CoeffPair.exponentInclusion hp2 (hillMiuraDiagonal v.val.val)).fst (-n))
      simp only [CoeffPair.exponentInclusion_snd,CoeffPair.exponentInclusion_fst,
        hillMiuraDiagonal_snd,hillMiuraDiagonal_fst,Coeff.exponentInclusion_apply]
      simpa only [neg_neg] using v.val.property (-n)⟩
  have hφ : Continuous φ := by
    apply Continuous.subtype_mk
    exact (CoeffPair.exponentInclusion hp2).continuous.comp
      (hillMiuraDiagonal.continuous.comp (continuous_subtype_val.comp continuous_subtype_val))
  have hbase : Memℓp (fun n : ℤ => hillMiuraDiracRight u₀.val n-hillMiuraDiracLeft u₀.val n) p := by
    apply hgap.mono'
    intro n
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((Weight.sobolev S).positive n)]
    have hw : 1 ≤ Weight.sobolev S n := by
      simpa only [Weight.sobolev_zero_apply] using Weight.sobolev_mono (hs.trans hsS.le) n
    exact le_mul_of_one_le_left (norm_nonneg _) hw
  let Γ : Coeff p := ⟨_,hbase⟩
  have hge (v : K) (n : ℤ) : sourcePeriodicGapDisplacement hp hp1 (φ v).val n = Γ n := by
    have hexp := canonicalPeriodicEndpoints_periodOne_exponent
      (by norm_num : (2:ℝ≥0∞) ≠ ⊤) hp (by norm_num) hp1 hp2 (hillMiuraDiagonal v.val.val)
    have hiso := canonicalPeriodicEndpoints_eq_of_spectral_data (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal v.val.val))
      (periodOnePotential (hillMiuraDiagonal u₀.val)) (periodOnePotential_mem _)
      (periodOnePotential_mem _) v.property.1 v.property.2
    rw [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap]
    change canonicalPeriodicRight hp hp1
      (periodOnePotential (CoeffPair.exponentInclusion hp2 (hillMiuraDiagonal v.val.val)))
        (periodOnePotential_mem _) n-
      canonicalPeriodicLeft hp hp1
        (periodOnePotential (CoeffPair.exponentInclusion hp2 (hillMiuraDiagonal v.val.val)))
          (periodOnePotential_mem _) n = Γ n
    rw [← congrFun hexp.2 n,← congrFun hexp.1 n,congrFun hiso.2 n,congrFun hiso.1 n]
    rfl
  obtain ⟨B,hB,hBc,_⟩ := exists_compact_source_sobolev_family_of_gap_majorant hp hp1 φ hφ
    S s hs hsS Γ hgap (fun v n => by rw [hge v n])
  let F := fun v => (B v).fst
  have hF : Continuous F := continuous_fst.comp ((CoeffPair.toMax p).continuous.comp hB)
  refine ⟨F,hF,?_,isCompact_range hF⟩
  intro v n
  simpa only [F,φ,CoeffPair.exponentInclusion_fst,hillMiuraDiagonal_fst,
    Coeff.exponentInclusion_apply] using (hBc v n).1

end NLS.KdV
