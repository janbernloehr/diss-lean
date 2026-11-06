import NLS.ZakharovShabat.CanonicalPeriodicEndpoints
import NLS.ZakharovShabat.FiniteParityCompatibility
import NLS.SequenceSpaces.Reflection

/-! # Actual endpoint reflection for an even discriminant

Evenness preserves the original periodic spectrum and its exact algebraic
multiplicities. Reflecting a complete ordered endpoint labeling therefore
identifies the actual canonical endpoints, including the central cluster
and collapsed pairs, without a real-type hypothesis.
-/
noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem complexLexLE_neg_iff (z w : ℂ) : complexLexLE (-z) (-w) ↔ complexLexLE w z := by
  simp only [complexLexLE_iff,neg_re,neg_im,neg_lt_neg_iff,neg_le_neg_iff,neg_inj]
  constructor <;> rintro (h | ⟨h,h'⟩)
  · exact Or.inl h
  · exact Or.inr ⟨h.symm,h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h.symm,h'⟩

theorem neg_mem_refinedResonantDisk_iff (n : ℤ) (z : ℂ) :
    -z ∈ refinedResonantDisk n ↔ z ∈ refinedResonantDisk (-n) := by
  simp only [refinedResonantDisk,mem_ball,dist_eq_norm,Int.cast_neg,mul_neg]
  rw [show -z-(Real.pi : ℂ)*n = -(z-(-(Real.pi : ℂ)*n)) by ring,norm_neg]
  ring_nf

theorem neg_mem_resonantStrip_iff (n : ℤ) (z : ℂ) :
    -z ∈ resonantStrip n ↔ z ∈ resonantStrip (-n) := by
  simp only [resonantStrip,mem_ofPred_eq,neg_re,Int.cast_neg,mul_neg]
  rw [show -z.re-Real.pi*n = -(z.re- -(Real.pi*n)) by ring,abs_neg]

theorem neg_mem_centralSpectralBox_iff (N : ℕ) (z : ℂ) :
    -z ∈ centralSpectralBox N ↔ z ∈ centralSpectralBox N := by
  simp only [centralSpectralBox,mem_ofPred_eq,neg_re,neg_im,abs_neg]

variable (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
  (hφ : φ ∈ pairParitySubspace 0)
  (heven : ∀ z, canonicalDiscriminant hp φ (-z) = canonicalDiscriminant hp φ z)

include hp1 hφ heven

theorem canonicalPeriodicProduct_even_of_discriminant_even (z : ℂ) :
    canonicalPeriodicProduct hp φ (-z) = canonicalPeriodicProduct hp φ z := by
  rw [canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1 φ hφ,
    canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1 φ hφ,heven]

theorem neg_mem_periodicSpectrum_iff_of_discriminant_even (z : ℂ) :
    -z ∈ periodicSpectrum hp φ ↔ z ∈ periodicSpectrum hp φ := by
  rw [← canonicalPeriodicProduct_eq_zero_iff hp hp1,
    canonicalPeriodicProduct_even_of_discriminant_even hp hp1 φ hφ heven,
    canonicalPeriodicProduct_eq_zero_iff hp hp1]

theorem periodicAlgebraicMultiplicity_neg_of_discriminant_even (z : ℂ) :
    periodicAlgebraicMultiplicity hp φ (-z) = periodicAlgebraicMultiplicity hp φ z := by
  have hg : AnalyticAt ℂ (fun w : ℂ => -w) z := analyticAt_id.neg
  have hd : deriv (fun w : ℂ => -w) z ≠ 0 := by simp
  have h := analyticOrderAt_comp_of_deriv_ne_zero
    (f := canonicalPeriodicProduct hp φ) hg hd
  have he : canonicalPeriodicProduct hp φ ∘ (fun w : ℂ => -w) = canonicalPeriodicProduct hp φ := by
    funext w
    exact canonicalPeriodicProduct_even_of_discriminant_even hp hp1 φ hφ heven w
  rw [he,analyticOrderAt_canonicalPeriodicProduct hp hp1,
    analyticOrderAt_canonicalPeriodicProduct hp hp1] at h
  exact_mod_cast h.symm

theorem neg_mem_centralPeriodicSpectrum_iff_of_discriminant_even (N : ℕ) (z : ℂ) :
    -z ∈ centralPeriodicSpectrum hp φ N ↔ z ∈ centralPeriodicSpectrum hp φ N := by
  rw [mem_centralPeriodicSpectrum,mem_centralPeriodicSpectrum,
    neg_mem_periodicSpectrum_iff_of_discriminant_even hp hp1 φ hφ heven,
    neg_mem_centralSpectralBox_iff]

theorem CentralPeriodicLabeling.neg_reflect_of_discriminant_even
    {N : ℕ} {ξ η : ℤ → ℂ} (h : CentralPeriodicLabeling hp φ N ξ η) :
    CentralPeriodicLabeling hp φ N (fun n => -η (-n)) (fun n => -ξ (-n)) := by
  constructor
  apply Multiset.ext.mpr
  intro z
  rw [Multiset.count_sum']
  calc
    _ = ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({ξ n,η n} : Multiset ℂ).count (-z) := by
      apply Finset.sum_bij (fun n _ => -n)
      · intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      · intro n _ m _ hnm
        exact neg_injective hnm
      · intro n hn
        refine ⟨-n,?_,by simp⟩
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      · intro n _
        simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,neg_eq_iff_eq_neg]
        omega
    _ = if -z ∈ centralPeriodicSpectrum hp φ N then
        periodicAlgebraicMultiplicity hp φ (-z) else 0 := h.count_eq (-z)
    _ = _ := by
      simp only [neg_mem_centralPeriodicSpectrum_iff_of_discriminant_even hp hp1 φ hφ heven,
        periodicAlgebraicMultiplicity_neg_of_discriminant_even hp hp1 φ hφ heven,
        count_centralPeriodicRoots]

theorem PeriodicEndpointPair.neg_reflect_of_discriminant_even
    {n : ℤ} {x y : ℂ} (h : PeriodicEndpointPair hp φ n x y) :
    PeriodicEndpointPair hp φ (-n) (-y) (-x) := by
  refine ⟨(neg_mem_refinedResonantDisk_iff (-n) y).mpr (by simpa using h.right_mem),
    (neg_mem_refinedResonantDisk_iff (-n) x).mpr (by simpa using h.left_mem),?_,?_⟩
  · intro z hz
    have hz' : -z ∈ resonantStrip n := (neg_mem_resonantStrip_iff n z).mpr hz
    have he := h.spectrum_iff (-z) hz'
    rw [neg_mem_periodicSpectrum_iff_of_discriminant_even hp hp1 φ hφ heven] at he
    simpa only [neg_eq_iff_eq_neg,or_comm] using he
  · intro z hz
    rw [← periodicAlgebraicMultiplicity_neg_of_discriminant_even hp hp1 φ hφ heven z,
      h.multiplicity_eq_count (-z) ((neg_mem_resonantStrip_iff n z).mpr hz)]
    simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,neg_eq_iff_eq_neg]
    omega

theorem PeriodicEndpointLabeling.neg_reflect_of_discriminant_even
    {N : ℕ} {ξ η : ℤ → ℂ} (h : PeriodicEndpointLabeling hp φ N ξ η) :
    PeriodicEndpointLabeling hp φ N (fun n => -η (-n)) (fun n => -ξ (-n)) := by
  refine ⟨h.counting,h.central.neg_reflect_of_discriminant_even hp hp1 φ hφ heven,
    ?_,?_,?_⟩
  · intro n hn
    simpa only [neg_neg] using
      (h.distant (-n) (by simpa only [Int.natAbs_neg] using hn)).neg_reflect_of_discriminant_even
        hp hp1 φ hφ heven
  · let a : Coeff p := ⟨fun n => η n-(Real.pi : ℂ)*n,h.right_displacement⟩
    have he : (fun n => -η (-n)-(Real.pi : ℂ)*n) = fun n => (-Coeff.reflection a) n := by
      funext n
      simp only [lp.coeFn_neg,Pi.neg_apply,Coeff.reflection_apply,a,Int.cast_neg,mul_neg]
      ring
    rw [he]
    exact lp.memℓp _
  · let a : Coeff p := ⟨fun n => ξ n-(Real.pi : ℂ)*n,h.left_displacement⟩
    have he : (fun n => -ξ (-n)-(Real.pi : ℂ)*n) = fun n => (-Coeff.reflection a) n := by
      funext n
      simp only [lp.coeFn_neg,Pi.neg_apply,Coeff.reflection_apply,a,Int.cast_neg,mul_neg]
      ring
    rw [he]
    exact lp.memℓp _

theorem canonicalPeriodicEndpoints_neg_of_discriminant_even (n : ℤ) :
    canonicalPeriodicLeft hp hp1 φ hφ (-n) = -canonicalPeriodicRight hp hp1 φ hφ n ∧
      canonicalPeriodicRight hp hp1 φ hφ (-n) = -canonicalPeriodicLeft hp hp1 φ hφ n := by
  obtain ⟨h,hw,hc⟩ := canonicalPeriodicEndpoints_spec hp hp1 φ hφ
  have hn := h.neg_reflect_of_discriminant_even hp hp1 φ hφ heven
  have hu := hn.eq_canonicalPeriodicEndpoints hp1 hφ
    (fun k => (complexLexLE_neg_iff _ _).mpr (hw (-k))) (by
      intro i j hij
      apply (complexLexLE_neg_iff _ _).mpr
      exact hc (-j) (-i) (neg_lt_neg hij))
  have hl := congrFun hu.1 (-n)
  have hr := congrFun hu.2 (-n)
  constructor
  · simpa only [neg_neg] using hl.symm
  · simpa only [neg_neg] using hr.symm

end NLS.ZakharovShabat
