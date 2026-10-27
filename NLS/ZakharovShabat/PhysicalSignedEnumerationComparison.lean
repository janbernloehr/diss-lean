import NLS.ZakharovShabat.PhysicalSignedEnumerationUniqueness
import NLS.ZakharovShabat.ClassicalSignedEndpointMultiplicity

/-! # Exact source comparison for the independently ordered physical signed lists -/
noncomputable section
set_option autoImplicit false
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem signed_displacement (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) 2) (r : ℤ) :
    Memℓp (fun n => ξ (2*n+r)-(Real.pi : ℂ)*(2*n+r : ℤ)) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  exact (hξ.summable (by norm_num)).comp_injective
    (show Function.Injective (fun n : ℤ => 2*n+r) by intro a b hab; dsimp at hab; omega)

/-- Every complete source parity enumeration sorted within each sign satisfies the independent physical specification. -/
theorem PhysicalSignedPairData.of_complete (u : IntervalPairL2) (r : ℤ) (hr : r = 0 ∨ r = 1)
    {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs (by simp) SpectralWeight.one
      (unitBaseEquiv.symm (periodOnePotential (sourcePhysicalL2Equiv.symm u))) N ξ η)
    (hw : ∀ n, complexLexLE (ξ n) (η n))
    (ho : ∀ i j : ℤ, i < j → i % 2 = j % 2 → complexLexLE (η i) (ξ j)) :
    PhysicalSignedPairData u r (fun n => ξ (2*n+r)) (fun n => η (2*n+r)) :=
  ⟨signed_displacement ξ h.left_displacement r,signed_displacement η h.right_displacement r,
    fun n => hw (2*n+r),fun i j hij => ho (2*i+r) (2*j+r) (by omega) (by omega),
    h.classicalSigned_multiplicity u r hr,h.classicalSigned_exhaustive u r hr⟩

/-- Any sorted complete source construction equals the independently selected physical signed lists. -/
theorem physicalSignedPairs_eq_of_complete (u : IntervalPairL2) (r : Fin 2)
    {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs (by simp) SpectralWeight.one
      (unitBaseEquiv.symm (periodOnePotential (sourcePhysicalL2Equiv.symm u))) N ξ η)
    (hw : ∀ n, complexLexLE (ξ n) (η n))
    (ho : ∀ i j : ℤ, i < j → i % 2 = j % 2 → complexLexLE (η i) (ξ j)) :
    physicalSignedLeft u r = (fun n => ξ (2*n+(r.val : ℤ))) ∧
      physicalSignedRight u r = (fun n => η (2*n+(r.val : ℤ))) :=
  physicalSignedPairs_eq_of_spec u r _ _
    (PhysicalSignedPairData.of_complete u _ (by have := r.isLt; omega) h hw ho)

/-- At arbitrary complex potentials, the separate signed lists agree with the combined
physical endpoint list outside a finite central block, with exactly the printed indices. -/
theorem physicalSignedPairs_eventually_eq_periodic (u : IntervalPairL2) (r : Fin 2) :
    ∃ K : ℕ, ∀ n : ℤ, K < (2*n+(r.val : ℤ)).natAbs →
      physicalSignedLeft u r n = physicalPeriodicLeft u (2*n+(r.val : ℤ)) ∧
      physicalSignedRight u r n = physicalPeriodicRight u (2*n+(r.val : ℤ)) := by
  have he : weightedBaseToPair SpectralWeight.one
      (unitBaseEquiv.symm (periodOnePotential (sourcePhysicalL2Equiv.symm u))) =
      periodOnePotential (sourcePhysicalL2Equiv.symm u) := by
    rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]
  obtain ⟨N,ξ,η,h,hw,ho⟩ := exists_ordered_completePeriodicParityPairs (by simp) (by norm_num)
    SpectralWeight.one (unitBaseEquiv.symm (periodOnePotential (sourcePhysicalL2Equiv.symm u)))
    (by rw [he]; exact periodOnePotential_mem _)
  have hc := canonicalPeriodicEndpoints_spec (by simp) (by norm_num)
    (periodOnePotential (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _)
  have hd := h.toEndpoints
  rw [he] at hd
  have hs := physicalSignedPairs_eq_of_complete u r h hw ho
  refine ⟨max N (canonicalPeriodicCutoff (by simp) (by norm_num)
    (periodOnePotential (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _)),?_⟩
  intro n hn
  rw [hs.1,hs.2,(physicalPeriodicEndpoints_eq_source u).1,(physicalPeriodicEndpoints_eq_source u).2]
  exact (hd.distant (2*n+(r.val : ℤ)) (by omega)).ordered_unique
    (hc.1.distant _ (by omega)) (hw _) (hc.2.1 _)

/-- At real-type potentials the even/odd combined endpoint subsequences satisfy the
independent signed physical specification at every index, including the central block. -/
theorem physicalSignedPairData_of_realType (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (r : ℤ) (hr : r = 0 ∨ r = 1) :
    PhysicalSignedPairData u r (fun n => physicalPeriodicLeft u (2*n+r))
      (fun n => physicalPeriodicRight u (2*n+r)) := by
  have h := physicalPeriodicEndpoints_spec u
  refine ⟨signed_displacement _ h.left_displacement r,signed_displacement _ h.right_displacement r,
    fun n => h.within _,fun i j hij => h.between _ _ (by omega),?_,?_⟩
  · intro z
    rw [finsum_affine_parity (fun k =>
      ({physicalPeriodicLeft u k,physicalPeriodicRight u k} : Multiset ℂ).count z) r]
    rcases hr with rfl | rfl
    · simpa only [Int.zero_emod] using physicalEvenEndpoints_count_classicalPeriodicMultiplicity u hu z
    · simpa only [show (1 : ℤ) % 2 = 1 by norm_num] using
        physicalOddEndpoints_count_classicalAntiperiodicMultiplicity u hu z
  · intro z
    rcases hr with rfl | rfl
    · constructor
      · intro hz
        obtain ⟨k,hk,hz⟩ := (classicalPeriodicSpectrum_iff_even_endpoint u hu z).mp hz
        refine ⟨k/2,?_⟩
        simpa only [show 2*(k/2)+(0 : ℤ) = k by omega] using hz
      · rintro ⟨n,hn⟩
        exact (classicalPeriodicSpectrum_iff_even_endpoint u hu z).mpr ⟨2*n+0,by omega,hn⟩
    · constructor
      · intro hz
        obtain ⟨k,hk,hz⟩ := (classicalAntiperiodicSpectrum_iff_odd_endpoint u hu z).mp hz
        refine ⟨(k-1)/2,?_⟩
        simpa only [show 2*((k-1)/2)+(1 : ℤ) = k by omega] using hz
      · rintro ⟨n,hn⟩
        exact (classicalAntiperiodicSpectrum_iff_odd_endpoint u hu z).mpr ⟨2*n+1,by omega,hn⟩

/-- For real-type potentials the separate physical lists are exactly the even/odd
combined endpoint subsequences, including every collapsed gap. -/
theorem physicalSignedPairs_eq_periodic_of_realType (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (r : Fin 2) :
    physicalSignedLeft u r = (fun n => physicalPeriodicLeft u (2*n+(r.val : ℤ))) ∧
      physicalSignedRight u r = (fun n => physicalPeriodicRight u (2*n+(r.val : ℤ))) :=
  physicalSignedPairs_eq_of_spec u r _ _
    (physicalSignedPairData_of_realType u hu _ (by have := r.isLt; omega))

end NLS.ZakharovShabat
