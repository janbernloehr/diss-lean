import NLS.ZakharovShabat.SourceStandardRootOmittedFreeNormalization
import NLS.ZakharovShabat.SourceSingleRootQuotientAnalytic
import NLS.ZakharovShabat.SourcePsiCandidate

/-!
# Root parameters, free normalization and numerator collisions

The displacement space represents exactly the affine ℓᵖ root sequences
of Corollary 10.6. The omitted coordinate is unused. Numerator collisions
are allowed and can produce actual zeros on the quotient's analytic domain.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At zero source and free displaced roots, the quotient equals one on its actual domain. -/
theorem sourceSingleRootQuotient_zero_free (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 (0 : CoeffPair p) n) :
    sourceSingleRootQuotientJointProduct hp hp1 n (z,(0,0)) = 1 := by
  have hne := sourceStandardRootOmittedProduct_ne_zero hp hp1 (0 : CoeffPair p) z n hz
  unfold sourceSingleRootQuotientJointProduct sourceStandardRootOmittedJointProduct
  rw [← sourceStandardRootOmittedProduct_zero_source_eq_deleted hp hp1 n z]
  exact div_self hne

/-- The omitted displacement coordinate is unused, even in the complete infinite product. -/
theorem sourceSingleRootQuotient_eq_of_off_index (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (z : ℂ) (a b : Coeff p)
    (hab : ∀ m : ℤ, m ≠ n → a m = b m) :
    sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ)) =
      sourceSingleRootQuotientJointProduct hp hp1 n (z,(b,ψ)) := by
  have hA := tendsto_jointDeletedSingleSpectralPartialProduct hp hp1 n (z,a)
  have hB := tendsto_jointDeletedSingleSpectralPartialProduct hp hp1 n (z,b)
  have he : (fun N => jointDeletedSingleSpectralPartialProduct n N (z,a)) =
      (fun N => jointDeletedSingleSpectralPartialProduct n N (z,b)) := by
    funext N
    exact jointDeletedSingleSpectralPartialProduct_eq_of_off_index n N z a b hab
  rw [he] at hA
  have hn := tendsto_nhds_unique hA hB
  unfold sourceSingleRootQuotientJointProduct
  rw [hn]

/-- Unomitted numerator roots remain zeros; no nonvanishing assertion is imposed on this quotient. -/
theorem sourceSingleRootQuotient_other_root_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n m : ℤ) (hmn : m ≠ n) (a : Coeff p) :
    sourceSingleRootQuotientJointProduct hp hp1 n (displacedRoots a m,(a,ψ)) = 0 := by
  have hn : jointDeletedSingleSpectralProduct n (displacedRoots a m,a) = 0 := by
    have hc := sourcePsiCandidate_other_root hp hp1 n m hmn a
    change -2*jointDeletedSingleSpectralProduct n (displacedRoots a m,a) = 0 at hc
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num)
  simp [sourceSingleRootQuotientJointProduct,hn]


omit [Fact (1 ≤ p)] in
/-- The displacement parameter represents exactly all root sequences permitted in the source. -/
theorem exists_displacedRoots_iff_memℓp (σ : ℤ → ℂ) :
    (∃ a : Coeff p, displacedRoots a = σ) ↔
      Memℓp (fun m : ℤ => σ m-(Real.pi:ℂ)*m) p := by
  constructor
  · rintro ⟨a,rfl⟩
    exact memℓp_displacedRoots a
  · intro hσ
    refine ⟨⟨fun m => σ m-(Real.pi:ℂ)*m,hσ⟩,?_⟩
    funext m
    change (Real.pi:ℂ)*m+(σ m-(Real.pi:ℂ)*m) = σ m
    ring

/-- Explicit finitely supported numerator data collide at I, yet the quotient is defined there and zero. -/
theorem exists_sourceSingleRootQuotient_colliding_roots_zero (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ a : Coeff p, displacedRoots a (-1) = Complex.I ∧ displacedRoots a 0 = Complex.I ∧
      Complex.I ∈ sourceStandardRootOmittedDomain hp hp1 (0 : CoeffPair p) (-1) ∧
      sourceSingleRootQuotientJointProduct hp hp1 (-1) (Complex.I,(a,0)) = 0 := by
  let a : Coeff p := Coeff.ofFinsupp
    (Finsupp.single 0 Complex.I + Finsupp.single (-1) ((Real.pi:ℂ)+Complex.I))
  have h0 : displacedRoots a 0 = Complex.I := by
    simp [a,displacedRoots,Coeff.ofFinsupp_apply]
  have hn : displacedRoots a (-1) = Complex.I := by
    simp [a,displacedRoots,Coeff.ofFinsupp_apply]
  refine ⟨a,hn,h0,sourceStandardRootOmittedDomain_zero_source_contains_I hp hp1 (-1),?_⟩
  rw [← h0]
  exact sourceSingleRootQuotient_other_root_zero hp hp1 0 (-1) 0 (by decide) a

/-- Every free omitted point lies in the natural domain, so the filled quotient has value one there. -/
theorem sourceStandardRootOmittedDomain_zero_source_contains_center (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    (Real.pi:ℂ)*n ∈ sourceStandardRootOmittedDomain hp hp1 (0 : CoeffPair p) n := by
  intro m hm hmem
  simp only [sourcePeriodicSegment,map_zero,canonicalPeriodicLeft_zero,
    canonicalPeriodicRight_zero,segment_same] at hmem
  have he : (Real.pi:ℂ)*n = (Real.pi:ℂ)*m := hmem
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hnm := mul_left_cancel₀ hπ he
  exact hm (by exact_mod_cast hnm.symm)

end NLS.ZakharovShabat
