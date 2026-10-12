import NLS.ZakharovShabat.L2GradientRestrictionFourier

/-! # Both physical G.7 estimates below the Hilbert exponent

The established actual derivative estimates transfer to the original
signed conjugate coefficient norm. Every real H1 source has both physical
gradient realizations, with arbitrary finite spectral heads included.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- Both signed coefficient sequences retain the original source exponent
and exact finite conjugate pair norm for every real H1 source below two. -/
theorem sourceG7_below_two_memlp_real
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : realTypeSourceLocus p) (a : Domain 2)
    (ha : periodOnePotential (CoeffPair.exponentInclusion hp2 φ.val) = domainInclusion a) :
    Memℓp (fun n : ℤ => sourceG7MidpointGradient (q := q) hp hp1 φ.val n) p ∧
      Memℓp (fun n : ℤ => sourceG7DirichletGradientError (q := q) hp hp1 φ.val n) p := by
  have hq : q ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne'
  have hm := CoeffPair.memlp_conjugateGradient (q := q) hp hq _
    (memlp_source_midpoint_fderiv_below_two hp hp1 hp2 φ a ha)
  have hd := CoeffPair.memlp_conjugateGradient (q := q) hp hq _
    (memlp_source_dirichlet_fderiv_error_below_two hp hp1 hp2 φ a ha)
  constructor
  · apply Memℓp.of_norm
    simpa only [sourceG7MidpointGradient,norm_sourceG7SignedCoordinates,sourceMidpointConjugateGradient] using hm.norm
  · apply Memℓp.of_norm
    simpa only [sourceG7DirichletGradientError,norm_sourceG7SignedCoordinates,sourceDirichletConjugateGradientError] using hd.norm

/-- G.7's whole sequences below two realize the canonical physical midpoint
gradient and the normalized Dirichlet gradient minus its actual free value. -/
theorem sourceG7_below_two_physical_real
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : realTypeSourceLocus p) (a : Domain 2)
    (ha : periodOnePotential (CoeffPair.exponentInclusion hp2 φ.val) = domainInclusion a) :
    Memℓp (fun n : ℤ => sourceG7MidpointGradient (q := q) hp hp1 φ.val n) p ∧
      Memℓp (fun n : ℤ => sourceG7DirichletGradientError (q := q) hp hp1 φ.val n) p ∧ ∀ n : ℤ,
        L2RootGradientFourierRealizes (sourceMidpointPhysicalGradientBelowTwo hp2 φ.val n)
          (sourceG7MidpointGradient (q := q) hp hp1 φ.val n) ∧
        let u := sourcePhysicalL2 (CoeffPair.exponentInclusion hp2 φ.val)
        let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n
        l2DirichletNormalization u z ≠ 0 ∧
          L2RootGradientFourierRealizes (l2DirichletGradientRemainder u z ((Real.pi : ℂ)*n))
            (sourceG7DirichletGradientError (q := q) hp hp1 φ.val n) := by
  obtain ⟨hm,hd⟩ := sourceG7_below_two_memlp_real (q := q) hp hp1 hp2 φ a ha
  obtain ⟨U,_,hUr,hu⟩ := exists_global_sourceG7_midpoint_below_two_realization (q := q) hp hp1 hp2
  obtain ⟨V,_,hVr,hv⟩ := exists_global_sourceG7_dirichlet_below_two_realization (q := q) hp hp1 hp2
  exact ⟨hm,hd,fun n => ⟨hu φ.val (hUr φ.property) n,hv φ.val (hVr φ.property) n⟩⟩

end NLS.ZakharovShabat
