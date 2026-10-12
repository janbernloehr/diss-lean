import NLS.ZakharovShabat.L2GradientsBelowTwo

/-! # Signed physical Fourier realization below the Hilbert exponent -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Subtracting coefficient vectors subtracts their actual continuous physical gradients. -/
theorem L2RootGradientFourierRealizes.sub {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {g h : ℝ → ℂ × ℂ} {a b : CoeffPair q} (ha : L2RootGradientFourierRealizes g a)
    (hb : L2RootGradientFourierRealizes h b) (hg : Continuous g) (hh : Continuous h) :
    L2RootGradientFourierRealizes (fun s => g s-h s) (a-b) := by
  intro k
  constructor
  · change a.fst k-b.fst k = intervalFourierCoefficient 1 (fun s => (g s).1-(h s).1) (-k)
    rw [(ha k).1,(hb k).1,intervalFourierCoefficient_sub 1 _ _ hg.fst hh.fst]
  · change a.snd k-b.snd k = intervalFourierCoefficient 1 (fun s => (g s).2-(h s).2) k
    rw [(ha k).2,(hb k).2,intervalFourierCoefficient_sub 1 _ _ hg.snd hh.snd]

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- An actual physical integral in all original source directions determines
the signed conjugate Fourier vector, with no change to its source norm. -/
theorem signedGradient_realizes_below_two_of_integral
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp2 : p ≤ 2) (L : CoeffPair p →L[ℂ] ℂ) (g : ℝ → ℂ × ℂ)
    (hint : ∀ h : CoeffPair p, L h = ∫ s in (0 : ℝ)..1,
      (g s).1*(physicalBase (periodOnePotential (CoeffPair.exponentInclusion hp2 h)) s).1+
      (g s).2*(physicalBase (periodOnePotential (CoeffPair.exponentInclusion hp2 h)) s).2) :
    L2RootGradientFourierRealizes g (sourceG7SignedCoordinates q (CoeffPair.conjugateGradient hp hq L)) := by
  have hc (f : ℝ → ℂ) (k : ℤ) : intervalFourierCoefficient 1 f k = unitFourierCoefficient f k := by
    rw [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),unitFourierCoefficient_eq_fourierCoeffOn]
  intro k
  simp only [sourceG7SignedCoordinates_fst,sourceG7SignedCoordinates_snd,
    CoeffPair.conjugateGradient_fst,CoeffPair.conjugateGradient_snd,neg_neg]
  constructor
  · have hd : CoeffPair.inlCLM (lp.single p k (1 : ℂ)) =
        CoeffPair.ofFinsupp (p := p) (Finsupp.single k 1,0) := by
      apply (CoeffPair.toMax p).injective
      apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
    rw [hd,hint,CoeffPair.exponentInclusion_ofFinsupp,source_physical_gradient_pairing_single_fst,hc]
  · have hd : CoeffPair.inrCLM (lp.single p (-k) (1 : ℂ)) =
        CoeffPair.ofFinsupp (p := p) (0,Finsupp.single (-k) 1) := by
      apply (CoeffPair.toMax p).injective
      apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
    rw [hd,hint,CoeffPair.exponentInclusion_ofFinsupp,source_physical_gradient_pairing_single_snd,neg_neg,hc]

/-- The exact free half-wave functional is also the actual zero-source
derivative below exponent two. -/
theorem fderiv_canonicalDirichletRoot_zero_eq_free_below_two
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) (n : ℤ) :
    fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) 0 =
      sourceFreeDirichletCotangent p n := by
  have he := fderiv_canonicalPeriodOneBoundaryRoots_exponent hp (by simp) hp1 (by norm_num) hp2 .dirichlet n
    ⟨0,by intro k; simp⟩
  simp only [map_zero,fderiv_canonicalDirichletRoot_zero_eq_free (by simp) (by norm_num) le_rfl] at he
  exact he.trans (sourceFreeDirichletCotangent_exponent hp2 n).symm

/-- The canonical physical midpoint gradient realizes the original source's
G.7 vector on a complex neighborhood for every 1<p<=2. -/
theorem exists_global_sourceG7_midpoint_below_two_realization
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ ∀ φ ∈ W, ∀ n : ℤ,
      L2RootGradientFourierRealizes (sourceMidpointPhysicalGradientBelowTwo hp2 φ n)
        (sourceG7MidpointGradient (q := q) hp hp1 φ n) := by
  obtain ⟨W,hW,hreal,h⟩ := exists_global_source_midpoint_below_two_integral hp hp1 hp2
  refine ⟨W,hW,hreal,?_⟩
  intro φ hφ n
  exact signedGradient_realizes_below_two_of_integral hp _ hp2 _ _ (h φ hφ n)

/-- The Dirichlet error vector subtracts the actual free physical gradient,
including its exact half-wave normalization and all signed indices. -/
theorem exists_global_sourceG7_dirichlet_below_two_realization
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ ∀ φ ∈ W, ∀ n : ℤ,
      let u := sourcePhysicalL2 (CoeffPair.exponentInclusion hp2 φ)
      let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
      l2DirichletNormalization u z ≠ 0 ∧
        L2RootGradientFourierRealizes (l2DirichletGradientRemainder u z ((Real.pi : ℂ)*n))
          (sourceG7DirichletGradientError (q := q) hp hp1 φ n) := by
  obtain ⟨W,hW,hreal,h⟩ := exists_global_source_dirichlet_below_two_integral hp hp1 hp2
  refine ⟨W,hW,hreal,?_⟩
  have hzero : (0 : CoeffPair p) ∈ W := hreal (by intro k; simp)
  intro φ hφ n
  dsimp only
  obtain ⟨hQ,hi⟩ := h φ hφ n
  have h0 := (h 0 hzero n).2
  simp only [map_zero,canonicalPeriodOneBoundaryRoots_zero] at h0
  have hq : q ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne'
  have hactual := signedGradient_realizes_below_two_of_integral hp hq hp2 _ _ hi
  have hfree := signedGradient_realizes_below_two_of_integral hp hq hp2 _ _ h0
  have hsub := hactual.sub hfree (continuous_l2DirichletNormalizedGradient _ _)
    (continuous_l2DirichletNormalizedGradient _ _)
  refine ⟨hQ,?_⟩
  change L2RootGradientFourierRealizes _ (sourceG7SignedCoordinates q
    (CoeffPair.conjugateGradientCLM hp hq (_-sourceFreeDirichletCotangent p n)))
  rw [← fderiv_canonicalDirichletRoot_zero_eq_free_below_two hp hp1 hp2 n,map_sub,map_sub]
  exact hsub

end NLS.ZakharovShabat
