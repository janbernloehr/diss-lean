import NLS.ZakharovShabat.SourceBirkhoffRegularCotangent

/-! # Lemma 15.3 on the real open-gap locus

The actual rectangular cotangents have the canonical physical Fourier
pairings at every finite exponent above one. This proves the open-gap
part of Lemma 15.3; extension across collapsed gaps remains separate.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The action is nonzero wherever its real periodic gap is open. -/
theorem birkhoff_action_ne_zero
    (n : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    sourceComplexAction hp hp1 n φ.val ≠ 0 := by
  rw [sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property]
  intro hz
  have h := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 φ.val φ.property n).2.2.mp hz
  exact hn (by simpa only [sourcePeriodicGapDisplacement_apply] using h)

/-- The same root family used for the canonical angles has the exact
rectangular action radius at every real open gap. -/
theorem birkhoffXY_action_radius
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    (sourceBirkhoffX hp hp1 n s φ.val)^2 + (sourceBirkhoffY hp hp1 n s φ.val)^2 =
      2*sourceComplexAction hp hp1 n φ.val := by
  obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,_,_,E⟩ := D.local_charts n φ.val (D.real_subset φ.property) hn
  obtain ⟨A,_,hφA,_,hfactor⟩ := exists_local_sourceNormalizedActionRoot_allIndices_analytic hp hp1 φ.val φ.property
  have hμ := (((E.annulus.disc_family φ.val (E.angle.source_subset hφU)).contour_family.2 n).2.2.1
    (Metric.ball_subset_closedBall ((E.annulus.disc_family φ.val (E.angle.source_subset hφU)).dirichlet_mem_ball n)))
  exact sourceBirkhoffX_sq_add_Y_sq hp hp1 n s φ.val
    (by simpa only [sourcePeriodicGapDisplacement_apply] using sourceGapWeightedEtaCoordinate_mul hp hp1 n s φ.val hμ)
    (hfactor φ.val hφA n).1 (hfactor φ.val hφA n).2

/-- All three rectangular canonical identities at real sources whose
two selected gaps are open, including the diagonal mixed sign `-1`. -/
theorem birkhoff_regular_canonical_of_open_gaps
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    (D.birkhoffXRegularCotangent n φ hn).bivector (D.birkhoffXRegularCotangent m φ hm) = 0 ∧
    (D.birkhoffXRegularCotangent n φ hn).bivector (D.birkhoffYRegularCotangent m φ hm) =
      -(if n = m then 1 else 0) ∧
    (D.birkhoffYRegularCotangent n φ hn).bivector (D.birkhoffYRegularCotangent m φ hm) = 0 := by
  have hII := sourceActionRegularCotangent_bivector_eq_zero hp hp1 n m φ
  have hTT := D.thetaRegularCotangent_bivector_eq_zero n m φ hn hm
  have hTI := D.thetaActionRegular_bivector_eq_kronecker n m φ hn
  have hIT : (sourceActionRegularCotangent hp hp1 n φ).bivector (D.thetaRegularCotangent m φ hm) =
      -(if n = m then 1 else 0) := by
    rw [RegularSourceCotangent.bivector_antisymm,D.thetaActionRegular_bivector_eq_kronecker m n φ hm]
    simp only [eq_comm]
  have hcomb := RegularSourceCotangent.bivector_linear_combination_of_canonical
    (sourceActionRegularCotangent hp hp1 n φ) (D.thetaRegularCotangent n φ hn)
    (sourceActionRegularCotangent hp hp1 m φ) (D.thetaRegularCotangent m φ hm)
    (if n = m then 1 else 0)
  simp only [birkhoffXRegularCotangent,birkhoffYRegularCotangent,
    hcomb _ _ _ _ hII hTT hTI hIT]
  by_cases hnm : n = m
  · subst m
    simp only [ite_true,mul_one]
    have hne := birkhoff_action_ne_zero n φ hn
    have hradius := D.birkhoffXY_action_radius n φ hn
    constructor
    · ring
    constructor
    · field_simp
      linear_combination -hradius
    · ring
  · simp only [hnm,ite_false,mul_zero,neg_zero,and_self]

/-- The literal physical Fourier sum of the actual mixed rectangular
cotangents is absolutely convergent and equals the negative Kronecker delta. -/
theorem birkhoffXY_fourier_canonical_of_open_gaps
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    let L := fderiv ℂ (sourceBirkhoffX hp hp1 n s) φ.val
    let M := fderiv ℂ (sourceBirkhoffY hp hp1 m s) φ.val
    Summable (fun j : ℤ => ‖L (CoeffPair.inlCLM (lp.single p j 1)) *
      M (CoeffPair.inrCLM (lp.single p (-j) 1)) -
      L (CoeffPair.inrCLM (lp.single p j 1)) * M (CoeffPair.inlCLM (lp.single p (-j) 1))‖) ∧
    -I * ∑' j : ℤ, (L (CoeffPair.inlCLM (lp.single p j 1)) *
      M (CoeffPair.inrCLM (lp.single p (-j) 1)) -
      L (CoeffPair.inrCLM (lp.single p j 1)) * M (CoeffPair.inlCLM (lp.single p (-j) 1))) =
        -(if n = m then 1 else 0) := by
  dsimp only
  have hs := (D.birkhoffXRegularCotangent n φ hn).summable_norm (D.birkhoffYRegularCotangent m φ hm)
  have heq := (D.birkhoffXRegularCotangent n φ hn).bivector_eq_tsum (D.birkhoffYRegularCotangent m φ hm)
  simp only [D.birkhoffXRegularCotangent_toCotangent,D.birkhoffYRegularCotangent_toCotangent] at hs heq
  exact ⟨hs,heq.symm.trans (D.birkhoff_regular_canonical_of_open_gaps n m φ hn hm).2.1⟩

/-- On exponents at least two these are exactly the existing source
brackets of the rectangular functions themselves. -/
theorem birkhoff_sourceBracket_canonical_of_open_gaps
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    sourceBracket h2p (sourceBirkhoffX hp hp1 n s) (sourceBirkhoffX hp hp1 m s) φ.val = 0 ∧
    sourceBracket h2p (sourceBirkhoffX hp hp1 n s) (sourceBirkhoffY hp hp1 m s) φ.val =
      -(if n = m then 1 else 0) ∧
    sourceBracket h2p (sourceBirkhoffY hp hp1 n s) (sourceBirkhoffY hp hp1 m s) φ.val = 0 := by
  have hcast (L M : RegularSourceCotangent p) (F G : CoeffPair p → ℂ)
      (hL : L.toCotangent = fderiv ℂ F φ.val) (hM : M.toCotangent = fderiv ℂ G φ.val) :
      L.bivector M = sourceBracket h2p F G φ.val := by
    change _ = (RegularSourceCotangent.ofCotangent h2p (fderiv ℂ F φ.val)).bivector
      (RegularSourceCotangent.ofCotangent h2p (fderiv ℂ G φ.val))
    exact RegularSourceCotangent.bivector_congr hL hM
  have h := D.birkhoff_regular_canonical_of_open_gaps n m φ hn hm
  rwa [hcast _ _ _ _ (D.birkhoffXRegularCotangent_toCotangent n φ hn)
      (D.birkhoffXRegularCotangent_toCotangent m φ hm),
    hcast _ _ _ _ (D.birkhoffXRegularCotangent_toCotangent n φ hn)
      (D.birkhoffYRegularCotangent_toCotangent m φ hm),
    hcast _ _ _ _ (D.birkhoffYRegularCotangent_toCotangent n φ hn)
      (D.birkhoffYRegularCotangent_toCotangent m φ hm)] at h

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
