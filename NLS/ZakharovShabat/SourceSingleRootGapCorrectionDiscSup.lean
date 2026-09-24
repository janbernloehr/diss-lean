import NLS.ZakharovShabat.SourceSingleRootGapCorrectionLimit
import NLS.ZakharovShabat.SourceSquaredGapReciprocalRows

/-!
# A half-exponent majorant for the infinite gap correction

The reciprocal-square gap row is independent of the point selected in
an isolating disc. Its `ℓ^(p/2)` coefficient sequence therefore gives
a common majorant for the analytic quotient-minus-midpoint error,
including the quasi-Banach range `1 < p < 2`.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- On distant discs where the gap row is small and the quotient is
defined, the difference from the midpoint product has an `ℓ^(p/2)`
majorant uniform in the spectral point. -/
theorem exists_sourceSingleRootGapCorrectionDiscMajorant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤)
    (φ ψ : CoeffPair p) (a : Coeff p) (α : Coeff q)
    (hα : ∀ m : ℤ,
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m)
    (N K : ℕ) (ε C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-z‖)
    (hdom : ∀ n : ℤ, K ≤ n.natAbs →
      ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε n,
        (z,(a,ψ)) ∈ sourceSingleRootQuotientJointDomain hp hp1 Set.univ n)
    (hsmall : ∀ n : ℤ, K ≤ n.natAbs →
      (C^2/4)*(∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) ≤ 1/2) :
    ∃ B : Coeff (ENNReal.ofReal (p.toReal/2)),
      (∀ n : ℤ, K ≤ n.natAbs →
        ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε n,
          ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ)) -
            (sourceMidpointProductRow hp hp1 ψ α n z+1)‖ ≤ ‖B n‖) ∧
      ‖B‖ ≤
        (Real.exp (C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖)*C^2) *
          (‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ *
            ‖squaredReciprocalKernel (min 1 (p.toReal/2))
              (lt_min (by norm_num : (1/2:ℝ)<1)
                (by
                  have hpr : 1 < p.toReal :=
                    (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
                  linarith))‖) := by
  obtain ⟨S,hS,hSnorm⟩ := exists_sourceSquaredGapPhysicalRows hp hp1 ψ
  let D : ℝ := Real.exp (C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖)*C^2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let B : Coeff (ENNReal.ofReal (p.toReal/2)) := (D : ℂ) • S
  refine ⟨B,?_,?_⟩
  · intro n hn z hz
    have hT : 0 ≤ (∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) :=
      tsum_nonneg (fun m => by
        unfold sourceSquaredGapReciprocalTerm
        split_ifs <;> positivity)
    have hBn : ‖B n‖ = D *
        (∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) := by
      change ‖(D : ℂ) • S n‖ = _
      rw [norm_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD,
        (hS n).2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT]
    rw [hBn]
    exact norm_sourceSingleRootQuotientJointProduct_sub_midpoint_le_of_small_row
      hp hp1 hq φ ψ a α hα N ε C hC hsep n z hz
        (hdom n hn z hz) (hsmall n hn)
  · change ‖(D : ℂ) • S‖ ≤ _
    have hhalf0 : ENNReal.ofReal (p.toReal/2) ≠ 0 := by
      have hpr : 0 < p.toReal :=
        ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
    rw [lp.norm_const_smul hhalf0, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hD]
    exact mul_le_mul_of_nonneg_left hSnorm hD

/-- A common connected source neighborhood and index threshold support
the `ℓ^(p/2)` gap-correction majorant for the actual analytic quotient. -/
theorem exists_local_sourceSingleRootGapCorrectionDiscMajorant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℕ,
          ∀ ψ ∈ V, ∀ a : Coeff p, ∀ α : Coeff q,
            (∀ m : ℤ,
              displacedRoots a m -
                canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
                  (periodOnePotential_mem ψ) m = α m) →
            ∃ B : Coeff (ENNReal.ofReal (p.toReal/2)),
              (∀ n : ℤ, K ≤ n.natAbs →
                ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                  ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ)) -
                    (sourceMidpointProductRow hp hp1 ψ α n z+1)‖ ≤ ‖B n‖) ∧
              ‖B‖ ≤
                (Real.exp (C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
                  ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖)*C^2) *
                    (‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ *
                      ‖squaredReciprocalKernel (min 1 (p.toReal/2))
                        (lt_min (by norm_num : (1/2:ℝ)<1)
                          (by
                            have hpr : 1 < p.toReal :=
                              (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
                            linarith))‖) := by
  obtain ⟨N,ε,hε,hεmax,Vsep,hVsepOpen,_,hφVsep,C,hC,hsep⟩ :=
    exists_local_source_midpoint_index_separation hp hp1 φ hφ
  obtain ⟨Vrow,hVrowOpen,hφVrow,Krow,hrow⟩ :=
    exists_uniform_sourceSquaredGapPhysicalRows_half_unit hp hp1 φ C hC
  obtain ⟨Ngeom,εgeom,_,_,Vgeom,hVgeomOpen,_,hφVgeom,hcluster,hdisjoint⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ hφ
  have hUopen : IsOpen ((Vsep ∩ Vrow) ∩ Vgeom) :=
    (hVsepOpen.inter hVrowOpen).inter hVgeomOpen
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp
    (hUopen.mem_nhds ⟨⟨hφVsep,hφVrow⟩,hφVgeom⟩)
  let K := max Krow (max (N+1) (Ngeom+1))
  refine ⟨N,ε,hε,hεmax,ball φ r,Metric.isOpen_ball,
    isConnected_ball hr,mem_ball_self hr,C,hC,K,?_⟩
  intro ψ hψ a α hα
  have hψU : ψ ∈ (Vsep ∩ Vrow) ∩ Vgeom := hrU hψ
  have hsmall (n : ℤ) (hn : K ≤ n.natAbs) :
      (C^2/4)*(∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) ≤ 1/2 := by
    have hnrow : Krow ≤ n.natAbs := by dsimp [K] at hn; omega
    exact hrow ψ hψU.1.2 n hnrow
  have hdomain (n : ℤ) (hn : K ≤ n.natAbs)
      (z : ℂ) (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε n) :
      (z,(a,ψ)) ∈ sourceSingleRootQuotientJointDomain hp hp1 Set.univ n := by
    have hNn : N < n.natAbs := by dsimp [K] at hn; omega
    have hNgeomn : Ngeom < n.natAbs := by dsimp [K] at hn; omega
    exact sourceSingleRootQuotientJointDomain_of_tail_isolation
      hp hp1 φ ψ a N Ngeom ε εgeom
        (hcluster ψ hψU.2) hdisjoint n hNn hNgeomn z hz
  exact exists_sourceSingleRootGapCorrectionDiscMajorant
    hp hp1 hq φ ψ a α hα N K ε C hC
      (hsep ψ hψU.1.1) hdomain hsmall

end NLS.ZakharovShabat
