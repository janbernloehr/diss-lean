import NLS.ZakharovShabat.SourceDeletedFreeSine

/-!
# The sine-product consequence of Lemma 10.8

For free numerator roots the deleted numerator is the filled sine
quotient. The source midpoint displacement is then the negative of
the numerator-minus-midpoint coefficient. The quotient asymptotic
therefore controls the sine quotient over the omitted standard-root
product on the distant source discs.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The displacement of free numerator roots from the moving source
midpoints. -/
def sourceFreeNumeratorMidpointDisplacement
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) : Coeff p :=
  -sourcePeriodicMidpointDisplacement hp hp1 ψ

theorem sourceFreeNumeratorMidpointDisplacement_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ) :
    displacedRoots (0 : Coeff p) m -
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m =
          sourceFreeNumeratorMidpointDisplacement hp hp1 ψ m := by
  simp only [sourceFreeNumeratorMidpointDisplacement, lp.coeFn_neg, Pi.neg_apply,
    sourcePeriodicMidpointDisplacement_apply, displacedRoots, lp.coeFn_zero,
    Pi.zero_apply, add_zero]
  ring

/-- The free-numerator analytic quotient is exactly the filled sine
quotient over the deleted standard-root product. -/
theorem sourceSingleRootQuotientJointProduct_free_eq_sine_div
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (z : ℂ) :
    sourceSingleRootQuotientJointProduct hp hp1 n (z,((0 : Coeff p),ψ)) =
      freeSineQuotient n z /
        sourceStandardRootOmittedJointProduct hp hp1 n (z,ψ) := by
  change jointDeletedSingleSpectralProduct n (z,(0 : Coeff p)) /
      sourceStandardRootOmittedJointProduct hp hp1 n (z,ψ) = _
  rw [← congrFun (jointDeletedSingleSpectralProduct_zero_eq_freeSineQuotient
    hp hp1 n) z]

/-- The sine quotient divided by the omitted standard-root product has
locally uniform `ℓp + ℓ^(p/2)` disc majorants. The first majorant also
covers the `ℓ^{1+}` term in the statement of Lemma 10.8. -/
theorem exists_local_sourceFreeSineQuotientDiscMajorants
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C R H : ℝ, 1 ≤ C ∧ 0 ≤ R ∧ 0 ≤ H ∧
          ∃ K : ℕ, N < K ∧
            ∀ ψ ∈ V,
              ‖sourceFreeNumeratorMidpointDisplacement hp hp1 ψ‖ ≤ R ∧
              ∃ Bp : Coeff p, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
                (∀ n : ℤ, K ≤ n.natAbs →
                  ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                    ‖freeSineQuotient n z /
                      sourceStandardRootOmittedJointProduct hp hp1 n (z,ψ)-1‖ ≤
                        ‖Bp n‖+‖Bg n‖) ∧
                ‖Bp‖ ≤
                  (Real.pi⁻¹*(Fourier.hilbertTransformBound hp1 hp+
                      ‖Fourier.hilbertSquareCoeffs‖)+
                    C*R*‖Fourier.hilbertSquareCoeffs‖)*
                      ‖sourceFreeNumeratorMidpointDisplacement hp hp1 ψ‖ +
                  Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hp*
                      ‖sourceFreeNumeratorMidpointDisplacement hp hp1 ψ‖)*
                    ((C/2)*Fourier.absoluteSampledRowConstant hp*
                      ‖sourceFreeNumeratorMidpointDisplacement hp hp1 ψ‖)^2 ∧
                ‖Bg‖ ≤
                  (Real.exp (C*‖sourceFreeNumeratorMidpointDisplacement hp hp1 ψ‖*
                    ‖Coeff.puncturedLattice p.conjExponent
                      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖)*C^2) *
                    (H^2 *
                      ‖squaredReciprocalKernel (min 1 (p.toReal/2))
                        (lt_min (by norm_num : (1/2:ℝ)<1)
                          (by
                            have hpr : 1 < p.toReal :=
                              (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
                            linarith))‖) := by
  obtain ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,R,H,hC,hR,hH,K,hNK,hdata⟩ :=
    exists_local_sourceSingleRootQuotientAsymptotic_data hp hp1 φ hφ
  refine ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,R,H,hC,hR,hH,K,hNK,?_⟩
  intro ψ hψ
  obtain ⟨hdisp,hgap,hsep,hsmall,hdom⟩ := hdata ψ hψ
  let α : Coeff p := sourceFreeNumeratorMidpointDisplacement hp hp1 ψ
  have hα (m : ℤ) :
      displacedRoots (0 : Coeff p) m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m :=
    sourceFreeNumeratorMidpointDisplacement_apply hp hp1 ψ m
  have hαnorm : ‖α‖ ≤ R := by
    simpa only [α, sourceFreeNumeratorMidpointDisplacement, norm_neg] using hdisp
  obtain ⟨Bp,Bg,hpoint,hBp,hBg⟩ :=
    exists_sourceSingleRootQuotientDiscMajorants
      hp hp1 hp1 hp φ ψ 0 α hα N K ε C R hC hR hdisp hsep
        (hdom 0) hsmall
  refine ⟨hαnorm,Bp,Bg,?_,hBp,?_⟩
  · intro n hn z hz
    rw [← sourceSingleRootQuotientJointProduct_free_eq_sine_div hp hp1 ψ n z]
    exact hpoint n (by omega) z hz
  · apply hBg.trans
    gcongr
    exact lp.norm_nonneg' (squaredReciprocalKernel (min 1 (p.toReal/2))
      (lt_min (by norm_num : (1/2:ℝ)<1)
        (by
          have hpr : 1 < p.toReal :=
            (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
          linarith)))

end NLS.ZakharovShabat
