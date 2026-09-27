import NLS.ZakharovShabat.SourceSingleRootQuotientAsymptoticDiscSup

/-!
# A common source domain for all endpoint exponents

The geometric disc and gap estimates in the single-root quotient
argument do not depend on the target Banach exponent. When the
critical-to-midpoint offset belongs to `ℓ¹`, the same source domain
therefore supports the quotient-disc majorants for every finite
exponent strictly above one.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One complex source neighborhood works for all finite `r > 1` in
the `ℓ¹` endpoint version of the quotient-disc estimate. The norm
bounds may depend on `r`, but the neighborhood and tail cutoff do not. -/
theorem exists_local_sourceSingleRootQuotientDiscMajorants_one_allExponents
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C R H : ℝ, 1 ≤ C ∧ 0 ≤ R ∧ 0 ≤ H ∧
          ∃ K : ℕ, N < K ∧
            ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)] (hr1 : 1 < r) (hr : r ≠ ⊤),
              ∀ ψ ∈ V, ∀ a : Coeff p, ∀ α : Coeff 1,
                (∀ m : ℤ,
                  displacedRoots a m -
                    canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
                      (periodOnePotential_mem ψ) m = α m) →
                ∃ Br : Coeff r, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
                  (∀ n : ℤ, K ≤ n.natAbs →
                    ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                      ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))-1‖ ≤
                        ‖Br n‖+‖Bg n‖) ∧
                  ‖Br‖ ≤
                    (Real.pi⁻¹*(Fourier.hilbertTransformBound hr1 hr+
                        ‖Fourier.hilbertSquareCoeffs‖)+
                      C*R*‖Fourier.hilbertSquareCoeffs‖)*
                        ‖Coeff.exponentInclusion hr1.le α‖ +
                    Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hr*
                        ‖Coeff.exponentInclusion hr1.le α‖)*
                      ((C/2)*Fourier.absoluteSampledRowConstant hr*
                        ‖Coeff.exponentInclusion hr1.le α‖)^2 ∧
                  ‖Bg‖ ≤
                    (Real.exp (C*‖α‖*‖Coeff.puncturedLattice
                      (1:ℝ≥0∞).conjExponent
                      ((ENNReal.HolderConjugate.lt_top_iff_one_lt (1:ℝ≥0∞)
                        (1:ℝ≥0∞).conjExponent).mp
                        (by norm_num : (1:ℝ≥0∞) < ⊤))‖)*C^2) *
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
  intro r hrFact hr1 hr ψ hψ a α hα
  obtain ⟨hdisp,hgap,hsep,hsmall,hdom⟩ := hdata ψ hψ
  obtain ⟨Br,Bg,hpoint,hBr,hBg⟩ :=
    exists_sourceSingleRootQuotientDiscMajorants_one
      hr1 hr hp hp1 φ ψ a α hα N K ε C R hC hR hdisp hsep
        (hdom a) hsmall
  refine ⟨Br,Bg,?_,hBr,?_⟩
  · intro n hn z hz
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
