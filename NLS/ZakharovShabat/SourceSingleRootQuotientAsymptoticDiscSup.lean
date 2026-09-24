import NLS.ZakharovShabat.SourceMidpointProductFullDiscSup
import NLS.ZakharovShabat.SourceSingleRootGapCorrectionDiscSup
import NLS.ZakharovShabat.SourceSquaredGapNorm

/-!
# The quotient asymptotic on source discs

The full midpoint-product disc majorant and the squared-gap correction
majorant combine to control the actual analytic single-root quotient.
The two terms retain their distinct sequence exponents.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The first asymptotic of Lemma 10.8 at a fixed source: for
`1 < q < ∞`, quotient disc errors are dominated by the sum of an
`ℓq` midpoint row and an `ℓ^(p/2)` squared-gap row. -/
theorem exists_sourceSingleRootQuotientDiscMajorants
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hq : q ≠ ⊤)
    (φ ψ : CoeffPair p) (a : Coeff p) (α : Coeff q)
    (hα : ∀ m : ℤ,
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m)
    (N K : ℕ) (ε C R : ℝ) (hC : 1 ≤ C) (hR : 0 ≤ R)
    (hdisp : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ R)
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
    ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
      (∀ n : ℤ, max (N+1) K ≤ n.natAbs →
        ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε n,
          ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))-1‖ ≤
            ‖Bq n‖+‖Bg n‖) ∧
      ‖Bq‖ ≤
        (Real.pi⁻¹*(Fourier.hilbertTransformBound hq1 hq+
            ‖Fourier.hilbertSquareCoeffs‖)+
          C*R*‖Fourier.hilbertSquareCoeffs‖)*‖α‖ +
        Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)*
          ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)^2 ∧
      ‖Bg‖ ≤
        (Real.exp (C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖)*C^2) *
          (‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ *
            ‖squaredReciprocalKernel (min 1 (p.toReal/2))
              (lt_min (by norm_num : (1/2:ℝ)<1)
                (by
                  have hpr : 1 < p.toReal :=
                    (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
                  linarith))‖) := by
  obtain ⟨Bq,hmid,_,_,hBq⟩ := exists_sourceMidpointProductDiscSup
    hq1 hq hp hp1 φ ψ N ε C R hC hR hdisp hsep α
  obtain ⟨Bg,hgap,hBg⟩ := exists_sourceSingleRootGapCorrectionDiscMajorant
    hp hp1 hq φ ψ a α hα N K ε C hC hsep hdom hsmall
  refine ⟨Bq,Bg,?_,hBq,hBg⟩
  intro n hn z hz
  have hnN : N < n.natAbs := by omega
  have hnK : K ≤ n.natAbs := by omega
  let P := sourceMidpointProductRow hp hp1 ψ α n z
  let Q := sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))
  calc
    ‖Q-1‖ = ‖P+(Q-(P+1))‖ := by congr 1; ring
    _ ≤ ‖P‖+‖Q-(P+1)‖ := norm_add_le _ _
    _ ≤ ‖Bq n‖+‖Bg n‖ :=
      add_le_add (hmid n hnN z hz) (hgap n hnK z hz)

/-- For an `ℓ¹` numerator displacement, the quotient error has an
`ℓʳ + ℓ^(p/2)` disc majorant for every finite `r > 1`. -/
theorem exists_sourceSingleRootQuotientDiscMajorants_one
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr1 : 1 < r) (hr : r ≠ ⊤)
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (a : Coeff p) (α : Coeff 1)
    (hα : ∀ m : ℤ,
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m)
    (N K : ℕ) (ε C R : ℝ) (hC : 1 ≤ C) (hR : 0 ≤ R)
    (hdisp : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ R)
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
    ∃ Br : Coeff r, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
      (∀ n : ℤ, max (N+1) K ≤ n.natAbs →
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
        (Real.exp (C*‖α‖*‖Coeff.puncturedLattice (1:ℝ≥0∞).conjExponent
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt (1:ℝ≥0∞)
            (1:ℝ≥0∞).conjExponent).mp (by norm_num : (1:ℝ≥0∞) < ⊤))‖)*C^2) *
          (‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ *
            ‖squaredReciprocalKernel (min 1 (p.toReal/2))
              (lt_min (by norm_num : (1/2:ℝ)<1)
                (by
                  have hpr : 1 < p.toReal :=
                    (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
                  linarith))‖) := by
  have hq : (1:ℝ≥0∞) ≠ ⊤ := by norm_num
  obtain ⟨Br,hmid,_,_,hBr⟩ := exists_sourceMidpointProductDiscSup_one
    hr1 hr hp hp1 φ ψ N ε C R hC hR hdisp hsep α
  obtain ⟨Bg,hgap,hBg⟩ := exists_sourceSingleRootGapCorrectionDiscMajorant
    hp hp1 hq φ ψ a α hα N K ε C hC hsep hdom hsmall
  refine ⟨Br,Bg,?_,hBr,?_⟩
  · intro n hn z hz
    have hnN : N < n.natAbs := by omega
    have hnK : K ≤ n.natAbs := by omega
    let P := sourceMidpointProductRow hp hp1 ψ α n z
    let Q := sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))
    calc
      ‖Q-1‖ = ‖P+(Q-(P+1))‖ := by congr 1; ring
      _ ≤ ‖P‖+‖Q-(P+1)‖ := norm_add_le _ _
      _ ≤ ‖Br n‖+‖Bg n‖ :=
        add_le_add (hmid n hnN z hz) (hgap n hnK z hz)
  · exact hBg

/-- One connected neighborhood supplies the midpoint, gap, and
omitted-root domain estimates on the same distant source discs. -/
theorem exists_local_sourceSingleRootQuotientAsymptotic_data
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C R H : ℝ, 1 ≤ C ∧ 0 ≤ R ∧ 0 ≤ H ∧
          ∃ K : ℕ, N < K ∧
            ∀ ψ ∈ V,
              ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ R ∧
              ‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ ≤ H^2 ∧
              (∀ i j : ℤ, i ≠ j →
                ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
                  |((i-j : ℤ) : ℝ)| ≤ C *
                    ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
                      (periodOnePotential_mem ψ) j-z‖) ∧
              (∀ n : ℤ, K ≤ n.natAbs →
                (C^2/4)*(∑' m : ℤ,
                  sourceSquaredGapReciprocalTerm hp hp1 ψ n m) ≤ 1/2) ∧
              (∀ a : Coeff p, ∀ n : ℤ, K ≤ n.natAbs →
                ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                  (z,(a,ψ)) ∈
                    sourceSingleRootQuotientJointDomain hp hp1 Set.univ n) := by
  obtain ⟨N,ε,hε,hεmax,Vmid,hVmidOpen,_,hφVmid,C,R,hC,hR,hmid⟩ :=
    exists_local_sourceMidpointHilbertCorrection_data hp hp1 φ hφ
  obtain ⟨Vrow,hVrowOpen,hφVrow,Krow,hrow⟩ :=
    exists_uniform_sourceSquaredGapPhysicalRows_half_unit hp hp1 φ C hC
  obtain ⟨Ngeom,εgeom,_,_,Vgeom,hVgeomOpen,_,hφVgeom,hcluster,hdisjoint⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ hφ
  obtain ⟨Vgap,hVgapOpen,hφVgap,H,hH,hgap⟩ :=
    exists_local_sourcePeriodicSquaredGapCoeff_bound hp hp1 φ
  have hUopen : IsOpen (((Vmid ∩ Vrow) ∩ Vgeom) ∩ Vgap) :=
    ((hVmidOpen.inter hVrowOpen).inter hVgeomOpen).inter hVgapOpen
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp
    (hUopen.mem_nhds ⟨⟨⟨hφVmid,hφVrow⟩,hφVgeom⟩,hφVgap⟩)
  let K := max Krow (max (N+1) (Ngeom+1))
  have hNK : N < K := by dsimp [K]; omega
  refine ⟨N,ε,hε,hεmax,ball φ r,Metric.isOpen_ball,
    isConnected_ball hr,mem_ball_self hr,C,R,H,hC,hR,hH,K,hNK,?_⟩
  intro ψ hψ
  have hψU : ψ ∈ ((Vmid ∩ Vrow) ∩ Vgeom) ∩ Vgap := hrU hψ
  obtain ⟨hdisp,hsep⟩ := hmid ψ hψU.1.1.1
  refine ⟨hdisp,hgap ψ hψU.2,hsep,?_,?_⟩
  · intro n hn
    have hnrow : Krow ≤ n.natAbs := by dsimp [K] at hn; omega
    exact hrow ψ hψU.1.1.2 n hnrow
  · intro a n hn z hz
    have hNn : N < n.natAbs := by dsimp [K] at hn; omega
    have hNgeomn : Ngeom < n.natAbs := by dsimp [K] at hn; omega
    exact sourceSingleRootQuotientJointDomain_of_tail_isolation
      hp hp1 φ ψ a N Ngeom ε εgeom
        (hcluster ψ hψU.1.2) hdisjoint n hNn hNgeomn z hz

/-- The quotient disc error has locally uniform `ℓq + ℓ^(p/2)`
majorants when `1 < q < ∞`. The constants and index threshold are
common to all nearby source potentials. -/
theorem exists_local_sourceSingleRootQuotientDiscMajorants
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hq : q ≠ ⊤)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C R H : ℝ, 1 ≤ C ∧ 0 ≤ R ∧ 0 ≤ H ∧
          ∃ K : ℕ, N < K ∧
            ∀ ψ ∈ V, ∀ a : Coeff p, ∀ α : Coeff q,
              (∀ m : ℤ,
                displacedRoots a m -
                  canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
                    (periodOnePotential_mem ψ) m = α m) →
              ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
                (∀ n : ℤ, K ≤ n.natAbs →
                  ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                    ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))-1‖ ≤
                      ‖Bq n‖+‖Bg n‖) ∧
                ‖Bq‖ ≤
                  (Real.pi⁻¹*(Fourier.hilbertTransformBound hq1 hq+
                      ‖Fourier.hilbertSquareCoeffs‖)+
                    C*R*‖Fourier.hilbertSquareCoeffs‖)*‖α‖ +
                  Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)*
                    ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)^2 ∧
                ‖Bg‖ ≤
                  (Real.exp (C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
                    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖)*C^2) *
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
  intro ψ hψ a α hα
  obtain ⟨hdisp,hgap,hsep,hsmall,hdom⟩ := hdata ψ hψ
  obtain ⟨Bq,Bg,hpoint,hBq,hBg⟩ :=
    exists_sourceSingleRootQuotientDiscMajorants
      hp hp1 hq1 hq φ ψ a α hα N K ε C R hC hR hdisp hsep
        (hdom a) hsmall
  refine ⟨Bq,Bg,?_,hBq,?_⟩
  · intro n hn z hz
    apply hpoint n (by omega) z hz
  · apply hBg.trans
    gcongr
    exact lp.norm_nonneg' (squaredReciprocalKernel (min 1 (p.toReal/2))
      (lt_min (by norm_num : (1/2:ℝ)<1)
        (by
          have hpr : 1 < p.toReal :=
            (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
          linarith)))

/-- At the `q=1` endpoint the quotient disc error has locally
uniform `ℓʳ + ℓ^(p/2)` majorants for every finite `r > 1`. -/
theorem exists_local_sourceSingleRootQuotientDiscMajorants_one
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr1 : 1 < r) (hr : r ≠ ⊤)
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C R H : ℝ, 1 ≤ C ∧ 0 ≤ R ∧ 0 ≤ H ∧
          ∃ K : ℕ, N < K ∧
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
                  (Real.exp (C*‖α‖*‖Coeff.puncturedLattice (1:ℝ≥0∞).conjExponent
                    ((ENNReal.HolderConjugate.lt_top_iff_one_lt (1:ℝ≥0∞)
                      (1:ℝ≥0∞).conjExponent).mp (by norm_num : (1:ℝ≥0∞) < ⊤))‖)*C^2) *
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
  intro ψ hψ a α hα
  obtain ⟨hdisp,hgap,hsep,hsmall,hdom⟩ := hdata ψ hψ
  obtain ⟨Br,Bg,hpoint,hBr,hBg⟩ :=
    exists_sourceSingleRootQuotientDiscMajorants_one
      hr1 hr hp hp1 φ ψ a α hα N K ε C R hC hR hdisp hsep
        (hdom a) hsmall
  refine ⟨Br,Bg,?_,hBr,?_⟩
  · intro n hn z hz
    apply hpoint n (by omega) z hz
  · apply hBg.trans
    gcongr
    exact lp.norm_nonneg' (squaredReciprocalKernel (min 1 (p.toReal/2))
      (lt_min (by norm_num : (1/2:ℝ)<1)
        (by
          have hpr : 1 < p.toReal :=
            (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
          linarith)))

end NLS.ZakharovShabat
