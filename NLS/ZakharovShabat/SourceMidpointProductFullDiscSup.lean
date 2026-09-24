import NLS.ZakharovShabat.SourceMidpointProductDiscSup
import NLS.SequenceSpaces.ExponentEmbedding

/-!
# The full midpoint product on source discs

The signed reciprocal row and the quadratic product remainder together
control the infinite midpoint product. Independent spectral samples
give the coordinatewise disc supremum in the original exponent when
`1 < q < ∞`.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The infinite off-diagonal midpoint product minus one. -/
def sourceMidpointProductRow
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (α : Coeff q) (n : ℤ) (w : ℂ) : ℂ :=
  (∏' m : ℤ, (1+(if m = n then 0 else
    α m / (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m-w))))-1

omit [Fact (1 ≤ q)] in
theorem sourceMidpointProductRow_eq_signed_add_remainder
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (α : Coeff q) (n : ℤ) (w : ℂ) :
    sourceMidpointProductRow hp hp1 ψ α n w =
      sourceMidpointSignedRow hp hp1 ψ α n w +
        sourceMidpointProductRemainderRow hp hp1 ψ α n w := by
  unfold sourceMidpointProductRow sourceMidpointProductRemainderRow
  ring

/-- The midpoint product is an `ℓq` row sequence for every independent
selection of spectral points in the distant source discs. -/
theorem exists_sourceMidpointProductRows
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε C R : ℝ) (hC : 1 ≤ C) (hR : 0 ≤ R)
    (hdisp : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ R)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-w‖)
    (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, N < n.natAbs →
      z n ∈ sourceIsolatingDisc hp hp1 φ N ε n)
    (α : Coeff q) :
    ∃ b : Coeff q,
      (∀ n : ℤ, N < n.natAbs →
        b n = sourceMidpointProductRow hp hp1 ψ α n (z n)) ∧
      ‖b‖ ≤
        (Real.pi⁻¹*(Fourier.hilbertTransformBound hq1 hq+
            ‖Fourier.hilbertSquareCoeffs‖)+
          C*R*‖Fourier.hilbertSquareCoeffs‖)*‖α‖ +
        Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)*
          ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)^2 := by
  obtain ⟨L,hL,hLn⟩ := exists_sourceMidpointSignedHilbertRows
    hq1 hq hp hp1 φ ψ N ε C R hC hR hdisp hsep z hz α
  obtain ⟨E,hE,hEn⟩ := exists_sourceMidpointProductRemainder
    hq hp hp1 φ ψ N ε C R hC hR hdisp hsep z hz α
  refine ⟨L+E,?_,?_⟩
  · intro n hn
    rw [lp.coeFn_add, Pi.add_apply, hL n hn, hE n hn]
    exact (sourceMidpointProductRow_eq_signed_add_remainder hp hp1 ψ α n (z n)).symm
  · exact (norm_add_le L E).trans (add_le_add hLn hEn)

/-- The least pointwise majorant of the full midpoint-product error on
distant source discs lies in `ℓq` for `1 < q < ∞`. -/
theorem exists_sourceMidpointProductDiscSup
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε C R : ℝ) (hC : 1 ≤ C) (hR : 0 ≤ R)
    (hdisp : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ R)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-w‖)
    (α : Coeff q) :
    ∃ B : Coeff q,
      (∀ n : ℤ, N < n.natAbs →
        ∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
          ‖sourceMidpointProductRow hp hp1 ψ α n w‖ ≤ ‖B n‖) ∧
      (∀ n : ℤ, N < n.natAbs → ∀ t : ℝ, 0 ≤ t →
        (∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
          ‖sourceMidpointProductRow hp hp1 ψ α n w‖ ≤ t) →
        ‖B n‖ ≤ t) ∧
      (∀ n : ℤ, ¬N < n.natAbs → B n = 0) ∧
      ‖B‖ ≤
        (Real.pi⁻¹*(Fourier.hilbertTransformBound hq1 hq+
            ‖Fourier.hilbertSquareCoeffs‖)+
          C*R*‖Fourier.hilbertSquareCoeffs‖)*‖α‖ +
        Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)*
          ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)^2 := by
  let S : Set ℤ := {n | N < n.natAbs}
  let D (n : ℤ) : Set ℂ :=
    if n ∈ S then sourceIsolatingDisc hp hp1 φ N ε n else Set.univ
  have hD (n : ℤ) : (D n).Nonempty := by
    by_cases hn : n ∈ S
    · have hn' : N < n.natAbs := hn
      refine ⟨(Real.pi : ℂ)*n, ?_⟩
      simp [D, hn, sourceIsolatingDisc, not_le.mpr hn',
        refinedResonantDisk, Real.pi_pos]
    · exact ⟨0, by simp [D, hn]⟩
  let K : ℝ :=
    (Real.pi⁻¹*(Fourier.hilbertTransformBound hq1 hq+
        ‖Fourier.hilbertSquareCoeffs‖)+
      C*R*‖Fourier.hilbertSquareCoeffs‖)*‖α‖ +
    Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)*
      ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)^2
  have hK : 0 ≤ K := by
    have hH := Fourier.hilbertTransformBound_nonneg hq1 hq
    have hC0 : 0 ≤ C := by linarith
    dsimp [K]
    positivity
  have hsel (z : ℤ → ℂ) (hz : ∀ n, z n ∈ D n) :
      ∃ b : Coeff q,
        (∀ n ∈ S, b n = sourceMidpointProductRow hp hp1 ψ α n (z n)) ∧
        ‖b‖ ≤ K := by
    have hz' : ∀ n : ℤ, N < n.natAbs →
        z n ∈ sourceIsolatingDisc hp hp1 φ N ε n := by
      intro n hn
      simpa only [D, if_pos (show n ∈ S from hn)] using hz n
    obtain ⟨b,hb,hbK⟩ := exists_sourceMidpointProductRows
      hq1 hq hp hp1 φ ψ N ε C R hC hR hdisp hsep z hz' α
    exact ⟨b,(by intro n hn; exact hb n hn),hbK⟩
  obtain ⟨B,hmajor,hmin,hzero,hB⟩ :=
    NLS.exists_uniformSelectionSup hq S D hD
      (sourceMidpointProductRow hp hp1 ψ α) K hK hsel
  refine ⟨B,?_,?_,?_,hB⟩
  · intro n hn w hw
    apply hmajor n hn w
    simpa only [D, if_pos (show n ∈ S from hn)] using hw
  · intro n hn t ht hupper
    apply hmin n hn t ht
    intro w hw
    apply hupper w
    simpa only [D, if_pos (show n ∈ S from hn)] using hw
  · intro n hn
    exact hzero n hn

/-- One connected source neighborhood supplies a uniform `ℓq`
midpoint-product disc bound. -/
theorem exists_local_sourceMidpointProductDiscSup
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C R : ℝ, 1 ≤ C ∧ 0 ≤ R ∧
          ∀ ψ ∈ V, ∀ α : Coeff q, ∃ B : Coeff q,
            (∀ n : ℤ, N < n.natAbs →
              ∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                ‖sourceMidpointProductRow hp hp1 ψ α n w‖ ≤ ‖B n‖) ∧
            (∀ n : ℤ, N < n.natAbs → ∀ t : ℝ, 0 ≤ t →
              (∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                ‖sourceMidpointProductRow hp hp1 ψ α n w‖ ≤ t) →
                ‖B n‖ ≤ t) ∧
            (∀ n : ℤ, ¬N < n.natAbs → B n = 0) ∧
            ‖B‖ ≤
              (Real.pi⁻¹*(Fourier.hilbertTransformBound hq1 hq+
                  ‖Fourier.hilbertSquareCoeffs‖)+
                C*R*‖Fourier.hilbertSquareCoeffs‖)*‖α‖ +
              Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)*
                ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)^2 := by
  obtain ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,R,hC,hR,hdata⟩ :=
    exists_local_sourceMidpointHilbertCorrection_data hp hp1 φ hφ
  refine ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,R,hC,hR,?_⟩
  intro ψ hψ α
  obtain ⟨hdisp,hsep⟩ := hdata ψ hψ
  exact exists_sourceMidpointProductDiscSup hq1 hq hp hp1 φ ψ N ε C R
    hC hR hdisp hsep α

/-- At `q=1`, the full midpoint-product disc supremum belongs to
every finite `ℓʳ` with `1 < r`, as in the `ℓ^{1+}` term of Lemma 10.8. -/
theorem exists_sourceMidpointProductDiscSup_one
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr1 : 1 < r) (hr : r ≠ ⊤)
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε C R : ℝ) (hC : 1 ≤ C) (hR : 0 ≤ R)
    (hdisp : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ R)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-w‖)
    (α : Coeff 1) :
    ∃ B : Coeff r,
      (∀ n : ℤ, N < n.natAbs →
        ∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
          ‖sourceMidpointProductRow hp hp1 ψ α n w‖ ≤ ‖B n‖) ∧
      (∀ n : ℤ, N < n.natAbs → ∀ t : ℝ, 0 ≤ t →
        (∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
          ‖sourceMidpointProductRow hp hp1 ψ α n w‖ ≤ t) →
        ‖B n‖ ≤ t) ∧
      (∀ n : ℤ, ¬N < n.natAbs → B n = 0) ∧
      ‖B‖ ≤
        (Real.pi⁻¹*(Fourier.hilbertTransformBound hr1 hr+
            ‖Fourier.hilbertSquareCoeffs‖)+
          C*R*‖Fourier.hilbertSquareCoeffs‖)*
            ‖Coeff.exponentInclusion hr1.le α‖ +
        Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hr*
            ‖Coeff.exponentInclusion hr1.le α‖)*
          ((C/2)*Fourier.absoluteSampledRowConstant hr*
            ‖Coeff.exponentInclusion hr1.le α‖)^2 := by
  let αr : Coeff r := Coeff.exponentInclusion hr1.le α
  have hrow (n : ℤ) (w : ℂ) :
      sourceMidpointProductRow hp hp1 ψ αr n w =
        sourceMidpointProductRow hp hp1 ψ α n w := by
    unfold sourceMidpointProductRow
    congr 1
  obtain ⟨B,hmajor,hmin,hzero,hB⟩ :=
    exists_sourceMidpointProductDiscSup hr1 hr hp hp1 φ ψ N ε C R
      hC hR hdisp hsep αr
  refine ⟨B,?_,?_,hzero,?_⟩
  · intro n hn w hw
    simpa only [hrow] using hmajor n hn w hw
  · intro n hn t ht hupper
    apply hmin n hn t ht
    intro w hw
    simpa only [hrow] using hupper w hw
  · exact hB

/-- The `ℓ^{1+}` midpoint-product bound holds on a single connected
source neighborhood. -/
theorem exists_local_sourceMidpointProductDiscSup_one
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr1 : 1 < r) (hr : r ≠ ⊤)
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C R : ℝ, 1 ≤ C ∧ 0 ≤ R ∧
          ∀ ψ ∈ V, ∀ α : Coeff 1, ∃ B : Coeff r,
            (∀ n : ℤ, N < n.natAbs →
              ∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                ‖sourceMidpointProductRow hp hp1 ψ α n w‖ ≤ ‖B n‖) ∧
            (∀ n : ℤ, N < n.natAbs → ∀ t : ℝ, 0 ≤ t →
              (∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                ‖sourceMidpointProductRow hp hp1 ψ α n w‖ ≤ t) →
                ‖B n‖ ≤ t) ∧
            (∀ n : ℤ, ¬N < n.natAbs → B n = 0) ∧
            ‖B‖ ≤
              (Real.pi⁻¹*(Fourier.hilbertTransformBound hr1 hr+
                  ‖Fourier.hilbertSquareCoeffs‖)+
                C*R*‖Fourier.hilbertSquareCoeffs‖)*
                  ‖Coeff.exponentInclusion hr1.le α‖ +
              Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hr*
                  ‖Coeff.exponentInclusion hr1.le α‖)*
                ((C/2)*Fourier.absoluteSampledRowConstant hr*
                  ‖Coeff.exponentInclusion hr1.le α‖)^2 := by
  obtain ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,R,hC,hR,hdata⟩ :=
    exists_local_sourceMidpointHilbertCorrection_data hp hp1 φ hφ
  refine ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,R,hC,hR,?_⟩
  intro ψ hψ α
  obtain ⟨hdisp,hsep⟩ := hdata ψ hψ
  exact exists_sourceMidpointProductDiscSup_one hr1 hr hp hp1 φ ψ N ε C R
    hC hR hdisp hsep α

end NLS.ZakharovShabat
