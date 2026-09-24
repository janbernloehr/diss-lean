import NLS.ZakharovShabat.SourceMidpointHilbertCorrection
import NLS.SequenceSpaces.UniformSelectionSup
import NLS.SequenceSpaces.ExponentEmbedding

/-!
# Disc suprema of signed midpoint reciprocal rows

The sampled Hilbert estimate holds for every independent choice of one
spectral point per distant disc.  A uniform-selection lemma upgrades it
to an `ℓq` bound for the actual coordinatewise disc suprema.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The signed off-diagonal first-order midpoint sum. -/
def sourceMidpointSignedRow
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (α : Coeff q) (n : ℤ) (w : ℂ) : ℂ :=
  ∑' m : ℤ, if m = n then 0 else
    α m / (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m-w)

/-- On all distant source discs, the coordinatewise supremum of the
absolute signed first-order sum belongs to `ℓq` for `1 < q < ∞`.
The constructed real nonnegative sequence is the least pointwise
majorant, hence realizes those disc suprema. -/
theorem exists_sourceMidpointSignedDiscSup
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
          ‖sourceMidpointSignedRow hp hp1 ψ α n w‖ ≤ ‖B n‖) ∧
      (∀ n : ℤ, N < n.natAbs → ∀ t : ℝ, 0 ≤ t →
        (∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
          ‖sourceMidpointSignedRow hp hp1 ψ α n w‖ ≤ t) →
        ‖B n‖ ≤ t) ∧
      (∀ n : ℤ, ¬N < n.natAbs → B n = 0) ∧
      ‖B‖ ≤
        (Real.pi⁻¹*(Fourier.hilbertTransformBound hq1 hq+
            ‖Fourier.hilbertSquareCoeffs‖)+
          C*R*‖Fourier.hilbertSquareCoeffs‖)*‖α‖ := by
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
      C*R*‖Fourier.hilbertSquareCoeffs‖)*‖α‖
  have hK : 0 ≤ K := by
    have hH := Fourier.hilbertTransformBound_nonneg hq1 hq
    have hC0 : 0 ≤ C := by linarith
    dsimp [K]
    positivity
  have hsel (z : ℤ → ℂ) (hz : ∀ n, z n ∈ D n) :
      ∃ b : Coeff q,
        (∀ n ∈ S, b n = sourceMidpointSignedRow hp hp1 ψ α n (z n)) ∧
        ‖b‖ ≤ K := by
    have hz' : ∀ n : ℤ, N < n.natAbs →
        z n ∈ sourceIsolatingDisc hp hp1 φ N ε n := by
      intro n hn
      simpa only [D, if_pos (show n ∈ S from hn)] using hz n
    obtain ⟨b,hb,hbK⟩ := exists_sourceMidpointSignedHilbertRows
      hq1 hq hp hp1 φ ψ N ε C R hC hR hdisp hsep z hz' α
    exact ⟨b,(by intro n hn; exact hb n hn),hbK⟩
  obtain ⟨B,hmajor,hmin,hzero,hB⟩ :=
    exists_uniformSelectionSup hq S D hD
      (sourceMidpointSignedRow hp hp1 ψ α) K hK hsel
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

/-- A single connected neighborhood and constants control the `ℓq`
sequence of disc suprema for every nearby source and every numerator
displacement sequence. -/
theorem exists_local_sourceMidpointSignedDiscSup
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C R : ℝ, 1 ≤ C ∧ 0 ≤ R ∧
          ∀ ψ ∈ V, ∀ α : Coeff q, ∃ B : Coeff q,
            (∀ n : ℤ, N < n.natAbs →
              ∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                ‖sourceMidpointSignedRow hp hp1 ψ α n w‖ ≤ ‖B n‖) ∧
            (∀ n : ℤ, N < n.natAbs → ∀ t : ℝ, 0 ≤ t →
              (∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                ‖sourceMidpointSignedRow hp hp1 ψ α n w‖ ≤ t) →
              ‖B n‖ ≤ t) ∧
            (∀ n : ℤ, ¬N < n.natAbs → B n = 0) ∧
            ‖B‖ ≤
              (Real.pi⁻¹*(Fourier.hilbertTransformBound hq1 hq+
                  ‖Fourier.hilbertSquareCoeffs‖)+
                C*R*‖Fourier.hilbertSquareCoeffs‖)*‖α‖ := by
  obtain ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,R,hC,hR,hdata⟩ :=
    exists_local_sourceMidpointHilbertCorrection_data hp hp1 φ hφ
  refine ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,R,hC,hR,?_⟩
  intro ψ hψ α
  obtain ⟨hdisp,hsep⟩ := hdata ψ hψ
  exact exists_sourceMidpointSignedDiscSup hq1 hq hp hp1 φ ψ N ε C R
    hC hR hdisp hsep α

/-- An `ℓ¹` numerator displacement gives the disc-supremum estimate in
every finite exponent strictly above one, the `ℓ^{1+}` endpoint in
Lemma 10.8. -/
theorem exists_sourceMidpointSignedDiscSup_one
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
          ‖sourceMidpointSignedRow hp hp1 ψ α n w‖ ≤ ‖B n‖) ∧
      (∀ n : ℤ, N < n.natAbs → ∀ t : ℝ, 0 ≤ t →
        (∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
          ‖sourceMidpointSignedRow hp hp1 ψ α n w‖ ≤ t) →
        ‖B n‖ ≤ t) ∧
      (∀ n : ℤ, ¬N < n.natAbs → B n = 0) ∧
      ‖B‖ ≤
        (Real.pi⁻¹*(Fourier.hilbertTransformBound hr1 hr+
            ‖Fourier.hilbertSquareCoeffs‖)+
          C*R*‖Fourier.hilbertSquareCoeffs‖)*‖α‖ := by
  let αr : Coeff r := Coeff.exponentInclusion hr1.le α
  have hrow (n : ℤ) (w : ℂ) :
      sourceMidpointSignedRow hp hp1 ψ αr n w =
        sourceMidpointSignedRow hp hp1 ψ α n w := by
    unfold sourceMidpointSignedRow
    congr 1
  obtain ⟨B,hmajor,hmin,hzero,hB⟩ :=
    exists_sourceMidpointSignedDiscSup hr1 hr hp hp1 φ ψ N ε C R
      hC hR hdisp hsep αr
  refine ⟨B,?_,?_,hzero,?_⟩
  · intro n hn w hw
    simpa only [hrow] using hmajor n hn w hw
  · intro n hn t ht hupper
    apply hmin n hn t ht
    intro w hw
    simpa only [hrow] using hupper w hw
  · have hcoef : 0 ≤ Real.pi⁻¹*(Fourier.hilbertTransformBound hr1 hr+
        ‖Fourier.hilbertSquareCoeffs‖)+
          C*R*‖Fourier.hilbertSquareCoeffs‖ := by
      have hH := Fourier.hilbertTransformBound_nonneg hr1 hr
      have hC0 : 0 ≤ C := by linarith
      positivity
    exact hB.trans (mul_le_mul_of_nonneg_left
      (Coeff.norm_exponentInclusion_le hr1.le α) hcoef)

/-- The `ℓ^{1+}` endpoint estimate holds locally uniformly on one
connected source neighborhood. -/
theorem exists_local_sourceMidpointSignedDiscSup_one
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr1 : 1 < r) (hr : r ≠ ⊤)
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C R : ℝ, 1 ≤ C ∧ 0 ≤ R ∧
          ∀ ψ ∈ V, ∀ α : Coeff 1, ∃ B : Coeff r,
            (∀ n : ℤ, N < n.natAbs →
              ∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                ‖sourceMidpointSignedRow hp hp1 ψ α n w‖ ≤ ‖B n‖) ∧
            (∀ n : ℤ, N < n.natAbs → ∀ t : ℝ, 0 ≤ t →
              (∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                ‖sourceMidpointSignedRow hp hp1 ψ α n w‖ ≤ t) →
              ‖B n‖ ≤ t) ∧
            (∀ n : ℤ, ¬N < n.natAbs → B n = 0) ∧
            ‖B‖ ≤
              (Real.pi⁻¹*(Fourier.hilbertTransformBound hr1 hr+
                  ‖Fourier.hilbertSquareCoeffs‖)+
                C*R*‖Fourier.hilbertSquareCoeffs‖)*‖α‖ := by
  obtain ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,R,hC,hR,hdata⟩ :=
    exists_local_sourceMidpointHilbertCorrection_data hp hp1 φ hφ
  refine ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,R,hC,hR,?_⟩
  intro ψ hψ α
  obtain ⟨hdisp,hsep⟩ := hdata ψ hψ
  exact exists_sourceMidpointSignedDiscSup_one hr1 hr hp hp1 φ ψ N ε C R
    hC hR hdisp hsep α

end NLS.ZakharovShabat
