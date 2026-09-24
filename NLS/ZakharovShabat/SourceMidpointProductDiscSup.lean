import NLS.ZakharovShabat.SourceMidpointProductRemainder

/-!
# Disc suprema of the quadratic midpoint-product remainder

The product remainder is uniformly bounded for every independent
choice of one point per distant disc.  Its coordinatewise supremum
therefore belongs to the original coefficient exponent, including at
the `ℓ¹` endpoint.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The infinite midpoint product minus its signed linear term. -/
def sourceMidpointProductRemainderRow
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (α : Coeff q) (n : ℤ) (w : ℂ) : ℂ :=
  (∏' m : ℤ, (1+(if m = n then 0 else
    α m / (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m-w))))-1-
    sourceMidpointSignedRow hp hp1 ψ α n w

/-- The least pointwise majorant of the quadratic midpoint-product
remainder on distant source discs lies in `ℓq`. -/
theorem exists_sourceMidpointProductRemainderDiscSup
    (hq : q ≠ ⊤)
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
          ‖sourceMidpointProductRemainderRow hp hp1 ψ α n w‖ ≤ ‖B n‖) ∧
      (∀ n : ℤ, N < n.natAbs → ∀ t : ℝ, 0 ≤ t →
        (∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
          ‖sourceMidpointProductRemainderRow hp hp1 ψ α n w‖ ≤ t) →
        ‖B n‖ ≤ t) ∧
      (∀ n : ℤ, ¬N < n.natAbs → B n = 0) ∧
      ‖B‖ ≤
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
    Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)*
      ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsel (z : ℤ → ℂ) (hz : ∀ n, z n ∈ D n) :
      ∃ b : Coeff q,
        (∀ n ∈ S, b n = sourceMidpointProductRemainderRow hp hp1 ψ α n (z n)) ∧
        ‖b‖ ≤ K := by
    have hz' : ∀ n : ℤ, N < n.natAbs →
        z n ∈ sourceIsolatingDisc hp hp1 φ N ε n := by
      intro n hn
      simpa only [D, if_pos (show n ∈ S from hn)] using hz n
    obtain ⟨b,hb,hbK⟩ := exists_sourceMidpointProductRemainder
      hq hp hp1 φ ψ N ε C R hC hR hdisp hsep z hz' α
    exact ⟨b,(by intro n hn; exact hb n hn),hbK⟩
  obtain ⟨B,hmajor,hmin,hzero,hB⟩ :=
    NLS.exists_uniformSelectionSup hq S D hD
      (sourceMidpointProductRemainderRow hp hp1 ψ α) K hK hsel
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

/-- The quadratic remainder-disc majorant has one norm bound on a
connected neighborhood of any real-type source. -/
theorem exists_local_sourceMidpointProductRemainderDiscSup
    (hq : q ≠ ⊤)
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C R : ℝ, 1 ≤ C ∧ 0 ≤ R ∧
          ∀ ψ ∈ V, ∀ α : Coeff q, ∃ B : Coeff q,
            (∀ n : ℤ, N < n.natAbs →
              ∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                ‖sourceMidpointProductRemainderRow hp hp1 ψ α n w‖ ≤ ‖B n‖) ∧
            (∀ n : ℤ, N < n.natAbs → ∀ t : ℝ, 0 ≤ t →
              (∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                ‖sourceMidpointProductRemainderRow hp hp1 ψ α n w‖ ≤ t) →
                ‖B n‖ ≤ t) ∧
            (∀ n : ℤ, ¬N < n.natAbs → B n = 0) ∧
            ‖B‖ ≤
              Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)*
                ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)^2 := by
  obtain ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,R,hC,hR,hdata⟩ :=
    exists_local_sourceMidpointHilbertCorrection_data hp hp1 φ hφ
  refine ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,R,hC,hR,?_⟩
  intro ψ hψ α
  obtain ⟨hdisp,hsep⟩ := hdata ψ hψ
  exact exists_sourceMidpointProductRemainderDiscSup hq hp hp1 φ ψ N ε C R
    hC hR hdisp hsep α

end NLS.ZakharovShabat
