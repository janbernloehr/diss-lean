import NLS.ZakharovShabat.SourceMidpointHilbertDiscSup
import NLS.Fourier.PhysicalMidpointProductRemainder

/-!
# Quadratic midpoint-product remainder on source discs

The numerator root-minus-midpoint displacement enters the midpoint
quotient as a product of factors `1+αₘ/(τₘ-z)`.  The signed linear sum
is kept exactly, while the nonlinear remainder lies in the original
coefficient exponent with a locally uniform quadratic bound.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The nonlinear midpoint-product remainder for every independent
selection of one point from each distant assigned disc. -/
theorem exists_sourceMidpointProductRemainder
    (hq : q ≠ ⊤)
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
    ∃ E : Coeff q,
      (∀ n : ℤ, N < n.natAbs →
        E n =
          (∏' m : ℤ, (1+(if m = n then 0 else
            α m / (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) m-z n))))-1-
            sourceMidpointSignedRow hp hp1 ψ α n (z n)) ∧
      ‖E‖ ≤
        Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)*
          ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)^2 := by
  let τ : ℤ → ℂ := fun m => canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  have hrows : Fourier.SeparatedReciprocalRows {n : ℤ | N < n.natAbs} C R τ z :=
    sourceMidpoint_separatedReciprocalRows hp hp1 φ ψ N ε C R hC hR hdisp hsep z hz
  refine ⟨Fourier.physicalMidpointProductRemainder hq hrows α, ?_,
    Fourier.norm_physicalMidpointProductRemainder_le hq hrows α⟩
  intro n hn
  change (∏' m : ℤ, (1+Fourier.physicalMidpointTerm
      {n : ℤ | N < n.natAbs} τ z α n m))-1-
    ∑' m : ℤ, Fourier.physicalMidpointTerm
      {n : ℤ | N < n.natAbs} τ z α n m = _
  have hnS : n ∈ {n : ℤ | N < n.natAbs} := hn
  simp only [Fourier.physicalMidpointTerm, if_pos hnS,
    sourceMidpointSignedRow, τ]

/-- A connected source neighborhood supplies one uniform quadratic
remainder bound for all nearby potentials and all spectral samples. -/
theorem exists_local_sourceMidpointProductRemainder
    (hq : q ≠ ⊤)
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C R : ℝ, 1 ≤ C ∧ 0 ≤ R ∧
          ∀ ψ ∈ V, ∀ z : ℤ → ℂ,
            (∀ n : ℤ, N < n.natAbs →
              z n ∈ sourceIsolatingDisc hp hp1 φ N ε n) →
            ∀ α : Coeff q, ∃ E : Coeff q,
              (∀ n : ℤ, N < n.natAbs →
                E n =
                  (∏' m : ℤ, (1+(if m = n then 0 else
                    α m / (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
                      (periodOnePotential_mem ψ) m-z n))))-1-
                    sourceMidpointSignedRow hp hp1 ψ α n (z n)) ∧
              ‖E‖ ≤
                Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)*
                  ((C/2)*Fourier.absoluteSampledRowConstant hq*‖α‖)^2 := by
  obtain ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,R,hC,hR,hdata⟩ :=
    exists_local_sourceMidpointHilbertCorrection_data hp hp1 φ hφ
  refine ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,R,hC,hR,?_⟩
  intro ψ hψ z hz α
  obtain ⟨hdisp,hsep⟩ := hdata ψ hψ
  exact exists_sourceMidpointProductRemainder hq hp hp1 φ ψ N ε C R
    hC hR hdisp hsep z hz α

end NLS.ZakharovShabat
