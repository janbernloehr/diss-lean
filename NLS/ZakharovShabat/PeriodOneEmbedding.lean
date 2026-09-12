import NLS.Fourier.PeriodOneCoefficients
import NLS.SequenceSpaces.PairNorm
import NLS.ZakharovShabat.PeriodicParity

/-!
# Period-one potential parameters in the period-two operator

Insert both potential components at even frequencies. The map preserves the
component-sum norm at finite exponents and covers exactly the even coefficient
potentials. For absolutely summable inputs it is the actual Fourier map of
continuous period-one functions, and the existing resolvent parity theorems
apply without a separately supplied even-support hypothesis.
-/

noncomputable section
open Complex Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Period doubling is an isometry in the finite-exponent source pair norm. -/
def periodOnePair : CoeffPair p →ₗᵢ[ℂ] CoeffPair p :=
  Coeff.periodDouble.withLpProdMap p Coeff.periodDouble

@[simp] theorem periodOnePair_ofLp (u : CoeffPair p) :
    (periodOnePair u).ofLp = (Coeff.periodDouble u.fst, Coeff.periodDouble u.snd) := rfl

@[simp] theorem norm_periodOnePair (u : CoeffPair p) : ‖periodOnePair u‖ = ‖u‖ := periodOnePair.norm_map u

/-- The corresponding parameter for the existing maximum-norm coefficient operator. -/
def periodOnePotential : CoeffPair p →L[ℂ] PairSpace p :=
  (CoeffPair.toMax p).toContinuousLinearMap.comp periodOnePair.toContinuousLinearMap

@[simp] theorem periodOnePotential_apply (u : CoeffPair p) :
    periodOnePotential u = (Coeff.periodDouble u.fst, Coeff.periodDouble u.snd) := rfl

/-- Every period-one parameter has even Fourier support in the period-two operator. -/
theorem periodOnePotential_mem (u : CoeffPair p) : periodOnePotential u ∈ pairParitySubspace 0 :=
  ⟨Coeff.periodDouble_mem u.fst, Coeff.periodDouble_mem u.snd⟩

/-- The operator parameter map is contractive from the actual finite-exponent pair norm. -/
theorem norm_periodOnePotential_le (u : CoeffPair p) : ‖periodOnePotential u‖ ≤ ‖u‖ := by
  exact (CoeffPair.norm_toMax_le (periodOnePair u)).trans_eq (norm_periodOnePair u)

/-- The canonical embedding covers exactly the entire even potential subspace. -/
theorem range_periodOnePotential : periodOnePotential (p := p).range = pairParitySubspace 0 := by
  ext φ
  constructor
  · rintro ⟨u, rfl⟩
    exact periodOnePotential_mem u
  · intro hφ
    refine ⟨WithLp.toLp p (Coeff.periodHalve φ.1, Coeff.periodHalve φ.2), ?_⟩
    change (Coeff.periodDouble (Coeff.periodHalve φ.1), Coeff.periodDouble (Coeff.periodHalve φ.2)) = φ
    rw [Coeff.periodDouble_periodHalve, Coeff.periodDouble_periodHalve,
      (Coeff.parityProjection_eq_self_iff 0 φ.1).mpr hφ.1,
      (Coeff.parityProjection_eq_self_iff 0 φ.2).mpr hφ.2]

/-- At absolute summability, these are the actual period-two integrals of continuous period-one components. -/
theorem periodOnePotential_physical_coefficients (u : CoeffPair 1) (n : ℤ) :
    (periodOnePotential u).1 n = Fourier.periodTwoCoefficient (Fourier.periodOneSynthesis u.fst) n ∧
    (periodOnePotential u).2 n = Fourier.periodTwoCoefficient (Fourier.periodOneSynthesis u.snd) n := by
  simp only [periodOnePotential_apply, Fourier.periodTwoCoefficient_periodOneSynthesis, and_self]

/-- The resolvent of an embedded period-one potential commutes with both parity projections. -/
theorem periodOnePotential_resolvent_commute (hp : p ≠ ⊤) (u : CoeffPair p) (r : ℤ) (z : ℂ)
    (hz : z ∈ resolventSet hp (periodOnePotential u)) :
    Commute (pairParityProjection r) (resolvent hp (periodOnePotential u) z) :=
  pairParityProjection_commute_resolvent hp _ (periodOnePotential_mem u) r z hz

/-- The associated circular spectral projections preserve periodic and antiperiodic sectors. -/
theorem periodOnePotential_contour_commute (hp : p ≠ ⊤) (u : CoeffPair p) (r : ℤ) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ resolventSet hp (periodOnePotential u)) :
    Commute (pairParityProjection r) (resolventCircleIntegral hp (periodOnePotential u) c R) :=
  pairParityProjection_commute_contour hp _ (periodOnePotential_mem u) r c R hR hc

end NLS.ZakharovShabat
