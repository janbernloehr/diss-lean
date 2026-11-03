import NLS.Articles.MKdVBelowL2.PhysicalBirkhoff
import NLS.ZakharovShabat.SourceBirkhoffOriginalExponent
import NLS.Dynamics.ComplexBirkhoffCoordinatesExponent

/-! # A single compatible family of physical Birkhoff maps

The original spectral constructions are chosen for all exponents. Shrinking
to real-centered ball cores makes the complex-domain overlap compatibility
literal, including complex distributions and closed gaps. These are the
family and analytic-domain clauses of article Theorem 1.2. Canonical physical
bracket and accepted Hilbert identification remain separate obligations. -/
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Retain the original angular family and the source domains together. -/
structure OriginalBirkhoffChart (hp : p ≠ ⊤) (hp1 : 1 < p) where
  initial : Set (CoeffPair p)
  ambient : Set (CoeffPair p)
  domain : Set (CoeffPair p)
  roots : (n : ℤ) → CoeffPair p → DeletedCoeff p n
  data : SourceSection14OriginalData hp hp1 initial ambient domain roots

/-- Constructing the original spectral chart leaves no atlas premise to a caller. -/
theorem exists_originalBirkhoffChart (hp : p ≠ ⊤) (hp1 : 1 < p) :
    Nonempty (OriginalBirkhoffChart hp hp1) := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14_original hp hp1
  exact ⟨⟨W₀,W,V,s,D⟩⟩

/-- One fixed chart for each finite exponent, used by all family statements. -/
def originalBirkhoffChart (hp : p ≠ ⊤) (hp1 : 1 < p) : OriginalBirkhoffChart hp hp1 :=
  Classical.choice (exists_originalBirkhoffChart hp hp1)

/-- Common complex physical domain for this exponent's family member. -/
def compatibleBirkhoffDomain (hp : p ≠ ⊤) (hp1 : 1 < p) : Set (PhysicalFL p × PhysicalFL p) :=
  physicalCoefficients ⁻¹' sourceRealBallCore (originalBirkhoffChart hp hp1).domain

/-- The family member uses the chosen original spectral map and exact complex normalization. -/
def compatibleBirkhoff (hp : p ≠ ⊤) (hp1 : 1 < p) :
    (PhysicalFL p × PhysicalFL p) → Coeff p × Coeff p :=
  physicalBirkhoff hp hp1 (originalBirkhoffChart hp hp1).roots

/-- The chosen domain is open and contains every physical real-type distribution pair. -/
theorem compatibleBirkhoffDomain_open_real (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsOpen (compatibleBirkhoffDomain hp hp1) ∧
      ∀ u : PhysicalRealInput p, u.val ∈ compatibleBirkhoffDomain hp hp1 := by
  refine ⟨(sourceRealBallCore_open _).preimage (physicalCoefficients (p := p)).continuous,?_⟩
  intro u
  exact sourceRealBallCore_real_subset _ (originalBirkhoffChart hp hp1).data.complex.source_open
    (originalBirkhoffChart hp hp1).data.complex.real_subset u.property

/-- Each member is genuinely holomorphic on its whole chosen complex domain. -/
theorem compatibleBirkhoff_analytic (hp : p ≠ ⊤) (hp1 : 1 < p) :
    AnalyticOnNhd ℂ (compatibleBirkhoff hp hp1) (compatibleBirkhoffDomain hp hp1) := by
  apply (physicalBirkhoff_analytic (originalBirkhoffChart hp hp1).data.complex).mono
  intro u hu
  exact sourceRealBallCore_subset _ hu

/-- The exact Fourier transport detects equality of physical distributions across exponents. -/
theorem physicalCoefficients_exponent_of_same_distributions (hpq : p ≤ q)
    (u : PhysicalFL p × PhysicalFL p) (v : PhysicalFL q × PhysicalFL q)
    (huv : u.1.val = v.1.val ∧ u.2.val = v.2.val) :
    CoeffPair.exponentInclusion hpq (physicalCoefficients u) = physicalCoefficients v := by
  apply (CoeffPair.toMax q).injective
  apply Prod.ext <;> ext n
  · change (physicalCoefficients u).fst n = (physicalCoefficients v).fst n
    rw [(physicalCoefficients_apply u n).1,(physicalCoefficients_apply v n).1,huv.1]
  · change (physicalCoefficients u).snd n = (physicalCoefficients v).snd n
    rw [(physicalCoefficients_apply u n).2,(physicalCoefficients_apply v n).2,huv.2]

/-- Theorem 1.2(ii) on physical complex intersections, with one fixed family throughout. -/
theorem compatibleBirkhoff_eq_on_intersection
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q) (hpq : p ≤ q)
    (u : PhysicalFL p × PhysicalFL p) (v : PhysicalFL q × PhysicalFL q)
    (hu : u ∈ compatibleBirkhoffDomain hp hp1) (hv : v ∈ compatibleBirkhoffDomain hq hq1)
    (huv : u.1.val = v.1.val ∧ u.2.val = v.2.val) :
    ((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq))
      (compatibleBirkhoff hp hp1 u) = compatibleBirkhoff hq hq1 v := by
  have hc := physicalCoefficients_exponent_of_same_distributions hpq u v huv
  have he := (originalBirkhoffChart hp hp1).data.map_exponent_on_realBallCore
    (originalBirkhoffChart hq hq1).data hpq (physicalCoefficients u) hu (by rw [hc]; exact hv)
  rw [hc] at he
  change ((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq))
    (Birkhoff.rectangularToComplex _) = Birkhoff.rectangularToComplex _
  rw [Birkhoff.rectangularToComplex_exponent,he]

/-- The overlap clause in both exponent orders, expressed as equality of every coordinate. -/
theorem compatibleBirkhoff_coordinates_on_intersection
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q)
    (u : PhysicalFL p × PhysicalFL p) (v : PhysicalFL q × PhysicalFL q)
    (hu : u ∈ compatibleBirkhoffDomain hp hp1) (hv : v ∈ compatibleBirkhoffDomain hq hq1)
    (huv : u.1.val = v.1.val ∧ u.2.val = v.2.val) (n : ℤ) :
    (compatibleBirkhoff hp hp1 u).1 n = (compatibleBirkhoff hq hq1 v).1 n ∧
    (compatibleBirkhoff hp hp1 u).2 n = (compatibleBirkhoff hq hq1 v).2 n := by
  rcases le_total p q with hpq | hqp
  · have h := compatibleBirkhoff_eq_on_intersection hp hp1 hq hq1 hpq u v hu hv huv
    exact ⟨congrArg (fun z : Coeff q × Coeff q => z.1 n) h,
      congrArg (fun z : Coeff q × Coeff q => z.2 n) h⟩
  · have h := compatibleBirkhoff_eq_on_intersection hq hq1 hp hp1 hqp v u hv hu
      ⟨huv.1.symm,huv.2.symm⟩
    exact ⟨(congrArg (fun z : Coeff p × Coeff p => z.1 n) h).symm,
      (congrArg (fun z : Coeff p × Coeff p => z.2 n) h).symm⟩

/-- The same chosen family sends the zero physical distribution to zero. -/
theorem compatibleBirkhoff_zero (hp : p ≠ ⊤) (hp1 : 1 < p) :
    compatibleBirkhoff hp hp1 (0 : PhysicalFL p × PhysicalFL p) = 0 := by
  unfold compatibleBirkhoff physicalBirkhoff
  rw [map_zero,(originalBirkhoffChart hp hp1).data.complex.birkhoff_map_zero,map_zero]

end NLS.Articles.MKdVBelowL2
