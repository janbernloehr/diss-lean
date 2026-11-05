import NLS.Poisson.GardnerHamiltonianDirection

/-! The physical H1 gradient of its actual bounded Hminus-one pairing
functional is exactly the supplied gradient, with no conjugation or
frequency normalization change. -/
noncomputable section
open Complex
namespace NLS.Poisson

theorem hminusCotangentCLM_sobolevBilinearPairing
    (g : WeightedCoeff (Weight.sobolev 1) 2) :
    hminusCotangentCLM ((WeightedCoeff.sobolevBilinearPairing (p:=2) (q:=2) 1) g)=g := by
  apply Subtype.ext
  funext k
  rw [hminusCotangentCLM_apply,WeightedCoeff.sobolevBilinearPairing_apply]
  simp [WeightedCoeff.ofFinsupp_apply,Finsupp.single_apply]

end NLS.Poisson
