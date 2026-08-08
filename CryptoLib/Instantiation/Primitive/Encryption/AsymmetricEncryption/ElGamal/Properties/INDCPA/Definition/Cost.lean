import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.Reduction

/-! # Cost and runtime expressions for the DDH reduction -/

namespace CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Oracle
open CryptoLib.Primitive.Encryption.AsymmetricEncryption

universe uCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {measure : NatMeasure M}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

/-- Exact input-dependent budget of the closed reduction. The cost expression
retains the operational order `prepare ; adversary-local ; oracle queries`. -/
def concreteReductionBudget
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : CryptoLib.Oracle.Complexity.TimedOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (sec : CryptoLib.Core.SecPar)
    (challenge : CryptoLib.Assumption.DL.DDH.ChallengeInput F) : M.Cost :=
  if F.parameterSec challenge.parameter = sec then
    M.instAddMonoid.add
      (M.instAddMonoid.add efficiency.prepareCost M.instAddMonoid.zero)
      (M.instAddMonoid.add
        (adversary.localBudget sec (reductionPublicInput F sec challenge))
        (Oracle.Program.repeatCost M
          (adversary.totalQueryBudget sec (reductionPublicInput F sec challenge))
          (efficiency.queryBudget sec)))
  else
    M.instAddMonoid.add efficiency.rejectCost M.instAddMonoid.zero

/-- Uniform natural runtime of the closed reduction, including its reject
branch. -/
def concreteReductionRuntime
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : CryptoLib.Oracle.Complexity.TimedOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    CryptoLib.Core.SecPar → Nat :=
  fun sec =>
    max (efficiency.rejectRuntime sec)
      (efficiency.prepareRuntime sec +
        (adversary.localRuntime sec +
          adversary.totalQueryRuntime sec * efficiency.queryRuntime sec))

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal
