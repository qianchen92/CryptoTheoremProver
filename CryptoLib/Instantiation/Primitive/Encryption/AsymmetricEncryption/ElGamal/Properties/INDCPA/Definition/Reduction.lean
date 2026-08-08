import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.Efficiency
import CryptoLib.Primitive.Encryption.AsymmetricEncryption.Properties.INDCPA

/-! # Executable DDH reduction definitions for ElGamal IND-CPA -/

namespace CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Oracle
open CryptoLib.Primitive.Encryption.AsymmetricEncryption
open CryptoLib.Program.Adapter.OneShotChoiceAdd
open scoped DDHParameter

universe uCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {measure : NatMeasure M}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

def reductionPublicInput
    (F : Family M Parameter Scalar Carrier)
    (sec : CryptoLib.Core.SecPar)
    (challenge : CryptoLib.Assumption.DL.DDH.ChallengeInput F) :
    PublicInput Parameter (PublicKey (Carrier := Carrier)) sec where
  param := challenge.parameter
  publicKey := challenge.left

/--
Answer the single IND-CPA challenge from a DDH tuple. In the real DDH game the
answer is a genuine ElGamal encryption; in the random game the second component
is one-time padded by the independent random DDH component.
-/
noncomputable def reductionOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : CryptoLib.Core.SecPar)
    (challenge : CryptoLib.Assumption.DL.DDH.ChallengeInput F)
    (rightMessage : Bool) :
    OracleEnv
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
        (reductionPublicInput F sec challenge)) where
  State := Bool
  init := false
  query
    | INDCPAOracle.challenge, _querySec, used, query =>
        if used then
          PMF.pure ((none : ChallengeResponse (Carrier × Carrier)), true)
        else
          let message : Carrier :=
            if rightMessage then query.2 else query.1
          let pp := F.publicParam challenge.parameter
          PMF.pure
            ((some (challenge.right, pp.addGroup.add message challenge.shared) :
              ChallengeResponse (Carrier × Carrier)), true)

/-- The unique exact primitive algebra used by the executable reduction. -/
noncomputable def reductionAdapter
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F) :
    Adapter M Parameter Carrier where
  add parameter := (F.publicParam parameter).addGroup.add
  costs :=
    { prepare := efficiency.prepareCost
      reject := efficiency.rejectCost
      queryPrefix := efficiency.queryPrefixCost
      querySuffix := efficiency.querySuffixCost
      repeatQuery := efficiency.repeatQueryCost
      add := F.addCost }

/-- Execute the adapter's represented prepare program and project its record. -/
noncomputable def reductionPrepare
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (sec : CryptoLib.Core.SecPar)
    (challenge : CryptoLib.Assumption.DL.DDH.ChallengeInput F) :
    RandCosted M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)) sec) :=
  RandCosted.map
    (fun prepared =>
      { param := prepared.1.down
        publicKey := prepared.2.down })
    (CryptoLib.Program.Procedure.runCosted (algebra (reductionAdapter F efficiency))
      (prepareProgram Parameter Carrier)
      (prepareInputValue challenge.parameter challenge.left))

/-- Execute the adapter's explicitly charged malformed-tag branch. -/
noncomputable def reductionReject
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F) :
    RandCosted M Bool :=
  RandCosted.map ULift.down
    (CryptoLib.Program.Procedure.runCosted (algebra (reductionAdapter F efficiency))
      (rejectProgram Parameter Carrier) (ULift.up ()))

/-- Exact one-shot challenge implementation backed by the query `Code`. -/
noncomputable def costedReductionOracle
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (sec : CryptoLib.Core.SecPar)
    (challenge : CryptoLib.Assumption.DL.DDH.ChallengeInput F)
    (rightMessage : Bool) :
    CostedOracleEnv M
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
        (reductionPublicInput F sec challenge)) where
  State := Bool
  init := false
  query
    | INDCPAOracle.challenge, _querySec, used, query =>
        RandCosted.map
          (fun output =>
            (output.1.map (fun ciphertext =>
              (ciphertext.1.down, ciphertext.2.down)), output.2.down))
          (CryptoLib.Program.Procedure.runCosted
            (algebra (reductionAdapter F efficiency))
            (queryProgram Parameter Carrier rightMessage)
            (queryInputValue challenge.parameter challenge.right
              challenge.shared used query.1 query.2))

/--
The executable reduction.  A valid tag executes prepare, the admitted caller,
and the exact query adapter in order; a malformed tag executes only reject.
-/
noncomputable def concreteDDHReduction
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : CryptoLib.Oracle.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    CryptoLib.Core.Infrastructure.Complexity.ProbabilisticMachine M
      (fun _sec => CryptoLib.Assumption.DL.DDH.ChallengeInput F)
      (fun _sec _challenge => Bool) where
  run := fun sec challenge =>
    if F.parameterSec challenge.parameter = sec then
      RandCosted.bind (reductionPrepare F efficiency sec challenge) fun prepared =>
        adversary.runCosted sec prepared
          (costedReductionOracle F efficiency sec challenge rightMessage)
    else
      reductionReject F efficiency

/--
The pure PMF specification obtained by erasing the concrete reduction's costs
on a correctly tagged challenge. It is deliberately not packaged as a second
zero-cost machine.
-/
noncomputable def semanticDDHReduction
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Oracle.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool)
    (sec : CryptoLib.Core.SecPar)
    (challenge : CryptoLib.Assumption.DL.DDH.ChallengeInput F) : PMF Bool :=
  adversary.runWithEnv sec (reductionPublicInput F sec challenge)
    (reductionOracle F sec challenge rightMessage)

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal
