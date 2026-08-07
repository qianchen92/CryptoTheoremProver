import CryptoLib.Core.Infrastructure.Computation.Game
import CryptoLib.Core.Infrastructure.UC.Complexity
import CryptoLib.Core.Infrastructure.UC.Composition

namespace CryptoLib.Core.Infrastructure.UC

open CryptoLib.Core.Infrastructure.Asymptotic
open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uAddress uPayload uPort uCapability
universe uState uLeakage uErasure uOutput

variable {M : CostModel.{uCost}}
variable {EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress :
  Type uAddress}
variable [DecidableEq EnvironmentAddress] [DecidableEq SystemAddress]
variable [DecidableEq AdversarialAddress] [DecidableEq NetworkAddress]
variable {schema : PortSchema.{uAddress, uPayload, uPort, uCapability}
  (WorldAddress EnvironmentAddress SystemAddress
    AdversarialAddress NetworkAddress)}

namespace RealWorld

/--
Erase exact costs from the unique real-world runner and map its observable
outcome to a Boolean decision.  The fuel is an execution parameter, not a
runtime check and not a field of a cost certificate.
-/
noncomputable def execution
    (world : RealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema)
    (fuel : CryptoLib.Core.SecPar → Nat) : Game Bool :=
  fun sec =>
    PMF.map
      (fun result => result.outcome.toBool (world.decision sec))
      (RandCosted.valueDist (world.runCosted sec (fuel sec)))

end RealWorld

namespace IdealWorld

/--
Erase exact costs from the unique ideal-world runner and map its observable
outcome to a Boolean decision.
-/
noncomputable def execution
    (world : IdealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema)
    (fuel : CryptoLib.Core.SecPar → Nat) : Game Bool :=
  fun sec =>
    PMF.map
      (fun result => result.outcome.toBool (world.decision sec))
      (RandCosted.valueDist (world.runCosted sec (fuel sec)))

end IdealWorld

/--
A real closed world and the complete exact-to-measured PPT execution
certificate for that same world.  Its Boolean interpretation is derived from
the environment stored in `world`.
-/
structure CertifiedRealWorld
    (measure : NatMeasure M)
    (EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress :
      Type uAddress)
    [DecidableEq EnvironmentAddress] [DecidableEq SystemAddress]
    [DecidableEq AdversarialAddress] [DecidableEq NetworkAddress]
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability}
      (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress)) where
  world : RealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema
  certificate :
    PPTExecutionCertificate
      (family := world.family) (policy := world.policy)
      measure world.kernelAlgebra world.networkAdapter world.initial

/--
An ideal closed world and the complete exact-to-measured PPT execution
certificate for that same world.  Its Boolean interpretation is derived from
the environment stored in `world`.
-/
structure CertifiedIdealWorld
    (measure : NatMeasure M)
    (EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress :
      Type uAddress)
    [DecidableEq EnvironmentAddress] [DecidableEq SystemAddress]
    [DecidableEq AdversarialAddress] [DecidableEq NetworkAddress]
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability}
      (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress)) where
  world : IdealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema
  certificate :
    PPTExecutionCertificate
      (family := world.family) (policy := world.policy)
      measure world.kernelAlgebra world.networkAdapter world.initial

namespace CertifiedRealWorld

variable {measure : NatMeasure M}

/-- Execute a certified real world at its own certified activation limit. -/
noncomputable def execution
    (certified : CertifiedRealWorld.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema) : Game Bool :=
  certified.world.execution certified.certificate.activationLimit

/-- Any larger certified fuel yields the same real Boolean game. -/
theorem execution_eq_of_activationLimit_le
    (certified : CertifiedRealWorld.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema)
    (fuel : CryptoLib.Core.SecPar → Nat)
    (fuel_le : ∀ sec, certified.certificate.activationLimit sec ≤ fuel sec) :
    certified.world.execution fuel = certified.execution := by
  funext sec
  let extra := fuel sec - certified.certificate.activationLimit sec
  have fuel_eq : certified.certificate.activationLimit sec + extra = fuel sec :=
    Nat.add_sub_of_le (fuel_le sec)
  have stable :
      RandCosted.valueDist (certified.world.runCosted sec (fuel sec)) =
        RandCosted.valueDist
          (certified.world.runCosted sec
            (certified.certificate.activationLimit sec)) := by
    simpa only [RealWorld.runCosted, fuel_eq] using
      certified.certificate.fuel.stable sec extra
  simp only [CertifiedRealWorld.execution, RealWorld.execution]
  rw [stable]

end CertifiedRealWorld

namespace CertifiedIdealWorld

variable {measure : NatMeasure M}

/-- Execute a certified ideal world at its own certified activation limit. -/
noncomputable def execution
    (certified : CertifiedIdealWorld.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema) : Game Bool :=
  certified.world.execution certified.certificate.activationLimit

/-- Any larger certified fuel yields the same ideal Boolean game. -/
theorem execution_eq_of_activationLimit_le
    (certified : CertifiedIdealWorld.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema)
    (fuel : CryptoLib.Core.SecPar → Nat)
    (fuel_le : ∀ sec, certified.certificate.activationLimit sec ≤ fuel sec) :
    certified.world.execution fuel = certified.execution := by
  funext sec
  let extra := fuel sec - certified.certificate.activationLimit sec
  have fuel_eq : certified.certificate.activationLimit sec + extra = fuel sec :=
    Nat.add_sub_of_le (fuel_le sec)
  have stable :
      RandCosted.valueDist (certified.world.runCosted sec (fuel sec)) =
        RandCosted.valueDist
          (certified.world.runCosted sec
            (certified.certificate.activationLimit sec)) := by
    simpa only [IdealWorld.runCosted, fuel_eq] using
      certified.certificate.fuel.stable sec extra
  simp only [CertifiedIdealWorld.execution, IdealWorld.execution]
  rw [stable]

end CertifiedIdealWorld

/--
A real and ideal certified world whose executions are compared at one common
fuel.  The exact result types may differ; only their Boolean observations are
compared.
-/
structure CertifiedWorldPair
    (measure : NatMeasure M)
    (EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress :
      Type uAddress)
    [DecidableEq EnvironmentAddress] [DecidableEq SystemAddress]
    [DecidableEq AdversarialAddress] [DecidableEq NetworkAddress]
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability}
      (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress)) where
  real : CertifiedRealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    measure EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema
  ideal : CertifiedIdealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    measure EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema
  environment_eq : real.world.environment = ideal.world.environment
  /-- Both executions use one common corruption policy. -/
  policy_eq : real.world.policy = ideal.world.policy

namespace CertifiedWorldPair

variable {measure : NatMeasure M}

/-- The least pointwise fuel that covers both certified activation limits. -/
def commonFuel
    (pair : CertifiedWorldPair.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema)
    (sec : CryptoLib.Core.SecPar) : Nat :=
  max (pair.real.certificate.activationLimit sec)
    (pair.ideal.certificate.activationLimit sec)

/-- The common real/ideal fuel remains polynomially bounded. -/
theorem commonFuel_isPoly
    (pair : CertifiedWorldPair.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema) :
    IsPolyBounded pair.commonFuel :=
  IsPolyBounded.max
    pair.real.certificate.activationLimit_isPoly
    pair.ideal.certificate.activationLimit_isPoly

/-- Extend the real world's semantic fuel certificate to the common fuel. -/
noncomputable def realFuelCertificate
    (pair : CertifiedWorldPair.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema) :
    FuelCertificate
      (family := pair.real.world.family) (policy := pair.real.world.policy)
      pair.real.world.kernelAlgebra pair.real.world.networkAdapter
        pair.real.world.initial pair.commonFuel :=
  pair.real.certificate.fuel.extend
    (fun _sec => Nat.le_max_left _ _)

/-- Extend the ideal world's semantic fuel certificate to the common fuel. -/
noncomputable def idealFuelCertificate
    (pair : CertifiedWorldPair.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema) :
    FuelCertificate
      (family := pair.ideal.world.family) (policy := pair.ideal.world.policy)
      pair.ideal.world.kernelAlgebra pair.ideal.world.networkAdapter
        pair.ideal.world.initial pair.commonFuel :=
  pair.ideal.certificate.fuel.extend
    (fun _sec => Nat.le_max_right _ _)

/-- Execute the real world at the shared fuel, then erase exact costs. -/
noncomputable def realExecution
    (pair : CertifiedWorldPair.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema) : Game Bool :=
  pair.real.world.execution pair.commonFuel

/-- Execute the ideal world at the shared fuel, then erase exact costs. -/
noncomputable def idealExecution
    (pair : CertifiedWorldPair.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema) : Game Bool :=
  pair.ideal.world.execution pair.commonFuel

/-- No exact real-world path at the common fuel can end in a timeout. -/
theorem real_noTimeout
    (pair : CertifiedWorldPair.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema)
    (sec : CryptoLib.Core.SecPar)
    (result : Costed M
      (Kernel.ExecutionResult pair.real.world.family
        pair.real.world.policy sec))
    (hresult : result ∈
      (pair.real.world.runCosted sec (pair.commonFuel sec)).support) :
    result.val.outcome ≠ Kernel.ExecutionOutcome.timeout := by
  apply pair.realFuelCertificate.noTimeout sec result
  simpa only [RealWorld.runCosted] using hresult

/-- No exact ideal-world path at the common fuel can end in a timeout. -/
theorem ideal_noTimeout
    (pair : CertifiedWorldPair.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema)
    (sec : CryptoLib.Core.SecPar)
    (result : Costed M
      (Kernel.ExecutionResult pair.ideal.world.family
        pair.ideal.world.policy sec))
    (hresult : result ∈
      (pair.ideal.world.runCosted sec (pair.commonFuel sec)).support) :
    result.val.outcome ≠ Kernel.ExecutionOutcome.timeout := by
  apply pair.idealFuelCertificate.noTimeout sec result
  simpa only [IdealWorld.runCosted] using hresult

/-- Increasing the common fuel cannot change the erased real distribution. -/
theorem real_stable
    (pair : CertifiedWorldPair.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema)
    (sec : CryptoLib.Core.SecPar) (extra : Nat) :
    RandCosted.valueDist
        (pair.real.world.runCosted sec (pair.commonFuel sec + extra)) =
      RandCosted.valueDist
        (pair.real.world.runCosted sec (pair.commonFuel sec)) := by
  simpa only [RealWorld.runCosted] using
    pair.realFuelCertificate.stable sec extra

/-- Increasing the common fuel cannot change the erased ideal distribution. -/
theorem ideal_stable
    (pair : CertifiedWorldPair.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema)
    (sec : CryptoLib.Core.SecPar) (extra : Nat) :
    RandCosted.valueDist
        (pair.ideal.world.runCosted sec (pair.commonFuel sec + extra)) =
      RandCosted.valueDist
        (pair.ideal.world.runCosted sec (pair.commonFuel sec)) := by
  simpa only [IdealWorld.runCosted] using
    pair.idealFuelCertificate.stable sec extra

end CertifiedWorldPair

end CryptoLib.Core.Infrastructure.UC
