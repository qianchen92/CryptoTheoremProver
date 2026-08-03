import Crypto.Infrastructure.Complexity.Machine
import Crypto.Infrastructure.GameBased.Indistinguishability
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace Crypto.Infrastructure.UC

open Crypto.Infrastructure.Complexity
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Oracle
open Crypto.Infrastructure.GameBased

universe uInput uOutput uState
universe uEnvInput uEnvOracle uEnvQuery uEnvResponse uEnvState
universe uAdvInput uAdvOutput uAdvOracle uAdvQuery uAdvResponse
universe uSimInput uSimOutput uSimOracle uSimQuery uSimResponse

/--
A semantic interactive system, indexed by the security parameter.

This is intentionally lower-level than a UC protocol.  It is the common shape
used for ideal functionalities, real protocols, trusted setup components, and
hybrid functionalities whose full message syntax will be fixed by later MPC
modules.
-/
structure InteractiveSystem
    (Input : Crypto.SecPar → Type uInput)
    (Output : Crypto.SecPar → Type uOutput) where
  State : Crypto.SecPar → Type uState
  init : (sec : Crypto.SecPar) → PMF (State sec)
  step : (sec : Crypto.SecPar) → State sec → Input sec → PMF (Output sec × State sec)

/-- The external UC environment, modeled semantically as an oracle machine. -/
abbrev Environment
    (EnvInput : Crypto.SecPar → Type uEnvInput)
    (EnvSpec :
      (sec : Crypto.SecPar) →
      EnvInput sec →
      OracleSpec.{uEnvOracle, uEnvQuery, uEnvResponse}) :=
  ProbabilisticOracleMachine Cost.CostModel.nat EnvInput (fun _ => Bool) EnvSpec

/-- A PPT external UC environment. -/
abbrev PPTEnvironment
    (EnvInput : Crypto.SecPar → Type uEnvInput)
    (EnvSpec :
      (sec : Crypto.SecPar) →
      EnvInput sec →
      OracleSpec.{uEnvOracle, uEnvQuery, uEnvResponse}) :=
  PPTOracleMachine Cost.CostModel.nat Cost.NatMeasure.nat
    EnvInput (fun _ => Bool) EnvSpec

/-- The real-world adversary, modeled semantically as an oracle machine. -/
abbrev Adversary
    (AdversaryInput : Crypto.SecPar → Type uAdvInput)
    (AdversaryOutput : Crypto.SecPar → Type uAdvOutput)
    (AdversarySpec :
      (sec : Crypto.SecPar) →
      AdversaryInput sec →
      OracleSpec.{uAdvOracle, uAdvQuery, uAdvResponse}) :=
  ProbabilisticOracleMachine Cost.CostModel.nat
    AdversaryInput AdversaryOutput AdversarySpec

/-- A PPT real-world adversary. -/
abbrev PPTAdversary
    (AdversaryInput : Crypto.SecPar → Type uAdvInput)
    (AdversaryOutput : Crypto.SecPar → Type uAdvOutput)
    (AdversarySpec :
      (sec : Crypto.SecPar) →
      AdversaryInput sec →
      OracleSpec.{uAdvOracle, uAdvQuery, uAdvResponse}) :=
  PPTOracleMachine Cost.CostModel.nat Cost.NatMeasure.nat
    AdversaryInput AdversaryOutput AdversarySpec

/-- The ideal-world simulator, modeled semantically as an oracle machine. -/
abbrev Simulator
    (SimulatorInput : Crypto.SecPar → Type uSimInput)
    (SimulatorOutput : Crypto.SecPar → Type uSimOutput)
    (SimulatorSpec :
      (sec : Crypto.SecPar) →
      SimulatorInput sec →
      OracleSpec.{uSimOracle, uSimQuery, uSimResponse}) :=
  ProbabilisticOracleMachine Cost.CostModel.nat
    SimulatorInput SimulatorOutput SimulatorSpec

/-- A PPT ideal-world simulator. -/
abbrev PPTSimulator
    (SimulatorInput : Crypto.SecPar → Type uSimInput)
    (SimulatorOutput : Crypto.SecPar → Type uSimOutput)
    (SimulatorSpec :
      (sec : Crypto.SecPar) →
      SimulatorInput sec →
      OracleSpec.{uSimOracle, uSimQuery, uSimResponse}) :=
  PPTOracleMachine Cost.CostModel.nat Cost.NatMeasure.nat
    SimulatorInput SimulatorOutput SimulatorSpec

/--
A UC experiment exposes the same oracle interface to the environment in both
worlds.  The real world is parameterized by an adversary and the ideal world by
a simulator; both internal schedulers are abstracted as oracle environments for
the external environment.
-/
structure Experiment
    (EnvInput : Crypto.SecPar → Type uEnvInput)
    (EnvSpec :
      (sec : Crypto.SecPar) →
      EnvInput sec →
      OracleSpec.{uEnvOracle, uEnvQuery, uEnvResponse})
    (AdversaryInput : Crypto.SecPar → Type uAdvInput)
    (AdversaryOutput : Crypto.SecPar → Type uAdvOutput)
    (AdversarySpec :
      (sec : Crypto.SecPar) →
      AdversaryInput sec →
      OracleSpec.{uAdvOracle, uAdvQuery, uAdvResponse})
    (SimulatorInput : Crypto.SecPar → Type uSimInput)
    (SimulatorOutput : Crypto.SecPar → Type uSimOutput)
    (SimulatorSpec :
      (sec : Crypto.SecPar) →
      SimulatorInput sec →
      OracleSpec.{uSimOracle, uSimQuery, uSimResponse}) where
  setup : (sec : Crypto.SecPar) → PMF (EnvInput sec)
  realWorld :
    Adversary AdversaryInput AdversaryOutput AdversarySpec →
    (sec : Crypto.SecPar) →
    (input : EnvInput sec) →
    OracleEnv.{uEnvOracle, uEnvQuery, uEnvResponse, uEnvState} (EnvSpec sec input)
  idealWorld :
    Simulator SimulatorInput SimulatorOutput SimulatorSpec →
    (sec : Crypto.SecPar) →
    (input : EnvInput sec) →
    OracleEnv.{uEnvOracle, uEnvQuery, uEnvResponse, uEnvState} (EnvSpec sec input)

namespace Experiment

variable
    {EnvInput : Crypto.SecPar → Type uEnvInput}
    {EnvSpec :
      (sec : Crypto.SecPar) →
      EnvInput sec →
      OracleSpec.{uEnvOracle, uEnvQuery, uEnvResponse}}
    {AdversaryInput : Crypto.SecPar → Type uAdvInput}
    {AdversaryOutput : Crypto.SecPar → Type uAdvOutput}
    {AdversarySpec :
      (sec : Crypto.SecPar) →
      AdversaryInput sec →
      OracleSpec.{uAdvOracle, uAdvQuery, uAdvResponse}}
    {SimulatorInput : Crypto.SecPar → Type uSimInput}
    {SimulatorOutput : Crypto.SecPar → Type uSimOutput}
    {SimulatorSpec :
      (sec : Crypto.SecPar) →
      SimulatorInput sec →
      OracleSpec.{uSimOracle, uSimQuery, uSimResponse}}

/-- Run the external environment against the real-world scheduler. -/
noncomputable def realExecution
    (experiment :
      Experiment EnvInput EnvSpec
        AdversaryInput AdversaryOutput AdversarySpec
        SimulatorInput SimulatorOutput SimulatorSpec)
    (adversary : Adversary AdversaryInput AdversaryOutput AdversarySpec)
    (environment : Environment EnvInput EnvSpec) :
    Game Bool :=
  fun sec =>
    PMF.bind (experiment.setup sec) fun input =>
      environment.runWithEnv sec input (experiment.realWorld adversary sec input)

/-- Run the external environment against the ideal-world scheduler. -/
noncomputable def idealExecution
    (experiment :
      Experiment EnvInput EnvSpec
        AdversaryInput AdversaryOutput AdversarySpec
        SimulatorInput SimulatorOutput SimulatorSpec)
    (simulator : Simulator SimulatorInput SimulatorOutput SimulatorSpec)
    (environment : Environment EnvInput EnvSpec) :
    Game Bool :=
  fun sec =>
    PMF.bind (experiment.setup sec) fun input =>
      environment.runWithEnv sec input (experiment.idealWorld simulator sec input)

/--
Computational UC emulation: for every PPT real-world adversary there is a PPT
ideal-world simulator such that every PPT environment sees negligible
distinguishing advantage.
-/
def UCEmulates
    (experiment :
      Experiment EnvInput EnvSpec
        AdversaryInput AdversaryOutput AdversarySpec
        SimulatorInput SimulatorOutput SimulatorSpec) : Prop :=
  ∀ adversary : PPTAdversary AdversaryInput AdversaryOutput AdversarySpec,
    ∃ simulator : PPTSimulator SimulatorInput SimulatorOutput SimulatorSpec,
      ∀ environment : PPTEnvironment EnvInput EnvSpec,
        Indistinguishable
          (realExecution experiment adversary.toProbabilisticOracleMachine
            environment.toProbabilisticOracleMachine)
          (idealExecution experiment simulator.toProbabilisticOracleMachine
            environment.toProbabilisticOracleMachine)

/--
UC emulation against a restricted class of environments.  This matches the
"controlled environment" phrasing used by layered/YOSO MPC papers.
-/
def ControlledUCEmulates
    (experiment :
      Experiment EnvInput EnvSpec
        AdversaryInput AdversaryOutput AdversarySpec
        SimulatorInput SimulatorOutput SimulatorSpec)
    (AllowedEnvironment : Environment EnvInput EnvSpec → Prop) : Prop :=
  ∀ adversary : PPTAdversary AdversaryInput AdversaryOutput AdversarySpec,
    ∃ simulator : PPTSimulator SimulatorInput SimulatorOutput SimulatorSpec,
      ∀ environment : PPTEnvironment EnvInput EnvSpec,
        AllowedEnvironment environment.toProbabilisticOracleMachine →
          Indistinguishable
            (realExecution experiment adversary.toProbabilisticOracleMachine
              environment.toProbabilisticOracleMachine)
            (idealExecution experiment simulator.toProbabilisticOracleMachine
              environment.toProbabilisticOracleMachine)

/--
Perfect UC emulation with an efficient simulator: for every PPT real-world
adversary there is a PPT ideal-world simulator such that every semantic
environment sees exactly the same boolean game at every security parameter.
-/
def PerfectUCEmulates
    (experiment :
      Experiment EnvInput EnvSpec
        AdversaryInput AdversaryOutput AdversarySpec
        SimulatorInput SimulatorOutput SimulatorSpec) : Prop :=
  ∀ adversary : PPTAdversary AdversaryInput AdversaryOutput AdversarySpec,
    ∃ simulator : PPTSimulator SimulatorInput SimulatorOutput SimulatorSpec,
      ∀ environment : Environment EnvInput EnvSpec,
        ∀ sec : Crypto.SecPar,
          realExecution experiment adversary.toProbabilisticOracleMachine environment sec =
            idealExecution experiment simulator.toProbabilisticOracleMachine environment sec

/-- Perfect UC emulation against a restricted class of environments. -/
def PerfectControlledUCEmulates
    (experiment :
      Experiment EnvInput EnvSpec
        AdversaryInput AdversaryOutput AdversarySpec
        SimulatorInput SimulatorOutput SimulatorSpec)
    (AllowedEnvironment : Environment EnvInput EnvSpec → Prop) : Prop :=
  ∀ adversary : PPTAdversary AdversaryInput AdversaryOutput AdversarySpec,
    ∃ simulator : PPTSimulator SimulatorInput SimulatorOutput SimulatorSpec,
      ∀ environment : Environment EnvInput EnvSpec,
        AllowedEnvironment environment →
          ∀ sec : Crypto.SecPar,
            realExecution experiment adversary.toProbabilisticOracleMachine environment sec =
              idealExecution experiment simulator.toProbabilisticOracleMachine environment sec

theorem PerfectUCEmulates.ucEmulates
    {experiment :
      Experiment EnvInput EnvSpec
        AdversaryInput AdversaryOutput AdversarySpec
        SimulatorInput SimulatorOutput SimulatorSpec}
    (h : PerfectUCEmulates experiment) :
    UCEmulates experiment := by
  intro adversary
  obtain ⟨simulator, hsimulator⟩ := h adversary
  refine ⟨simulator, ?_⟩
  intro environment
  have hAdvantage :
      Advantage
          (realExecution experiment adversary.toProbabilisticOracleMachine
            environment.toProbabilisticOracleMachine)
          (idealExecution experiment simulator.toProbabilisticOracleMachine
            environment.toProbabilisticOracleMachine) =
        fun _ => (0 : Real) := by
    funext sec
    simp [Advantage, AcceptProb, hsimulator environment.toProbabilisticOracleMachine sec]
  unfold Indistinguishable
  rw [hAdvantage]
  exact Crypto.Infrastructure.Asymptotic.isNegligible_zero

theorem PerfectControlledUCEmulates.controlledUCEmulates
    {experiment :
      Experiment EnvInput EnvSpec
        AdversaryInput AdversaryOutput AdversarySpec
        SimulatorInput SimulatorOutput SimulatorSpec}
    {AllowedEnvironment : Environment EnvInput EnvSpec → Prop}
    (h : PerfectControlledUCEmulates experiment AllowedEnvironment) :
    ControlledUCEmulates experiment AllowedEnvironment := by
  intro adversary
  obtain ⟨simulator, hsimulator⟩ := h adversary
  refine ⟨simulator, ?_⟩
  intro environment hallowed
  have hAdvantage :
      Advantage
          (realExecution experiment adversary.toProbabilisticOracleMachine
            environment.toProbabilisticOracleMachine)
          (idealExecution experiment simulator.toProbabilisticOracleMachine
            environment.toProbabilisticOracleMachine) =
        fun _ => (0 : Real) := by
    funext sec
    simp [Advantage, AcceptProb,
      hsimulator environment.toProbabilisticOracleMachine hallowed sec]
  unfold Indistinguishable
  rw [hAdvantage]
  exact Crypto.Infrastructure.Asymptotic.isNegligible_zero

end Experiment

end Crypto.Infrastructure.UC
