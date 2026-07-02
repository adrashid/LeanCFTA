import FaultTree.CoherentCutSets

namespace CFTree

abbrev EventId := String

/-
===========================================================
Case Study: Autonomous Emergency Braking
===========================================================
-/

/-
===========================================================
1. Events
===========================================================
-/

def CameraFailure : CFTree EventId :=
  BE "CameraFailure"

def RadarFailure : CFTree EventId :=
  BE "RadarFailure"

def SensorFusionFailure : CFTree EventId :=
  BE "SensorFusionFailure"

def ControllerFailure : CFTree EventId :=
  BE "ControllerFailure"

def SafetyMonitorFailure : CFTree EventId :=
  BE "SafetyMonitorFailure"

def BrakeActuatorFailure : CFTree EventId :=
  BE "BrakeActuatorFailure"

def HydraulicFailure : CFTree EventId :=
  BE "HydraulicFailure"

def PowerFailure : CFTree EventId :=
  BE "PowerFailure"

/-
===========================================================
2. Subsystems
===========================================================
-/

def PerceptionFailure : CFTree EventId :=
  OR [
    CameraFailure,
    RadarFailure,
    SensorFusionFailure
  ]

def DecisionFailure : CFTree EventId :=
  AND [
    ControllerFailure,
    SafetyMonitorFailure
  ]

def ActuationFailure : CFTree EventId :=
  OR [
    BrakeActuatorFailure,
    HydraulicFailure,
    PowerFailure
  ]

/-
===========================================================
3. Complete Tree
===========================================================
-/

def EmergencyBrakingFailure : CFTree EventId :=
  OR [
    PerceptionFailure,
    DecisionFailure,
    ActuationFailure
  ]

/-- The emergency braking fault tree is well formed. -/
theorem EmergencyBrakingFailure_wellFormed :
    WellFormed EmergencyBrakingFailure := by
  simp [
    EmergencyBrakingFailure,
    PerceptionFailure,
    DecisionFailure,
    ActuationFailure,
    CameraFailure,
    RadarFailure,
    SensorFusionFailure,
    ControllerFailure,
    SafetyMonitorFailure,
    BrakeActuatorFailure,
    HydraulicFailure,
    PowerFailure,
    WellFormed,
    OR,
    AND,
    BE
  ]

/-- The complete emergency braking fault tree is monotone. -/
theorem EmergencyBrakingFailure_monotone :
    Monotone EmergencyBrakingFailure := by
  exact coherent_monotone EmergencyBrakingFailure

/-
===========================================================
4. Generated Cut Sets
===========================================================
-/

/-- The singleton camera failure is generated as a cut set. -/
theorem camera_generated :
    ({"CameraFailure"} : CutSet EventId) ∈
      cutSets EmergencyBrakingFailure := by
  native_decide

/-- The controller-monitor pair is generated as a cut set. -/
theorem controller_monitor_generated :
    ({"ControllerFailure", "SafetyMonitorFailure"} : CutSet EventId) ∈
      cutSets EmergencyBrakingFailure := by
  native_decide

/-- The camera-radar pair is not generated as a minimal structural cut set. -/
theorem camera_radar_not_generated :
    ({"CameraFailure", "RadarFailure"} : CutSet EventId) ∉
      cutSets EmergencyBrakingFailure := by
  native_decide

/-
===========================================================
5. Representative Theorems
===========================================================
-/

/-- Every generated cut set for the emergency braking system is semantically valid. -/
theorem EmergencyBrakingFailure_cutSets_sound
    (C : CutSet EventId)
    (h : C ∈ cutSets EmergencyBrakingFailure) :
    IsCutSet C EmergencyBrakingFailure := by
  exact cutSets_sound EmergencyBrakingFailure C h

/-- Global soundness of all generated cut sets for the emergency braking system. -/
theorem EmergencyBraking_sound :
    ∀ C ∈ cutSets EmergencyBrakingFailure,
      IsCutSet C EmergencyBrakingFailure := by
  intro C h
  exact EmergencyBrakingFailure_cutSets_sound C h

/-- Every generated minimal cut set for the emergency braking system is valid. -/
theorem EmergencyBraking_minimal_sound :
    ∀ C ∈ minimalCutSets EmergencyBrakingFailure,
      IsCutSet C EmergencyBrakingFailure := by
  intro C h
  exact minimalCutSets_semantic_sound EmergencyBrakingFailure C h

/-- Failure of the controller alone is not sufficient to cause the top event. -/
theorem controller_alone_not_cutset :
    ¬ IsCutSet
      ({"ControllerFailure"} : CutSet EventId)
      EmergencyBrakingFailure := by
  unfold IsCutSet
  simp [
    EmergencyBrakingFailure,
    PerceptionFailure,
    DecisionFailure,
    ActuationFailure,
    CameraFailure,
    RadarFailure,
    SensorFusionFailure,
    ControllerFailure,
    SafetyMonitorFailure,
    BrakeActuatorFailure,
    HydraulicFailure,
    PowerFailure,
    eval_basic,
    evalAny,
    evalAll,
    OR,
    AND,
    BE
  ]

/-- The generated camera failure cut set is semantically valid. -/
theorem camera_semantic_cutset :
    IsCutSet
      ({"CameraFailure"} : CutSet EventId)
      EmergencyBrakingFailure := by
  exact EmergencyBrakingFailure_cutSets_sound
    ({"CameraFailure"} : CutSet EventId)
    camera_generated

/-- The generated controller-monitor cut set is semantically valid. -/
theorem controller_monitor_semantic_cutset :
    IsCutSet
      ({"ControllerFailure", "SafetyMonitorFailure"} : CutSet EventId)
      EmergencyBrakingFailure := by
  exact EmergencyBrakingFailure_cutSets_sound
    ({"ControllerFailure", "SafetyMonitorFailure"} : CutSet EventId)
    controller_monitor_generated

/-- The camera failure singleton is generated as a minimal cut set. -/
theorem camera_minimal_generated :
    ({"CameraFailure"} : CutSet EventId) ∈
      minimalCutSets EmergencyBrakingFailure := by
  native_decide

/-- The controller-monitor pair is generated as a minimal cut set. -/
theorem controller_monitor_minimal_generated :
    ({"ControllerFailure", "SafetyMonitorFailure"} : CutSet EventId) ∈
      minimalCutSets EmergencyBrakingFailure := by
  native_decide

/-
===========================================================
6. Computation Examples
===========================================================
-/

#eval cutSets PerceptionFailure
#eval cutSets DecisionFailure
#eval cutSets ActuationFailure
#eval cutSets EmergencyBrakingFailure
#eval minimalCutSets EmergencyBrakingFailure

end CFTree
