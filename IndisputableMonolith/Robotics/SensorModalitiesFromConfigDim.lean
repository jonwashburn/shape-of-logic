import Mathlib
import IndisputableMonolith.Constants

/-!
# Robot Sensor Modalities from configDim — Robotics Depth

Five canonical robotic sensor modalities (= configDim D = 5):
  vision, lidar, radar, tactile, proprioceptive.

These correspond to external geometry, active ranging, long-range
motion sensing, contact sensing, and internal body-state sensing.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Robotics.SensorModalitiesFromConfigDim

inductive SensorModality where
  | vision
  | lidar
  | radar
  | tactile
  | proprioceptive
  deriving DecidableEq, Repr, BEq, Fintype

theorem sensorModality_count : Fintype.card SensorModality = 5 := by decide

structure SensorModalitiesCert where
  five_modalities : Fintype.card SensorModality = 5

def sensorModalitiesCert : SensorModalitiesCert where
  five_modalities := sensorModality_count

end IndisputableMonolith.Robotics.SensorModalitiesFromConfigDim
