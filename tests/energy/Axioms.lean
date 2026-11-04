import Demos.Energy.Theorems
import Demos.Energy.Examples
import Demos.Energy.GatewayRun
import Demos.Energy.Loop

/-! The axioms of the energy authorizer's and the gateway's theorems, which must be `propext`,
`Classical.choice`, and `Quot.sound`. -/

#print axioms Demos.Energy.Theorems.energy_authorize
#print axioms Demos.Energy.Theorems.authorize_sound
#print axioms Demos.Energy.Theorems.authorize_accepted
#print axioms Demos.Energy.Theorems.authorize_admits
#print axioms Demos.Energy.Theorems.authorize_operation
#print axioms Demos.Energy.Authorize.authorizeWith_iff
#print axioms Demos.Energy.Spec.operation_sound
#print axioms Demos.Energy.Spec.operates_exists
#print axioms Demos.Energy.Spec.Trajectory.fallback_keeps_floor
#print axioms Demos.Energy.Spec.Trajectory.fallback_keeps_ceiling
#print axioms Demos.Energy.Spec.Trajectory.fallback_keeps_export
#print axioms Demos.Energy.Spec.Trajectory.fallback_keeps_import
#print axioms Demos.Energy.Spec.Trajectory.within_of_fallback
#print axioms Demos.Energy.Examples.example_accept
#print axioms Demos.Energy.Examples.example_export
#print axioms Demos.Energy.Examples.example_floor
#print axioms Demos.Energy.Examples.example_relative
#print axioms Demos.Energy.Examples.example_renewal
#print axioms Demos.Energy.Examples.example_limits
#print axioms Demos.Energy.Examples.example_limits_import
#print axioms Demos.Energy.authorizeFlat_eq
#print axioms Demos.Energy.gateway_command
#print axioms Demos.Energy.gateway_fault
#print axioms Demos.Energy.gateway_leaves
#print axioms Demos.Energy.gateway_record
#print axioms Demos.Energy.gateway_states
#print axioms Demos.Energy.gwTick_abs
#print axioms Demos.Energy.gw_program
#print axioms Demos.Energy.gw_prefix
