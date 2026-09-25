import Project.Drone.Reconstruction
import Project.Drone.Kinematics

/-! Check all current drone source-proof components in one target.
This is not a full `compute` specification or an exact-WASM behavior theorem.
See task.md for the remaining composition obligations. -/

#print axioms Project.Drone.Edges.state_edge_clearance
#print axioms Project.Drone.Arithmetic.restSeconds_bounds
#print axioms Project.Drone.Sqrt.ceilSqrt_correct
#print axioms Project.Drone.Selection.scan_minimum
#print axioms Project.Drone.Selection.finite_scan_predecessor
#print axioms Project.Drone.Selection.advance_size
#print axioms Project.Drone.Optimality.attaining_route_optimal

#print axioms Project.Drone.Dynamics.accepted_forward_bounds
#print axioms Project.Drone.Dynamics.rest_bounds
#print axioms Project.Drone.Timing.state_ticks_exact
#print axioms Project.Drone.Timing.rest_admitted
#print axioms Project.Drone.Kinematics.vertical_derivative
#print axioms Project.Drone.Kinematics.vertical_second_derivative
#print axioms Project.Drone.Kinematics.forward_derivative
#print axioms Project.Drone.Kinematics.forward_second_derivative
#print axioms Project.Drone.Rows.advance_word
#print axioms Project.Drone.Costs.predecessor_exact
#print axioms Project.Drone.Costs.best_parent
#print axioms Project.Drone.Costs.advance_bound
#print axioms Project.Drone.Initial.initial_fields
#print axioms Project.Drone.Planner.advance_correct
#print axioms Project.Drone.Planner.layers_optimal

#print axioms Project.Drone.Feasibility.all_stop_flight
#print axioms Project.Drone.Feasibility.terrain_terminal_optimal

#print axioms Project.Drone.Reconstruction.backtrack_correct
#print axioms Project.Drone.Reconstruction.reconstructed_optimal
