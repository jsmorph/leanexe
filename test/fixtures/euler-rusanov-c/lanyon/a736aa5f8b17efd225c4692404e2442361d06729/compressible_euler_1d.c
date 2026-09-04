#include <math.h>
#include <stdlib.h>
#include <stdbool.h>

typedef struct {
  double x;
} compressible_euler_1d_coordinates;

typedef struct {
  double rho;
  double mom;
  double energy;
} compressible_euler_1d_state;

static inline bool
compressible_euler_1d_state_valid(const compressible_euler_1d_state *U)
{
  double rho = U->rho;
  double mom = U->mom;
  double energy = U->energy;
  
  return (rho > 0.0 && energy > 0.0);
}

typedef struct {
  double gas_gamma;
} compressible_euler_1d_parameters;

static inline bool
compressible_euler_1d_parameters_valid(const compressible_euler_1d_parameters *P)
{
  double gas_gamma = P->gas_gamma;

  return (gas_gamma > 1.0);
}

typedef struct {
  double flux_rho;
  double flux_mom;
  double flux_energy;
} compressible_euler_1d_flux;

typedef struct {
  void (*x_flux)(const compressible_euler_1d_coordinates *C, const compressible_euler_1d_parameters *P,
    const compressible_euler_1d_state *U, compressible_euler_1d_flux *flux);
} compressible_euler_1d_fluxes_1D;

static inline void
compressible_euler_1d_x_flux(const compressible_euler_1d_coordinates *C, const compressible_euler_1d_parameters *P,
  const compressible_euler_1d_state *U, compressible_euler_1d_flux *flux)
{
  double x = C->x;
  double gas_gamma = P->gas_gamma;
  double rho = U->rho;
  double mom = U->mom;
  double energy = U->energy;

  flux->flux_rho = mom;
  flux->flux_mom = (((mom * mom) / rho) + ((gas_gamma - 1.0) * (energy - (0.5 * ((mom * mom) / rho)))));
  flux->flux_energy = ((energy + ((gas_gamma - 1.0) * (energy - (0.5 * ((mom * mom) / rho))))) * (mom / rho));
}

static inline compressible_euler_1d_fluxes_1D
create_fluxes()
{
  compressible_euler_1d_fluxes_1D fluxes;

  fluxes.x_flux = compressible_euler_1d_x_flux;
  
  return fluxes;
}

typedef struct {
  double mu1;
  double mu2;
  double mu3;
} compressible_euler_1d_wavespeed;

typedef struct {
  void (*x_wavespeed)(const compressible_euler_1d_coordinates *C, const compressible_euler_1d_parameters *P,
    const compressible_euler_1d_state *U, compressible_euler_1d_wavespeed *wavespeed);
} compressible_euler_1d_wavespeed_estimate_1D;

static inline void
compressible_euler_1d_x_wavespeed(const compressible_euler_1d_coordinates *C, const compressible_euler_1d_parameters *P,
  const compressible_euler_1d_state *U, compressible_euler_1d_wavespeed *wavespeed)
{
  double x = C->x;
  double gas_gamma = P->gas_gamma;
  double rho = U->rho;
  double mom = U->mom;
  double energy = U->energy;

  wavespeed->mu1 = ((mom / rho) - sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy - (0.5 * ((mom * mom) / rho))))) /
    rho)));
  wavespeed->mu2 = (mom / rho);
  wavespeed->mu3 = ((mom / rho) + sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy - (0.5 * ((mom * mom) / rho))))) /
    rho)));
}

static inline compressible_euler_1d_wavespeed_estimate_1D
create_wavespeeds()
{
  compressible_euler_1d_wavespeed_estimate_1D wavespeed_estimate;

  wavespeed_estimate.x_wavespeed = compressible_euler_1d_x_wavespeed;
  
  return wavespeed_estimate;
}

typedef struct {
  double rho_x;
  double mom_x;
  double energy_x;
} compressible_euler_1d_gradient;

typedef struct {
  double diffusive_flux_rho;
  double diffusive_flux_mom;
  double diffusive_flux_energy;
} compressible_euler_1d_diffusive_flux;

typedef struct {
  void (*x_diffusive_flux)(const compressible_euler_1d_coordinates *C, const compressible_euler_1d_parameters *P,
    const compressible_euler_1d_state *U, compressible_euler_1d_gradient *DU, compressible_euler_1d_diffusive_flux *flux);
} compressible_euler_1d_diffusive_fluxes_1D;

static inline void
compressible_euler_1d_x_diffusive_flux(const compressible_euler_1d_coordinates *C, const compressible_euler_1d_parameters *P,
  const compressible_euler_1d_state *U, compressible_euler_1d_gradient *DU, compressible_euler_1d_diffusive_flux *diffusive_flux)
{
  double x = C->x;
  double gas_gamma = P->gas_gamma;
  double rho = U->rho;
  double mom = U->mom;
  double energy = U->energy;
  double rho_x = DU->rho_x;
  double mom_x = DU->mom_x;
  double energy_x = DU->energy_x;

  diffusive_flux->diffusive_flux_rho = 0.0;
  diffusive_flux->diffusive_flux_mom = 0.0;
  diffusive_flux->diffusive_flux_energy = 0.0;
}

static inline compressible_euler_1d_diffusive_fluxes_1D
create_diffusive_fluxes()
{
  compressible_euler_1d_diffusive_fluxes_1D diffusive_fluxes;

  diffusive_fluxes.x_diffusive_flux = compressible_euler_1d_x_diffusive_flux;
  
  return diffusive_fluxes;
}

typedef struct {
  double wave_rho;
  double wave_mom;
  double wave_energy;
} compressible_euler_1d_lax_friedrichs_wave;

typedef struct {
  compressible_euler_1d_lax_friedrichs_wave wave1;
  compressible_euler_1d_lax_friedrichs_wave wave2;
} compressible_euler_1d_lax_friedrichs_wave_family;

typedef struct {
  void (*x_wave_family)(const compressible_euler_1d_coordinates *C_L, const compressible_euler_1d_coordinates *C_R,
    const compressible_euler_1d_state *U_L, const compressible_euler_1d_state *U_R,
    const compressible_euler_1d_parameters *P, compressible_euler_1d_lax_friedrichs_wave_family *wave_family);
} compressible_euler_1d_lax_friedrichs_waves_1D;

static inline void
compressible_euler_1d_lax_friedrichs_x_wave_family(const compressible_euler_1d_coordinates *C_L, const compressible_euler_1d_coordinates *C_R,
  const compressible_euler_1d_state *U_L, const compressible_euler_1d_state *U_R,
  const compressible_euler_1d_parameters *P, compressible_euler_1d_lax_friedrichs_wave_family *wave_family)
{
  double x_L = C_L->x;
  double x_R = C_R->x;
  double rho_L = U_L->rho;
  double rho_R = U_R->rho;
  double mom_L = U_L->mom;
  double mom_R = U_R->mom;
  double energy_L = U_L->energy;
  double energy_R = U_R->energy;
  double gas_gamma = P->gas_gamma;

  wave_family->wave1.wave_rho = (0.5 * ((rho_R - rho_L) - ((mom_R - mom_L) / fmax(fmax(fabs(((mom_L / rho_L) -
    sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_L - (0.5 * ((mom_L * mom_L) / rho_L))))) / rho_L)))), fabs(((mom_L /
    rho_L) + sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_L - (0.5 * ((mom_L * mom_L) / rho_L))))) / rho_L))))),
    fmax(fabs(((mom_R / rho_R) - sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_R - (0.5 * ((mom_R * mom_R) /
    rho_R))))) / rho_R)))), fabs(((mom_R / rho_R) + sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_R - (0.5 * ((mom_R *
    mom_R) / rho_R))))) / rho_R)))))))));
  wave_family->wave1.wave_mom = (0.5 * ((mom_R - mom_L) - (((((mom_R * mom_R) / rho_R) + ((gas_gamma - 1.0) * (energy_R
    - (0.5 * ((mom_R * mom_R) / rho_R))))) - (((mom_L * mom_L) / rho_L) + ((gas_gamma - 1.0) * (energy_L - (0.5 *
    ((mom_L * mom_L) / rho_L)))))) / fmax(fmax(fabs(((mom_L / rho_L) - sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_L
    - (0.5 * ((mom_L * mom_L) / rho_L))))) / rho_L)))), fabs(((mom_L / rho_L) + sqrt(((gas_gamma * ((gas_gamma - 1.0) *
    (energy_L - (0.5 * ((mom_L * mom_L) / rho_L))))) / rho_L))))), fmax(fabs(((mom_R / rho_R) - sqrt(((gas_gamma *
    ((gas_gamma - 1.0) * (energy_R - (0.5 * ((mom_R * mom_R) / rho_R))))) / rho_R)))), fabs(((mom_R / rho_R) +
    sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_R - (0.5 * ((mom_R * mom_R) / rho_R))))) / rho_R)))))))));
  wave_family->wave1.wave_energy = (0.5 * ((energy_R - energy_L) - ((((energy_R + ((gas_gamma - 1.0) * (energy_R - (0.5
    * ((mom_R * mom_R) / rho_R))))) * (mom_R / rho_R)) - ((energy_L + ((gas_gamma - 1.0) * (energy_L - (0.5 * ((mom_L *
    mom_L) / rho_L))))) * (mom_L / rho_L))) / fmax(fmax(fabs(((mom_L / rho_L) - sqrt(((gas_gamma * ((gas_gamma - 1.0) *
    (energy_L - (0.5 * ((mom_L * mom_L) / rho_L))))) / rho_L)))), fabs(((mom_L / rho_L) + sqrt(((gas_gamma * ((gas_gamma
    - 1.0) * (energy_L - (0.5 * ((mom_L * mom_L) / rho_L))))) / rho_L))))), fmax(fabs(((mom_R / rho_R) -
    sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_R - (0.5 * ((mom_R * mom_R) / rho_R))))) / rho_R)))), fabs(((mom_R /
    rho_R) + sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_R - (0.5 * ((mom_R * mom_R) / rho_R))))) / rho_R)))))))));

  wave_family->wave2.wave_rho = (0.5 * ((rho_R - rho_L) + ((mom_R - mom_L) / fmax(fmax(fabs(((mom_L / rho_L) -
    sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_L - (0.5 * ((mom_L * mom_L) / rho_L))))) / rho_L)))), fabs(((mom_L /
    rho_L) + sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_L - (0.5 * ((mom_L * mom_L) / rho_L))))) / rho_L))))),
    fmax(fabs(((mom_R / rho_R) - sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_R - (0.5 * ((mom_R * mom_R) /
    rho_R))))) / rho_R)))), fabs(((mom_R / rho_R) + sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_R - (0.5 * ((mom_R *
    mom_R) / rho_R))))) / rho_R)))))))));
  wave_family->wave2.wave_mom = (0.5 * ((mom_R - mom_L) + (((((mom_R * mom_R) / rho_R) + ((gas_gamma - 1.0) * (energy_R
    - (0.5 * ((mom_R * mom_R) / rho_R))))) - (((mom_L * mom_L) / rho_L) + ((gas_gamma - 1.0) * (energy_L - (0.5 *
    ((mom_L * mom_L) / rho_L)))))) / fmax(fmax(fabs(((mom_L / rho_L) - sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_L
    - (0.5 * ((mom_L * mom_L) / rho_L))))) / rho_L)))), fabs(((mom_L / rho_L) + sqrt(((gas_gamma * ((gas_gamma - 1.0) *
    (energy_L - (0.5 * ((mom_L * mom_L) / rho_L))))) / rho_L))))), fmax(fabs(((mom_R / rho_R) - sqrt(((gas_gamma *
    ((gas_gamma - 1.0) * (energy_R - (0.5 * ((mom_R * mom_R) / rho_R))))) / rho_R)))), fabs(((mom_R / rho_R) +
    sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_R - (0.5 * ((mom_R * mom_R) / rho_R))))) / rho_R)))))))));
  wave_family->wave2.wave_energy = (0.5 * ((energy_R - energy_L) + ((((energy_R + ((gas_gamma - 1.0) * (energy_R - (0.5
    * ((mom_R * mom_R) / rho_R))))) * (mom_R / rho_R)) - ((energy_L + ((gas_gamma - 1.0) * (energy_L - (0.5 * ((mom_L *
    mom_L) / rho_L))))) * (mom_L / rho_L))) / fmax(fmax(fabs(((mom_L / rho_L) - sqrt(((gas_gamma * ((gas_gamma - 1.0) *
    (energy_L - (0.5 * ((mom_L * mom_L) / rho_L))))) / rho_L)))), fabs(((mom_L / rho_L) + sqrt(((gas_gamma * ((gas_gamma
    - 1.0) * (energy_L - (0.5 * ((mom_L * mom_L) / rho_L))))) / rho_L))))), fmax(fabs(((mom_R / rho_R) -
    sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_R - (0.5 * ((mom_R * mom_R) / rho_R))))) / rho_R)))), fabs(((mom_R /
    rho_R) + sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_R - (0.5 * ((mom_R * mom_R) / rho_R))))) / rho_R)))))))));
}

static inline compressible_euler_1d_lax_friedrichs_waves_1D
create_waves()
{
  compressible_euler_1d_lax_friedrichs_waves_1D waves;

  waves.x_wave_family = compressible_euler_1d_lax_friedrichs_x_wave_family;
  
  return waves;
}

static inline bool
compressible_euler_1d_lax_friedrichs_x_waves_consistent(const compressible_euler_1d_coordinates *C, const compressible_euler_1d_state *U,
  const compressible_euler_1d_parameters *P)
{
  compressible_euler_1d_lax_friedrichs_wave_family wave_family;
  compressible_euler_1d_lax_friedrichs_x_wave_family(C, C, U, U, P, &wave_family);

  double rho_wave1 = wave_family.wave1.wave_rho;
  double rho_wave2 = wave_family.wave2.wave_rho;
  double mom_wave1 = wave_family.wave1.wave_mom;
  double mom_wave2 = wave_family.wave2.wave_mom;
  double energy_wave1 = wave_family.wave1.wave_energy;
  double energy_wave2 = wave_family.wave2.wave_energy;

  return ((fabs(rho_wave1) < 1.0e-8) && (fabs(rho_wave2) < 1.0e-8) &&
    (fabs(mom_wave1) < 1.0e-8) && (fabs(mom_wave2) < 1.0e-8) &&
    (fabs(energy_wave1) < 1.0e-8) && (fabs(energy_wave2) < 1.0e-8));
}

static inline bool
compressible_euler_1d_lax_friedrichs_x_waves_valid(const compressible_euler_1d_coordinates *C_L, const compressible_euler_1d_coordinates *C_R,
  const compressible_euler_1d_state *U_L, const compressible_euler_1d_state *U_R, const compressible_euler_1d_parameters *P)
{
  double rho_L = U_L->rho;
  double rho_R = U_R->rho;
  double mom_L = U_L->mom;
  double mom_R = U_R->mom;
  double energy_L = U_L->energy;
  double energy_R = U_R->energy;

  double rho_jump = rho_R - rho_L;
  double mom_jump = mom_R - mom_L;
  double energy_jump = energy_R - energy_L;

  compressible_euler_1d_lax_friedrichs_wave_family wave_family;
  compressible_euler_1d_lax_friedrichs_x_wave_family(C_L, C_R, U_L, U_R, P, &wave_family);

  double rho_wave_sum = wave_family.wave1.wave_rho + wave_family.wave2.wave_rho;
  double mom_wave_sum = wave_family.wave1.wave_mom + wave_family.wave2.wave_mom;
  double energy_wave_sum = wave_family.wave1.wave_energy + wave_family.wave2.wave_energy;

  return (fabs(rho_jump - rho_wave_sum) < 1.0e-8) && (fabs(mom_jump - mom_wave_sum) < 1.0e-8) && (fabs(energy_jump -
    energy_wave_sum) < 1.0e-8);
}

typedef struct {
  double speed1;
  double speed2;
} compressible_euler_1d_lax_friedrichs_speed_family;

typedef struct {
  void (*x_speed_family)(const compressible_euler_1d_coordinates *C_L, const compressible_euler_1d_coordinates *C_R,
    const compressible_euler_1d_state *U_L, const compressible_euler_1d_state *U_R,
    const compressible_euler_1d_parameters *P, compressible_euler_1d_lax_friedrichs_speed_family *speed_family);
} compressible_euler_1d_lax_friedrichs_speeds_1D;

static inline void
compressible_euler_1d_lax_friedrichs_x_speed_family(const compressible_euler_1d_coordinates *C_L, const compressible_euler_1d_coordinates *C_R,
  const compressible_euler_1d_state *U_L, const compressible_euler_1d_state *U_R,
  const compressible_euler_1d_parameters *P, compressible_euler_1d_lax_friedrichs_speed_family *speed_family)
{
  double x_L = C_L->x;
  double x_R = C_R->x;
  double rho_L = U_L->rho;
  double rho_R = U_R->rho;
  double mom_L = U_L->mom;
  double mom_R = U_R->mom;
  double energy_L = U_L->energy;
  double energy_R = U_R->energy;
  double gas_gamma = P->gas_gamma;

  speed_family->speed1 = -(fmax(fmax(fabs(((mom_L / rho_L) - sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_L - (0.5 *
    ((mom_L * mom_L) / rho_L))))) / rho_L)))), fabs(((mom_L / rho_L) + sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_L
    - (0.5 * ((mom_L * mom_L) / rho_L))))) / rho_L))))), fmax(fabs(((mom_R / rho_R) - sqrt(((gas_gamma * ((gas_gamma -
    1.0) * (energy_R - (0.5 * ((mom_R * mom_R) / rho_R))))) / rho_R)))), fabs(((mom_R / rho_R) + sqrt(((gas_gamma *
    ((gas_gamma - 1.0) * (energy_R - (0.5 * ((mom_R * mom_R) / rho_R))))) / rho_R)))))));
  speed_family->speed2 = fmax(fmax(fabs(((mom_L / rho_L) - sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_L - (0.5 *
    ((mom_L * mom_L) / rho_L))))) / rho_L)))), fabs(((mom_L / rho_L) + sqrt(((gas_gamma * ((gas_gamma - 1.0) * (energy_L
    - (0.5 * ((mom_L * mom_L) / rho_L))))) / rho_L))))), fmax(fabs(((mom_R / rho_R) - sqrt(((gas_gamma * ((gas_gamma -
    1.0) * (energy_R - (0.5 * ((mom_R * mom_R) / rho_R))))) / rho_R)))), fabs(((mom_R / rho_R) + sqrt(((gas_gamma *
    ((gas_gamma - 1.0) * (energy_R - (0.5 * ((mom_R * mom_R) / rho_R))))) / rho_R))))));
}

static inline compressible_euler_1d_lax_friedrichs_speeds_1D
create_speeds()
{
  compressible_euler_1d_lax_friedrichs_speeds_1D speeds;

  speeds.x_speed_family = compressible_euler_1d_lax_friedrichs_x_speed_family;

  return speeds;
}

typedef struct {
  double fluctuation_rho;
  double fluctuation_mom;
  double fluctuation_energy;
} compressible_euler_1d_lax_friedrichs_fluctuation;

typedef struct {
  void (*x_fluctuation)(const compressible_euler_1d_coordinates *C_L, const compressible_euler_1d_coordinates *C_R,
    const compressible_euler_1d_state *U_L, const compressible_euler_1d_state *U_R,
    const compressible_euler_1d_parameters *P, compressible_euler_1d_lax_friedrichs_fluctuation *fluctuation);
} compressible_euler_1d_lax_friedrichs_fluctuations_1D;

static inline void
compressible_euler_1d_lax_friedrichs_x_left_fluctuation(const compressible_euler_1d_coordinates *C_L, const compressible_euler_1d_coordinates *C_R,
  const compressible_euler_1d_state *U_L, const compressible_euler_1d_state *U_R,
  const compressible_euler_1d_parameters *P, compressible_euler_1d_lax_friedrichs_fluctuation *left_fluctuation)
{
  compressible_euler_1d_lax_friedrichs_wave_family wave_family;
  compressible_euler_1d_lax_friedrichs_x_wave_family(C_L, C_R, U_L, U_R, P, &wave_family);

  compressible_euler_1d_lax_friedrichs_speed_family speed_family;
  compressible_euler_1d_lax_friedrichs_x_speed_family(C_L, C_R, U_L, U_R, P, &speed_family);

  left_fluctuation->fluctuation_rho = 
    (wave_family.wave1.wave_rho * fmin(speed_family.speed1, 0.0)) + 
    (wave_family.wave2.wave_rho * fmin(speed_family.speed2, 0.0));

  left_fluctuation->fluctuation_mom = 
    (wave_family.wave1.wave_mom * fmin(speed_family.speed1, 0.0)) + 
    (wave_family.wave2.wave_mom * fmin(speed_family.speed2, 0.0));

  left_fluctuation->fluctuation_energy = 
    (wave_family.wave1.wave_energy * fmin(speed_family.speed1, 0.0)) + 
    (wave_family.wave2.wave_energy * fmin(speed_family.speed2, 0.0));
}

static inline void
compressible_euler_1d_lax_friedrichs_x_right_fluctuation(const compressible_euler_1d_coordinates *C_L, const compressible_euler_1d_coordinates *C_R,
  const compressible_euler_1d_state *U_L, const compressible_euler_1d_state *U_R,
  const compressible_euler_1d_parameters *P, compressible_euler_1d_lax_friedrichs_fluctuation *right_fluctuation)
{
  compressible_euler_1d_lax_friedrichs_wave_family wave_family;
  compressible_euler_1d_lax_friedrichs_x_wave_family(C_L, C_R, U_L, U_R, P, &wave_family);

  compressible_euler_1d_lax_friedrichs_speed_family speed_family;
  compressible_euler_1d_lax_friedrichs_x_speed_family(C_L, C_R, U_L, U_R, P, &speed_family);

  right_fluctuation->fluctuation_rho = 
    (wave_family.wave1.wave_rho * fmax(speed_family.speed1, 0.0)) + 
    (wave_family.wave2.wave_rho * fmax(speed_family.speed2, 0.0));

  right_fluctuation->fluctuation_mom = 
    (wave_family.wave1.wave_mom * fmax(speed_family.speed1, 0.0)) + 
    (wave_family.wave2.wave_mom * fmax(speed_family.speed2, 0.0));

  right_fluctuation->fluctuation_energy = 
    (wave_family.wave1.wave_energy * fmax(speed_family.speed1, 0.0)) + 
    (wave_family.wave2.wave_energy * fmax(speed_family.speed2, 0.0));
}

static inline compressible_euler_1d_lax_friedrichs_fluctuations_1D
create_left_fluctuations()
{
  compressible_euler_1d_lax_friedrichs_fluctuations_1D left_fluctuations;

  left_fluctuations.x_fluctuation = compressible_euler_1d_lax_friedrichs_x_left_fluctuation;

  return left_fluctuations;
}

static inline compressible_euler_1d_lax_friedrichs_fluctuations_1D
create_right_fluctuations()
{
  compressible_euler_1d_lax_friedrichs_fluctuations_1D right_fluctuations;

  right_fluctuations.x_fluctuation = compressible_euler_1d_lax_friedrichs_x_right_fluctuation;

  return right_fluctuations;
}

static inline bool
compressible_euler_1d_lax_friedrichs_x_left_fluctuations_consistent(const compressible_euler_1d_coordinates *C, const compressible_euler_1d_state *U,
  const compressible_euler_1d_parameters *P)
{
  compressible_euler_1d_lax_friedrichs_fluctuation left_fluctuation;
  compressible_euler_1d_lax_friedrichs_x_left_fluctuation(C, C, U, U, P, &left_fluctuation);

  double rho_left_fluctuation = left_fluctuation.fluctuation_rho;
  double mom_left_fluctuation = left_fluctuation.fluctuation_mom;
  double energy_left_fluctuation = left_fluctuation.fluctuation_energy;

  return ((fabs(rho_left_fluctuation) < 1.0e-8) && (fabs(mom_left_fluctuation) < 1.0e-8) &&
    (fabs(energy_left_fluctuation) < 1.0e-8));
}

static inline bool
compressible_euler_1d_lax_friedrichs_x_right_fluctuations_consistent(const compressible_euler_1d_coordinates *C, const compressible_euler_1d_state *U,
  const compressible_euler_1d_parameters *P)
{
  compressible_euler_1d_lax_friedrichs_fluctuation right_fluctuation;
  compressible_euler_1d_lax_friedrichs_x_right_fluctuation(C, C, U, U, P, &right_fluctuation);

  double rho_right_fluctuation = right_fluctuation.fluctuation_rho;
  double mom_right_fluctuation = right_fluctuation.fluctuation_mom;
  double energy_right_fluctuation = right_fluctuation.fluctuation_energy;

  return ((fabs(rho_right_fluctuation) < 1.0e-8) && (fabs(mom_right_fluctuation) < 1.0e-8) &&
    (fabs(energy_right_fluctuation) < 1.0e-8));
}

static inline bool
compressible_euler_1d_lax_friedrichs_x_fluctuations_valid(const compressible_euler_1d_coordinates *C_L, const compressible_euler_1d_coordinates *C_R,
  const compressible_euler_1d_state *U_L, const compressible_euler_1d_state *U_R, const compressible_euler_1d_parameters *P)
{
  compressible_euler_1d_flux left_flux;
  compressible_euler_1d_x_flux(C_L, P, U_L, &left_flux);

  compressible_euler_1d_flux right_flux;
  compressible_euler_1d_x_flux(C_R, P, U_R, &right_flux);

  double rho_flux_jump = right_flux.flux_rho - left_flux.flux_rho;
  double mom_flux_jump = right_flux.flux_mom - left_flux.flux_mom;
  double energy_flux_jump = right_flux.flux_energy - left_flux.flux_energy;

  compressible_euler_1d_lax_friedrichs_fluctuation left_fluctuation;
  compressible_euler_1d_lax_friedrichs_x_left_fluctuation(C_L, C_R, U_L, U_R, P, &left_fluctuation);

  compressible_euler_1d_lax_friedrichs_fluctuation right_fluctuation;
  compressible_euler_1d_lax_friedrichs_x_right_fluctuation(C_L, C_R, U_L, U_R, P, &right_fluctuation);

  double rho_fluctuation_sum = left_fluctuation.fluctuation_rho + right_fluctuation.fluctuation_rho;
  double mom_fluctuation_sum = left_fluctuation.fluctuation_mom + right_fluctuation.fluctuation_mom;
  double energy_fluctuation_sum = left_fluctuation.fluctuation_energy + right_fluctuation.fluctuation_energy;

  return (fabs(rho_flux_jump - rho_fluctuation_sum) < 1.0e-8) && (fabs(mom_flux_jump - mom_fluctuation_sum) < 1.0e-8) &&
    (fabs(energy_flux_jump - energy_fluctuation_sum) < 1.0e-8);
}

typedef struct {
  double reconstruction_rho;
  double reconstruction_mom;
  double reconstruction_energy;
} compressible_euler_1d_minmod_reconstruction;

typedef struct {
  void (*x_reconstruction)(const compressible_euler_1d_coordinates *C_L, const compressible_euler_1d_coordinates *C, const compressible_euler_1d_coordinates *C_R,
    const compressible_euler_1d_state *U_L, const compressible_euler_1d_state *U, const compressible_euler_1d_state *U_R,
    const compressible_euler_1d_parameters *P, compressible_euler_1d_minmod_reconstruction *reconstruction);
} compressible_euler_1d_minmod_reconstruction_1D;

static inline void
compressible_euler_1d_minmod_x_left_reconstruction(const compressible_euler_1d_coordinates *C_L, const compressible_euler_1d_coordinates *C,
  const compressible_euler_1d_coordinates *C_R, const compressible_euler_1d_state *U_L, const compressible_euler_1d_state *U, const compressible_euler_1d_state *U_R,
  const compressible_euler_1d_parameters *P, compressible_euler_1d_minmod_reconstruction *left_reconstruction)
{
  double x_L = C_L->x;
  double x = C->x; 
  double x_R = C_R->x;
  double rho_L = U_L->rho;
  double rho = U->rho;
  double rho_R = U_R->rho;
  double mom_L = U_L->mom;
  double mom = U->mom;
  double mom_R = U_R->mom;
  double energy_L = U_L->energy;
  double energy = U->energy;
  double energy_R = U_R->energy;
  double gas_gamma = P->gas_gamma;

  left_reconstruction->reconstruction_rho = (rho - (0.5 * (fmax(0.0, fmin((rho - rho_L), (rho_R - rho))) + fmin(0.0,
    fmax((rho - rho_L), (rho_R - rho))))));
  left_reconstruction->reconstruction_mom = (mom - (0.5 * (fmax(0.0, fmin((mom - mom_L), (mom_R - mom))) + fmin(0.0,
    fmax((mom - mom_L), (mom_R - mom))))));
  left_reconstruction->reconstruction_energy = (energy - (0.5 * (fmax(0.0, fmin((energy - energy_L), (energy_R -
    energy))) + fmin(0.0, fmax((energy - energy_L), (energy_R - energy))))));
}

static inline void
compressible_euler_1d_minmod_x_right_reconstruction(const compressible_euler_1d_coordinates *C_L, const compressible_euler_1d_coordinates *C,
  const compressible_euler_1d_coordinates *C_R, const compressible_euler_1d_state *U_L, const compressible_euler_1d_state *U, const compressible_euler_1d_state *U_R,
  const compressible_euler_1d_parameters *P, compressible_euler_1d_minmod_reconstruction *right_reconstruction)
{
  double x_L = C_L->x;
  double x = C->x; 
  double x_R = C_R->x;
  double rho_L = U_L->rho;
  double rho = U->rho;
  double rho_R = U_R->rho;
  double mom_L = U_L->mom;
  double mom = U->mom;
  double mom_R = U_R->mom;
  double energy_L = U_L->energy;
  double energy = U->energy;
  double energy_R = U_R->energy;
  double gas_gamma = P->gas_gamma;

  right_reconstruction->reconstruction_rho = (rho + (0.5 * (fmax(0.0, fmin((rho - rho_L), (rho_R - rho))) + fmin(0.0,
    fmax((rho - rho_L), (rho_R - rho))))));
  right_reconstruction->reconstruction_mom = (mom + (0.5 * (fmax(0.0, fmin((mom - mom_L), (mom_R - mom))) + fmin(0.0,
    fmax((mom - mom_L), (mom_R - mom))))));
  right_reconstruction->reconstruction_energy = (energy + (0.5 * (fmax(0.0, fmin((energy - energy_L), (energy_R -
    energy))) + fmin(0.0, fmax((energy - energy_L), (energy_R - energy))))));
}

static inline compressible_euler_1d_minmod_reconstruction_1D
create_left_reconstruction()
{
  compressible_euler_1d_minmod_reconstruction_1D left_reconstruction;

  left_reconstruction.x_reconstruction = compressible_euler_1d_minmod_x_left_reconstruction;

  return left_reconstruction;
}

static inline compressible_euler_1d_minmod_reconstruction_1D
create_right_reconstruction()
{
  compressible_euler_1d_minmod_reconstruction_1D right_reconstruction;

  right_reconstruction.x_reconstruction = compressible_euler_1d_minmod_x_right_reconstruction;

  return right_reconstruction;
}

static inline bool
compressible_euler_1d_minmod_x_left_reconstruction_consistent(const compressible_euler_1d_coordinates *C, const compressible_euler_1d_state *U,
const compressible_euler_1d_parameters *P)
{
  compressible_euler_1d_minmod_reconstruction left_reconstruction;
  compressible_euler_1d_minmod_x_left_reconstruction(C, C, C, U, U, U, P, &left_reconstruction);

  double rho_left_reconstruction = left_reconstruction.reconstruction_rho;
  double rho = U->rho;
  double mom_left_reconstruction = left_reconstruction.reconstruction_mom;
  double mom = U->mom;
  double energy_left_reconstruction = left_reconstruction.reconstruction_energy;
  double energy = U->energy;

  return ((fabs(rho_left_reconstruction - rho) < 1.0e-8) && (fabs(mom_left_reconstruction - mom) < 1.0e-8) &&
    (fabs(energy_left_reconstruction - energy) < 1.0e-8));
}

static inline bool
compressible_euler_1d_minmod_x_right_reconstruction_consistent(const compressible_euler_1d_coordinates *C, const compressible_euler_1d_state *U,
const compressible_euler_1d_parameters *P)
{
  compressible_euler_1d_minmod_reconstruction right_reconstruction;
  compressible_euler_1d_minmod_x_right_reconstruction(C, C, C, U, U, U, P, &right_reconstruction);

  double rho_right_reconstruction = right_reconstruction.reconstruction_rho;
  double rho = U->rho;
  double mom_right_reconstruction = right_reconstruction.reconstruction_mom;
  double mom = U->mom;
  double energy_right_reconstruction = right_reconstruction.reconstruction_energy;
  double energy = U->energy;

  return ((fabs(rho_right_reconstruction - rho) < 1.0e-8) && (fabs(mom_right_reconstruction - mom) < 1.0e-8) &&
    (fabs(energy_right_reconstruction - energy) < 1.0e-8));
}

int
main(int argc, char *argv[])
{
  // Insert simulation drivers here.
  
  return 0;
}
                