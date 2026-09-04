#include <fenv.h>
#include <float.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef struct {
  uint64_t status;
  uint64_t mass;
  uint64_t momentum;
  uint64_t energy;
} checked_flux_bits;

static int
supported_binary64_environment(void)
{
  const double one = 1.0;
  uint64_t one_bits;
#if !defined(__STDC_IEC_559__)
  fprintf(stderr, "fixed-alpha-mirror: C implementation does not advertise IEC 60559 arithmetic\n");
  return 0;
#endif
  if (CHAR_BIT != 8 || sizeof(uint64_t) != 8 || sizeof(double) != 8 ||
      FLT_RADIX != 2 || DBL_MANT_DIG != 53 || DBL_MAX_EXP != 1024 ||
      DBL_MIN_EXP != -1021 || FLT_EVAL_METHOD != 0) {
    fprintf(stderr, "fixed-alpha-mirror: unsupported binary64 platform\n");
    return 0;
  }
  memcpy(&one_bits, &one, sizeof(one_bits));
  if (one_bits != UINT64_C(0x3ff0000000000000)) {
    fprintf(stderr, "fixed-alpha-mirror: unsupported binary64 word layout\n");
    return 0;
  }
  if (fesetround(FE_TONEAREST) != 0 || fegetround() != FE_TONEAREST) {
    fprintf(stderr, "fixed-alpha-mirror: round-to-nearest mode is unavailable\n");
    return 0;
  }
  return 1;
}

static int
parse_lower_hex_word(const char *text, uint64_t *word)
{
  uint64_t value = 0;
  size_t index;

  if (strlen(text) != 16) {
    return 0;
  }
  for (index = 0; index < 16; ++index) {
    unsigned digit;
    const unsigned char ch = (unsigned char)text[index];
    if (ch >= (unsigned char)'0' && ch <= (unsigned char)'9') {
      digit = (unsigned)(ch - (unsigned char)'0');
    } else if (ch >= (unsigned char)'a' && ch <= (unsigned char)'f') {
      digit = 10U + (unsigned)(ch - (unsigned char)'a');
    } else {
      return 0;
    }
    value = (value << 4) | (uint64_t)digit;
  }
  *word = value;
  return 1;
}

static double
double_from_bits(uint64_t bits)
{
  double value;
  memcpy(&value, &bits, sizeof(value));
  return value;
}

static uint64_t
bits_from_double(double value)
{
  uint64_t bits;
  memcpy(&bits, &value, sizeof(bits));
  return bits;
}

static double
binary64_add(double left, double right)
{
  volatile double result = left + right;
  return result;
}

static double
binary64_mul(double left, double right)
{
  volatile double result = left * right;
  return result;
}

static int
raw_guard(uint64_t rho_l, uint64_t u_l, uint64_t p_l,
          uint64_t rho_r, uint64_t u_r, uint64_t p_r)
{
  const uint64_t eighth = UINT64_C(0x3fc0000000000000);
  const uint64_t one = UINT64_C(0x3ff0000000000000);
  const uint64_t sixteenth = UINT64_C(0x3fb0000000000000);
  const uint64_t half = UINT64_C(0x3fe0000000000000);
  const uint64_t magnitude_mask = UINT64_C(0x7fffffffffffffff);

  return eighth <= rho_l && rho_l <= one &&
         sixteenth <= p_l && p_l <= rho_l &&
         (u_l & magnitude_mask) <= half &&
         eighth <= rho_r && rho_r <= one &&
         sixteenth <= p_r && p_r <= rho_r &&
         (u_r & magnitude_mask) <= half;
}

static checked_flux_bits
fixed_alpha_flux(uint64_t rho_l_bits, uint64_t u_l_bits, uint64_t p_l_bits,
                 uint64_t rho_r_bits, uint64_t u_r_bits, uint64_t p_r_bits)
{
  checked_flux_bits result = { UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0) };
  const uint64_t sign_mask = UINT64_C(0x8000000000000000);
  const double half = double_from_bits(UINT64_C(0x3fe0000000000000));
  const double quarter = double_from_bits(UINT64_C(0x3fd0000000000000));
  const double eighth = double_from_bits(UINT64_C(0x3fc0000000000000));
  double rho_l;
  double u_l;
  double p_l;
  double rho_r;
  double u_r;
  double p_r;
  double mass_l;
  double velocity_squared_mass_l;
  double half_kinetic_l;
  double half_pressure_l;
  double two_pressure_l;
  double energy_pressure_l;
  double energy_l;
  double enthalpy_pressure_l;
  double enthalpy_l;
  double momentum_flux_l;
  double energy_flux_l;
  double mass_r;
  double velocity_squared_mass_r;
  double half_kinetic_r;
  double half_pressure_r;
  double two_pressure_r;
  double energy_pressure_r;
  double energy_r;
  double enthalpy_pressure_r;
  double enthalpy_r;
  double momentum_flux_r;
  double energy_flux_r;
  double mass_jump;
  double mass_mean;
  double mass_dissipation;
  double mass_flux;
  double momentum_jump;
  double momentum_mean;
  double momentum_dissipation;
  double momentum_flux;
  double energy_jump;
  double energy_mean;
  double energy_dissipation;
  double energy_flux;

  if (!raw_guard(rho_l_bits, u_l_bits, p_l_bits,
                 rho_r_bits, u_r_bits, p_r_bits)) {
    return result;
  }

  rho_l = double_from_bits(rho_l_bits);
  u_l = double_from_bits(u_l_bits);
  p_l = double_from_bits(p_l_bits);
  rho_r = double_from_bits(rho_r_bits);
  u_r = double_from_bits(u_r_bits);
  p_r = double_from_bits(p_r_bits);

  mass_l = binary64_mul(rho_l, u_l);
  velocity_squared_mass_l = binary64_mul(mass_l, u_l);
  half_kinetic_l = binary64_mul(half, velocity_squared_mass_l);
  half_pressure_l = binary64_mul(half, p_l);
  two_pressure_l = binary64_add(p_l, p_l);
  energy_pressure_l = binary64_add(two_pressure_l, half_pressure_l);
  energy_l = binary64_add(energy_pressure_l, half_kinetic_l);
  enthalpy_pressure_l = binary64_add(energy_pressure_l, p_l);
  enthalpy_l = binary64_add(enthalpy_pressure_l, half_kinetic_l);
  momentum_flux_l = binary64_add(velocity_squared_mass_l, p_l);
  energy_flux_l = binary64_mul(enthalpy_l, u_l);

  mass_r = binary64_mul(rho_r, u_r);
  velocity_squared_mass_r = binary64_mul(mass_r, u_r);
  half_kinetic_r = binary64_mul(half, velocity_squared_mass_r);
  half_pressure_r = binary64_mul(half, p_r);
  two_pressure_r = binary64_add(p_r, p_r);
  energy_pressure_r = binary64_add(two_pressure_r, half_pressure_r);
  energy_r = binary64_add(energy_pressure_r, half_kinetic_r);
  enthalpy_pressure_r = binary64_add(energy_pressure_r, p_r);
  enthalpy_r = binary64_add(enthalpy_pressure_r, half_kinetic_r);
  momentum_flux_r = binary64_add(velocity_squared_mass_r, p_r);
  energy_flux_r = binary64_mul(enthalpy_r, u_r);

  mass_jump = binary64_add(rho_l, double_from_bits(rho_r_bits ^ sign_mask));
  mass_mean = binary64_mul(half, binary64_add(mass_l, mass_r));
  mass_dissipation = binary64_add(
      binary64_add(binary64_mul(half, mass_jump),
                   binary64_mul(quarter, mass_jump)),
      binary64_mul(eighth, mass_jump));
  mass_flux = binary64_add(mass_mean, mass_dissipation);

  momentum_jump = binary64_add(mass_l, double_from_bits(bits_from_double(mass_r) ^ sign_mask));
  momentum_mean = binary64_mul(half, binary64_add(momentum_flux_l, momentum_flux_r));
  momentum_dissipation = binary64_add(
      binary64_add(binary64_mul(half, momentum_jump),
                   binary64_mul(quarter, momentum_jump)),
      binary64_mul(eighth, momentum_jump));
  momentum_flux = binary64_add(momentum_mean, momentum_dissipation);

  energy_jump = binary64_add(energy_l, double_from_bits(bits_from_double(energy_r) ^ sign_mask));
  energy_mean = binary64_mul(half, binary64_add(energy_flux_l, energy_flux_r));
  energy_dissipation = binary64_add(
      binary64_add(binary64_mul(half, energy_jump),
                   binary64_mul(quarter, energy_jump)),
      binary64_mul(eighth, energy_jump));
  energy_flux = binary64_add(energy_mean, energy_dissipation);

  result.status = UINT64_C(0);
  result.mass = bits_from_double(mass_flux);
  result.momentum = bits_from_double(momentum_flux);
  result.energy = bits_from_double(energy_flux);
  return result;
}

int
main(int argc, char **argv)
{
  uint64_t words[6];
  checked_flux_bits result;
  int index;

  if (argc != 7) {
    fprintf(stderr,
        "usage: %s rho_l_bits u_l_bits p_l_bits rho_r_bits u_r_bits p_r_bits\n",
        argv[0]);
    return 2;
  }
  if (!supported_binary64_environment()) {
    return 2;
  }
  for (index = 0; index < 6; ++index) {
    if (!parse_lower_hex_word(argv[index + 1], &words[index])) {
      fprintf(stderr, "fixed-alpha-mirror: argument %d is not a lowercase 16-hex word\n", index + 1);
      return 2;
    }
  }

  result = fixed_alpha_flux(words[0], words[1], words[2],
                            words[3], words[4], words[5]);
  printf("%" PRIu64 ",%016" PRIx64 ",%016" PRIx64 ",%016" PRIx64 "\n",
         result.status, result.mass, result.momentum, result.energy);
  return 0;
}
